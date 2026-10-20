/-
Simulation library, part 3: chaining the event simulations (promoted from the
simulation prototype). One instruction's event tree (`runTree_sim`), one thread step
(`finishInstr_sim`, `stepOne_sim`) and promise-free solo runs
(`threadSF_sim`), under the source-run side condition `StaleFree`.
-/
import Kraken.Promising.SLR.Sim.Event

namespace Kraken.Promising

namespace Sim

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## One instruction's event tree

`runTree_sim` chains the event lemmas through an event tree. It carries the
invariant `SimInv`: the relation, the source context bounded (`Ctx.Bnd`), every
promise and every source timestamp in the domain (a *total* map on the source
memory), and foreign target messages placed as `FgnSep` says; the source tree
satisfies `StaleFree`. With no foreign messages (`runTree_sim_noForeign`) there
is no side condition: the environment instance (`ρ = id`, the same memory) and
every instance whose target memory is the image of the source's. The
`PromisePure` instance needs a partial map (its own promise outside the
domain) and the break event (`writeSuccs_break`). -/

section Tree

variable (A : Arch) (tid : Nat)

/-- The source-side side condition of the instances with foreign messages
(B2, O11), as a property of the source run (like `EvTree.RelFulfils`, but for
every run): a read of an `L`-location (a location foreign messages write) from
a timestamp at most `n` has its bound at most `n`, and an exclusive or RMW
write to an `L`-location is paired with a read above `n`. In words: once the
thread has seen past the base memory, it never reads a base message of a
location the other threads wrote, and never claims atomicity over one. -/
def StaleFree (A : Arch) (tid : Nat) (iv : InstrViews) (n : Nat) (L : Loc → Prop) {σ : Type} :
    Ctx → EvTree σ → Prop
  | _, .done _ => True
  | _, .fault _ => True
  | c, .choose _ k => ∀ i, StaleFree A tid iv n L c (k i)
  | c, .load k xcl l ret =>
    ∀ x ∈ readSuccs A iv c k xcl l, (L l → x.1 ≤ n → max (readPre A iv c k) (c.views.getCoh l) ≤ n) ∧
      StaleFree A tid iv n L x.2.2 (ret x.2.1)
  | c, .store k xcl l v ret =>
    (xcl = true → L l → ∀ a, c.views.xclb.map (·.1) = some a → n < a) ∧
    (∀ c' ∈ writeSuccs A tid (iv.forStore c.stores) c k xcl l v
        (if xcl then c.views.xclb.map (·.1) else none) 0 (if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0), StaleFree A tid iv n L c' (ret true)) ∧
    StaleFree A tid iv n L
      { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } (ret false)
  | c, .fence k ret => StaleFree A tid iv n L (fenceStep c k) (ret ())
  | c, .rmw k noRet l op ret =>
    ∀ x ∈ readSuccs A iv (if A.rmwFence then fenceStep c .sy else c)
        (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      (L l → x.1 ≤ n →
        max (readPre A iv (if A.rmwFence then fenceStep c .sy else c) (if noRet then .plain else (A.rmwKind k).loadKind))
          ((if A.rmwFence then fenceStep c .sy else c).views.getCoh l) ≤ n ∧ op x.2.1 = none) ∧
      StaleFree A tid iv n L (if A.rmwFence then fenceStep x.2.2 .sy else x.2.2) (ret x.2.1) ∧
      ∀ new, op x.2.1 = some new →
        ∀ c' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
          StaleFree A tid iv n L
            (if A.rmwFence then fenceStep (rmwPost A k noRet l c') .sy else rmwPost A k noRet l c') (ret x.2.1)

/-- With no watched location the side condition is trivial. -/
theorem staleFree_bot {σ : Type} (iv : InstrViews) (n : Nat) (tree : EvTree σ) :
    ∀ c, StaleFree A tid iv n (fun _ => False) c tree := by
  induction tree with
  | done _ => intro _; trivial
  | fault _ => intro _; trivial
  | choose _ _ ih => intro c i; exact ih i c
  | load _ _ _ _ ih => intro c x _; exact ⟨fun h => h.elim, ih _ _⟩
  | store _ _ _ _ _ ih => intro c; exact ⟨fun _ h => h.elim, fun _ _ => ih _ _, ih _ _⟩
  | fence _ _ ih => intro c; exact ih _ _
  | rmw _ _ _ _ _ ih => intro c x _; exact ⟨fun h => h.elim, ih _ _, fun _ _ _ _ => ih _ _⟩

/-- The invariant of `runTree_sim`: the relation; the source context bounded
(`Ctx.Bnd`); a total map on the source memory (every source timestamp and
promise in the domain); related instruction views; and the foreign target
messages separated at `n` (`FgnSep`). -/
structure SimInv (ρ : TMap) (n : Nat) (L : Loc → Prop) (iv iv' : InstrViews) (c c' : Ctx) : Prop where
  rel : CtxRel ρ c c'
  bnd : c.Bnd
  promDom : ∀ s ∈ c.prom, ρ.dom s
  domAll : ∀ s ≤ c.mem.last, ρ.dom s
  ivr : IVLe ρ iv' iv
  ivb : iv.Le c.mem.last
  nle : n ≤ c.mem.last
  fgn : FgnSep ρ c'.mem n L

variable {n : Nat} {L : Loc → Prop}

theorem SimInv.read {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInv ρ n L iv iv' c c')
    {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {t : Time} {v : Val} {c₁ : Ctx}
    (hx : (t, v, c₁) ∈ readSuccs A iv c k xcl l noRet)
    (hst : L l → t ≤ n → max (readPre A iv c k) (c.views.getCoh l) ≤ n) :
    ∃ c₁', (ρ.f t, v, c₁') ∈ readSuccs A iv' c' k xcl l noRet ∧ SimInv ρ n L iv iv' c₁ c₁' ∧
      c₁.mem = c.mem := by
  obtain ⟨hb1, ht, hm⟩ := readSuccs_bnd A iv hs.bnd hs.ivb hx
  obtain ⟨c₁', hx', hr⟩ := readSuccs_sim A hs.rel hs.ivr hx (hs.domAll t ht) (hs.fgn.gap (hs.domAll t ht) hst)
  have hm' : c₁'.mem = c'.mem := by
    obtain ⟨_, _, he, -⟩ := (mem_readSuccs A).mp hx'
    simp only [Prod.mk.injEq] at he
    rw [he.2.2]; rfl
  have hp : c₁.prom = c.prom := by
    obtain ⟨_, _, he, -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at he
    rw [he.2.2]; rfl
  exact ⟨c₁', hx', ⟨hr, hb1, hp ▸ hs.promDom, hm ▸ hs.domAll, hs.ivr, hm ▸ hs.ivb, hm ▸ hs.nle, hm' ▸ hs.fgn⟩, hm⟩

theorem SimInv.write {ρ : TMap} {iv iv' ivs ivs' : InstrViews} {c c' : Ctx} (hs : SimInv ρ n L iv iv' c c')
    (hivs : IVLe ρ ivs' ivs) (hivsb : ivs.Le c.mem.last) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : TrRel ρ tr tr') (hst : ∀ a, tr = some a → L l → n < a)
    {extra extra' : View} (hex : extra' ≤ ρ.fv extra)
    (hexb : extra ≤ c.mem.last) {xr xr' : View} (hxr : xr' ≤ ρ.fv xr) (hxrb : xr ≤ c.mem.last)
    {c₂ : Ctx} (h : c₂ ∈ writeSuccs A tid ivs c k xcl l v tr extra xr) :
    ∃ ρ' : TMap, ∃ c₂', c₂' ∈ writeSuccs A tid ivs' c' k xcl l v tr' extra' xr' ∧ SimInv ρ' n L iv iv' c₂ c₂' ∧
      Ext ρ ρ' c.mem.last ∧ c.mem.last ≤ c₂.mem.last := by
  have hgap : ∀ a, tr' = some a → AtomGap ρ c'.mem l tid a (c'.mem.last + 1) := by
    intro a ha
    cases tr with
    | none => cases tr' with
      | none => cases ha
      | some _ => exact htr.elim
    | some b =>
      cases tr' with
      | none => cases ha
      | some b' =>
        cases ha
        obtain ⟨hd, rfl⟩ := htr
        exact hs.fgn.atom tid hd (hst b rfl) _
  obtain ⟨ρ', c₂', h', hr, hag, hfv, hpd, -, hall, hfg⟩ :=
    writeSuccs_sim A tid hs.rel hs.bnd hs.promDom hivs hivsb htr hex hexb hxr hxrb hgap h
  obtain ⟨hb2, hm⟩ := writeSuccs_bnd A tid ivs hs.bnd hivsb hexb h
  exact ⟨ρ', c₂', h', ⟨hr, hb2, hpd, hall hs.domAll, hs.ivr.lift hs.ivb hfv, hs.ivb.mono hm,
    Nat.le_trans hs.nle hm, hfg n L hs.nle hs.fgn⟩, ⟨hag, hfv⟩, hm⟩

theorem SimInv.fence {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInv ρ n L iv iv' c c')
    (k : FenceKind) : SimInv ρ n L iv iv' (fenceStep c k) (fenceStep c' k) := by
  have hm := fenceStep_mem c k
  have hm' := fenceStep_mem c' k
  have hp : (fenceStep c k).prom = c.prom := by cases k <;> rfl
  exact ⟨fenceStep_sim hs.rel k, fenceStep_bnd hs.bnd k, hp ▸ hs.promDom, hm ▸ hs.domAll, hs.ivr,
    hm ▸ hs.ivb, hm ▸ hs.nle, hm' ▸ hs.fgn⟩

theorem SimInv.fenceOpt {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInv ρ n L iv iv' c c') (b : Bool)
    (k : FenceKind) :
    SimInv ρ n L iv iv' (if b then fenceStep c k else c) (if b then fenceStep c' k else c') := by
  cases b
  · exact hs
  · exact hs.fence k

theorem SimInv.post {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInv ρ n L iv iv' c c') (k : RmwKind)
    (noRet : Bool) (l : Loc) :
    SimInv ρ n L iv iv' (Kraken.Promising.rmwPost A k noRet l c) (Kraken.Promising.rmwPost A k noRet l c') := by
  have hv := hs.rel.views
  have hc := hs.rel
  have hb := (rmwPost_bnd A hs.bnd k noRet l).1
  revert hb
  unfold rmwPost
  by_cases hk : (A.rmwKind k == .acqRel && !noRet) = true
  · simp only [hk, ↓reduceIte]
    intro hb
    exact ⟨⟨hc.mem, ⟨hv.coh, le_fv_max hv.vrNew (hv.coh l), hv.vrOld, hv.vrOldNR, le_fv_max hv.vwNew (hv.coh l),
      hv.vwOld, hv.vwOldNT, hv.vCAP, hv.vRel, hv.fwd, hv.xclb⟩, hc.prom, hc.loadViews, hc.succView, rfl, hc.stores⟩,
      hb, hs.promDom, hs.domAll, hs.ivr, hs.ivb, hs.nle, hs.fgn⟩
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    intro hb
    exact ⟨⟨hc.mem, hv, hc.prom, hc.loadViews, hc.succView, rfl, hc.stores⟩, hb, hs.promDom, hs.domAll, hs.ivr,
      hs.ivb, hs.nle, hs.fgn⟩

/-! ### Several thresholds (interleaved foreign appends)

`SimInvAt ρ N L` is `SimInv` with the foreign messages separated at a *set*
of thresholds `N` (`FgnSepAt`), and the source tree `StaleFree` at every
threshold in `N`. `SimInv ρ n L` is the case `N = {n}` (`SimInv.toAt`,
`SimInvAt.toInv`), and `runTree_sim` is the corollary of `runTree_simAt`. -/

/-- The invariant of `runTree_simAt`: `SimInv` with a set of thresholds. -/
structure SimInvAt (ρ : TMap) (N : Nat → Prop) (L : Loc → Prop) (iv iv' : InstrViews) (c c' : Ctx) : Prop where
  rel : CtxRel ρ c c'
  bnd : c.Bnd
  promDom : ∀ s ∈ c.prom, ρ.dom s
  domAll : ∀ s ≤ c.mem.last, ρ.dom s
  ivr : IVLe ρ iv' iv
  ivb : iv.Le c.mem.last
  nle : ∀ n, N n → n ≤ c.mem.last
  fgn : FgnSepAt ρ c'.mem N L

theorem SimInv.toAt {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInv ρ n L iv iv' c c') :
    SimInvAt ρ (· = n) L iv iv' c c' :=
  ⟨hs.rel, hs.bnd, hs.promDom, hs.domAll, hs.ivr, hs.ivb, fun _ h => h ▸ hs.nle, hs.fgn.toAt⟩

theorem SimInvAt.toInv {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInvAt ρ (· = n) L iv iv' c c') :
    SimInv ρ n L iv iv' c c' :=
  ⟨hs.rel, hs.bnd, hs.promDom, hs.domAll, hs.ivr, hs.ivb, hs.nle n rfl, hs.fgn.toSep⟩

variable {N : Nat → Prop}

theorem SimInvAt.read {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInvAt ρ N L iv iv' c c')
    {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {t : Time} {v : Val} {c₁ : Ctx}
    (hx : (t, v, c₁) ∈ readSuccs A iv c k xcl l noRet)
    (hst : ∀ n, N n → L l → t ≤ n → max (readPre A iv c k) (c.views.getCoh l) ≤ n) :
    ∃ c₁', (ρ.f t, v, c₁') ∈ readSuccs A iv' c' k xcl l noRet ∧ SimInvAt ρ N L iv iv' c₁ c₁' ∧
      c₁.mem = c.mem := by
  obtain ⟨hb1, ht, hm⟩ := readSuccs_bnd A iv hs.bnd hs.ivb hx
  obtain ⟨c₁', hx', hr⟩ := readSuccs_sim A hs.rel hs.ivr hx (hs.domAll t ht) (hs.fgn.gap (hs.domAll t ht) hst)
  have hm' : c₁'.mem = c'.mem := by
    obtain ⟨_, _, he, -⟩ := (mem_readSuccs A).mp hx'
    simp only [Prod.mk.injEq] at he
    rw [he.2.2]; rfl
  have hp : c₁.prom = c.prom := by
    obtain ⟨_, _, he, -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at he
    rw [he.2.2]; rfl
  exact ⟨c₁', hx', ⟨hr, hb1, hp ▸ hs.promDom, hm ▸ hs.domAll, hs.ivr, hm ▸ hs.ivb, hm ▸ hs.nle, hm' ▸ hs.fgn⟩, hm⟩

theorem SimInvAt.write {ρ : TMap} {iv iv' ivs ivs' : InstrViews} {c c' : Ctx} (hs : SimInvAt ρ N L iv iv' c c')
    (hivs : IVLe ρ ivs' ivs) (hivsb : ivs.Le c.mem.last) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : TrRel ρ tr tr') (hst : ∀ a, tr = some a → ∀ n, N n → L l → n < a)
    {extra extra' : View} (hex : extra' ≤ ρ.fv extra)
    (hexb : extra ≤ c.mem.last) {xr xr' : View} (hxr : xr' ≤ ρ.fv xr) (hxrb : xr ≤ c.mem.last)
    {c₂ : Ctx} (h : c₂ ∈ writeSuccs A tid ivs c k xcl l v tr extra xr) :
    ∃ ρ' : TMap, ∃ c₂', c₂' ∈ writeSuccs A tid ivs' c' k xcl l v tr' extra' xr' ∧ SimInvAt ρ' N L iv iv' c₂ c₂' ∧
      Ext ρ ρ' c.mem.last ∧ c.mem.last ≤ c₂.mem.last := by
  have hgap : ∀ a, tr' = some a → AtomGap ρ c'.mem l tid a (c'.mem.last + 1) := by
    intro a ha
    cases tr with
    | none => cases tr' with
      | none => cases ha
      | some _ => exact htr.elim
    | some b =>
      cases tr' with
      | none => cases ha
      | some b' =>
        cases ha
        obtain ⟨hd, rfl⟩ := htr
        exact hs.fgn.atom tid hd (hst b rfl) _
  obtain ⟨ρ', c₂', h', hr, hag, hfv, hpd, -, hall, hfg⟩ :=
    writeSuccs_simAt A tid hs.rel hs.bnd hs.promDom hivs hivsb htr hex hexb hxr hxrb hgap h
  obtain ⟨hb2, hm⟩ := writeSuccs_bnd A tid ivs hs.bnd hivsb hexb h
  exact ⟨ρ', c₂', h', ⟨hr, hb2, hpd, hall hs.domAll, hs.ivr.lift hs.ivb hfv, hs.ivb.mono hm,
    fun n hn => Nat.le_trans (hs.nle n hn) hm, hfg N L hs.nle hs.fgn⟩, ⟨hag, hfv⟩, hm⟩

theorem SimInvAt.fence {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInvAt ρ N L iv iv' c c')
    (k : FenceKind) : SimInvAt ρ N L iv iv' (fenceStep c k) (fenceStep c' k) := by
  have hm := fenceStep_mem c k
  have hm' := fenceStep_mem c' k
  have hp : (fenceStep c k).prom = c.prom := by cases k <;> rfl
  exact ⟨fenceStep_sim hs.rel k, fenceStep_bnd hs.bnd k, hp ▸ hs.promDom, hm ▸ hs.domAll, hs.ivr,
    hm ▸ hs.ivb, hm ▸ hs.nle, hm' ▸ hs.fgn⟩

theorem SimInvAt.fenceOpt {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInvAt ρ N L iv iv' c c')
    (b : Bool) (k : FenceKind) :
    SimInvAt ρ N L iv iv' (if b then fenceStep c k else c) (if b then fenceStep c' k else c') := by
  cases b
  · exact hs
  · exact hs.fence k

theorem SimInvAt.post {ρ : TMap} {iv iv' : InstrViews} {c c' : Ctx} (hs : SimInvAt ρ N L iv iv' c c')
    (k : RmwKind) (noRet : Bool) (l : Loc) :
    SimInvAt ρ N L iv iv' (Kraken.Promising.rmwPost A k noRet l c) (Kraken.Promising.rmwPost A k noRet l c') := by
  have hv := hs.rel.views
  have hc := hs.rel
  have hb := (rmwPost_bnd A hs.bnd k noRet l).1
  revert hb
  unfold rmwPost
  by_cases hk : (A.rmwKind k == .acqRel && !noRet) = true
  · simp only [hk, ↓reduceIte]
    intro hb
    exact ⟨⟨hc.mem, ⟨hv.coh, le_fv_max hv.vrNew (hv.coh l), hv.vrOld, hv.vrOldNR, le_fv_max hv.vwNew (hv.coh l),
      hv.vwOld, hv.vwOldNT, hv.vCAP, hv.vRel, hv.fwd, hv.xclb⟩, hc.prom, hc.loadViews, hc.succView, rfl, hc.stores⟩,
      hb, hs.promDom, hs.domAll, hs.ivr, hs.ivb, hs.nle, hs.fgn⟩
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    intro hb
    exact ⟨⟨hc.mem, hv, hc.prom, hc.loadViews, hc.succView, rfl, hc.stores⟩, hb, hs.promDom, hs.domAll, hs.ivr,
      hs.ivb, hs.nle, hs.fgn⟩

/-- **One instruction's event tree, several thresholds.** Under `SimInvAt`,
every source run of the tree that is `StaleFree` at every threshold in `N` is
matched by a target run with the same final machine state, ending in
`SimInvAt` again for an extension of the map. -/
theorem runTree_simAt {σ : Type} {iv iv' : InstrViews} (tree : EvTree σ) :
    ∀ (ρ : TMap) (c c' : Ctx) (s : σ) (c₂ : Ctx), SimInvAt ρ N L iv iv' c c' →
      (∀ n, N n → StaleFree A tid iv n L c tree) → .ok (s, c₂) ∈ runTree A tid iv c tree →
      ∃ ρ' : TMap, ∃ c₂', .ok (s, c₂') ∈ runTree A tid iv' c' tree ∧ SimInvAt ρ' N L iv iv' c₂ c₂' ∧
        Ext ρ ρ' c.mem.last ∧ c.mem.last ≤ c₂.mem.last := by
  induction tree with
  | done s0 =>
    intro ρ c c' s c₂ hs _ h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ρ, c', by simp [runTree], hs, Ext.refl _ _, Nat.le_refl _⟩
  | fault msg =>
    intro ρ c c' s c₂ _ _ h
    simp [runTree] at h
  | choose n k ih =>
    intro ρ c c' s c₂ hs hsf h
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨i, hi, h⟩ := h
    obtain ⟨ρ', c₂', h', hs', hag⟩ := ih i ρ c c' s c₂ hs (fun m hm => hsf m hm i) h
    exact ⟨ρ', c₂', ⟨i, hi, h'⟩, hs', hag⟩
  | load k xcl l ret ih =>
    intro ρ c c' s c₂ hs hsf h
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨⟨t, v, c0⟩, hx, h⟩ := h
    obtain ⟨c0', hx', hs0, hm0⟩ := hs.read A hx (fun m hm => (hsf m hm _ hx).1)
    obtain ⟨ρ', c₂', h', hs', hag, hm⟩ := ih v ρ c0 c0' s c₂ hs0 (fun m hm => (hsf m hm _ hx).2) h
    rw [hm0] at hag hm
    exact ⟨ρ', c₂', ⟨(ρ.f t, v, c0'), hx', h'⟩, hs', hag, hm⟩
  | store k xcl l v ret ih =>
    intro ρ c c' s c₂ hs hsf h
    have hst : ∀ m, N m → xcl = true → L l → ∀ a, c.views.xclb.map (·.1) = some a → m < a := fun m hm => by
      obtain ⟨h1, -, -⟩ := hsf m hm; exact h1
    have hsfw : ∀ m, N m → ∀ c' ∈ writeSuccs A tid (iv.forStore c.stores) c k xcl l v
        (if xcl then c.views.xclb.map (·.1) else none) 0 (if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0), StaleFree A tid iv m L c' (ret true) := fun m hm => by
      obtain ⟨-, h2, -⟩ := hsf m hm; exact h2
    have hsff : ∀ m, N m → StaleFree A tid iv m L
        { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } (ret false) :=
      fun m hm => by obtain ⟨-, -, h3⟩ := hsf m hm; exact h3
    have hv := hs.rel.views
    have htr : TrRel ρ (if xcl then c.views.xclb.map (·.1) else none)
        (if xcl then c'.views.xclb.map (·.1) else none) := by
      cases xcl
      · trivial
      · have hx := hv.xclb
        revert hx
        rcases c.views.xclb with _ | ⟨a, b, l1⟩ <;> rcases c'.views.xclb with _ | ⟨a', b', l2⟩ <;>
          simp only [XclLe, TrRel, Option.map, imp_self, ↓reduceIte]
        rintro ⟨h1, h2, -, -⟩; exact ⟨h1, h2⟩
    have hst' : ∀ a, (if xcl then c.views.xclb.map (·.1) else none) = some a → ∀ m, N m → L l → m < a := by
      intro a ha m hm hl
      cases xcl
      · cases ha
      · exact hst m hm rfl hl a ha
    simp only [runTree, List.mem_append] at h ⊢
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨hp, c0, hc0, h⟩ := h
      have hivs : IVLe ρ (iv'.forStore c'.stores) (iv.forStore c.stores) := hs.rel.stores ▸ hs.ivr.forStore c.stores
      obtain ⟨ρ0, c0', hc0', hs0, hag0, hm0⟩ :=
        hs.write A tid hivs (hs.ivb.forStore c.stores) htr hst' (Nat.zero_le _) (Nat.zero_le _)
          (xr' := if xcl then (c'.views.xclb.map (·.2.1)).getD 0 else 0)
          (by cases xcl; exact Nat.zero_le _; exact hs.rel.views.xclb.xclRead)
          (by cases xcl; exact Nat.zero_le _; exact hs.bnd.views.xclRead) hc0
      obtain ⟨ρ', c₂', h', hs', hag, hm⟩ := ih true ρ0 c0 c0' s c₂ hs0 (fun m hm => hsfw m hm c0 hc0) h
      refine ⟨ρ', c₂', Or.inl ?_, hs', hag0.trans hag hm0, Nat.le_trans hm0 hm⟩
      rw [List.mem_ite_nil_left, List.mem_flatMap]
      refine ⟨?_, c0', ?_, h'⟩
      · have hx := hv.xclb
        revert hp hx
        generalize c.views.xclb = a
        generalize c'.views.xclb = b
        rcases a with _ | ⟨a1, a2, l1⟩ <;> rcases b with _ | ⟨b1, b2, l2⟩ <;> intro hp hx
        · exact hp
        · exact (hx : False).elim
        · exact (hx : False).elim
        · obtain ⟨-, -, -, rfl⟩ := hx; exact hp
      · exact hc0'
    · rw [List.mem_ite_nil_right] at h
      have hs0 : SimInvAt ρ N L iv iv'
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }
          { c' with views := { c'.views with xclb := none }, succView := 0, log := c'.log ++ [.xclFail l] } :=
        ⟨⟨hs.rel.mem, ⟨hv.coh, hv.vrNew, hv.vrOld, hv.vrOldNR, hv.vwNew, hv.vwOld, hv.vwOldNT, hv.vCAP, hv.vRel,
            hv.fwd, trivial⟩, hs.rel.prom, hs.rel.loadViews, Nat.zero_le _, hs.rel.rmwWrote, hs.rel.stores⟩,
          ⟨hs.bnd.views.xclbNone, hs.bnd.loadViews, Nat.zero_le _⟩, hs.promDom, hs.domAll, hs.ivr, hs.ivb,
          hs.nle, hs.fgn⟩
      obtain ⟨ρ', c₂', h', hs', hag⟩ := ih false ρ _ _ s c₂ hs0 hsff h.2
      refine ⟨ρ', c₂', Or.inr ?_, hs', hag⟩
      rw [List.mem_ite_nil_right]
      exact ⟨h.1, h'⟩
  | fence k ret ih =>
    intro ρ c c' s c₂ hs hsf h
    simp only [runTree] at h ⊢
    have := ih () ρ _ _ s c₂ (hs.fence k) hsf h
    rw [fenceStep_mem] at this
    exact this
  | rmw k noRet l op ret ih =>
    intro ρ c c' s c₂ hs hsf h
    simp only [runTree] at h ⊢
    simp only [StaleFree] at hsf
    have hs1 := hs.fenceOpt A.rmwFence .sy
    have hm1 : (if A.rmwFence then fenceStep c .sy else c).mem = c.mem := by
      split <;> simp only [fenceStep_mem]
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h hs1 hsf hm1
    generalize (if A.rmwFence then fenceStep c' .sy else c') = c1' at hs1 ⊢
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c3⟩, hx, h⟩ := h
    have hst := fun m (hm : N m) => (hsf m hm _ hx).1
    have hsfn := fun m (hm : N m) => (hsf m hm _ hx).2.1
    have hsfs := fun m (hm : N m) => (hsf m hm _ hx).2.2
    obtain ⟨c3', hx', hs3, hm3⟩ := hs1.read A hx (fun m hm hl ht => (hst m hm hl ht).1)
    have htr3 : tr ≤ c3.mem.last := by
      have := readSuccs_bnd A iv hs1.bnd hs1.ivb hx
      rw [this.2.2]; exact this.2.1
    simp only at h hst hsfn hsfs
    have hfo : ∀ x : Ctx, (if A.rmwFence then fenceStep x .sy else x).mem = x.mem := by
      intro x; split <;> simp only [fenceStep_mem]
    cases hop : op old with
    | none =>
      rw [hop] at h
      obtain ⟨ρ', c₂', h', hs', hag, hm⟩ := ih old ρ _ _ s c₂ (hs3.fenceOpt A.rmwFence .sy) hsfn h
      rw [hfo, hm3, hm1] at hag hm
      exact ⟨ρ', c₂', List.mem_flatMap.mpr ⟨(ρ.f tr, old, c3'), hx', by simp only [hop]; exact h'⟩, hs', hag, hm⟩
    | some new =>
      rw [hop] at h
      simp only [List.mem_flatMap] at h
      obtain ⟨c4, hc4, h⟩ := h
      have hst4 : ∀ a, some tr = some a → ∀ m, N m → L l → m < a := by
        intro a ha m hm hl
        cases ha
        refine Nat.lt_of_not_le fun hle => ?_
        rw [(hst m hm hl hle).2] at hop; cases hop
      obtain ⟨ρ4, c4', hc4', hs4, hag4, hm4⟩ := hs3.write A tid hs3.ivr hs3.ivb (tr := some tr)
        (tr' := some (ρ.f tr)) ⟨hs3.domAll tr htr3, rfl⟩ hst4
        (hs3.rel.loadViews.getLastD 0 0 (by rw [ρ.fv_zero]; exact Nat.le_refl _))
        (getLastD_le hs3.bnd.loadViews 0 (Nat.zero_le _)) (Nat.zero_le _) (Nat.zero_le _) hc4
      have hs5 := (hs4.post A k noRet l).fenceOpt A.rmwFence .sy
      change .ok (s, c₂) ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c4) .sy else rmwPost A k noRet l c4) (ret old) at h
      obtain ⟨ρ', c₂', h', hs', hag, hm⟩ := ih old ρ4 _ _ s c₂ hs5 (fun m hm => hsfs m hm new hop c4 hc4) h
      have hpm : (rmwPost A k noRet l c4).mem = c4.mem := by
        unfold rmwPost; split <;> rfl
      rw [hfo, hpm] at hag hm
      rw [hm3, hm1] at hag4 hm4
      refine ⟨ρ', c₂', List.mem_flatMap.mpr ⟨(ρ.f tr, old, c3'), hx', ?_⟩, hs', hag4.trans hag hm4,
        Nat.le_trans hm4 hm⟩
      simp only [hop, List.mem_flatMap]
      exact ⟨c4', hc4', h'⟩

/-- **One instruction's event tree.** Under `SimInv`, every source run of the
tree that is `StaleFree` is matched by a target run with the same final
machine state (so the same register effects), ending in `SimInv` again for an
extension of the map. With no foreign messages (`runTree_sim_noForeign`) the
side condition disappears. -/
theorem runTree_sim {σ : Type} {iv iv' : InstrViews} (tree : EvTree σ) :
    ∀ (ρ : TMap) (c c' : Ctx) (s : σ) (c₂ : Ctx), SimInv ρ n L iv iv' c c' →
      StaleFree A tid iv n L c tree → .ok (s, c₂) ∈ runTree A tid iv c tree →
      ∃ ρ' : TMap, ∃ c₂', .ok (s, c₂') ∈ runTree A tid iv' c' tree ∧ SimInv ρ' n L iv iv' c₂ c₂' ∧
        Ext ρ ρ' c.mem.last ∧ c.mem.last ≤ c₂.mem.last := by
  intro ρ c c' s c₂ hs hsf h
  obtain ⟨ρ', c₂', h', hs', hext, hm⟩ :=
    runTree_simAt A tid (N := (· = n)) tree ρ c c' s c₂ hs.toAt (fun m hm => hm ▸ hsf) h
  exact ⟨ρ', c₂', h', hs'.toInv, hext, hm⟩

/-- `runTree_sim` without foreign messages (the environment instance: `ρ =
id`, the same memory, target views lower): no side condition. -/
theorem runTree_sim_noForeign {σ : Type} {iv iv' : InstrViews} (tree : EvTree σ) {ρ : TMap} {c c' : Ctx}
    (hrel : CtxRel ρ c c') (hb : c.Bnd) (hpd : ∀ s ∈ c.prom, ρ.dom s) (hall : ∀ s ≤ c.mem.last, ρ.dom s)
    (hiv : IVLe ρ iv' iv) (hivb : iv.Le c.mem.last) (hnf : NoForeign ρ c'.mem) {s : σ} {c₂ : Ctx}
    (h : .ok (s, c₂) ∈ runTree A tid iv c tree) :
    ∃ ρ' : TMap, ∃ c₂', .ok (s, c₂') ∈ runTree A tid iv' c' tree ∧ CtxRel ρ' c₂ c₂' ∧
      (∀ s, ρ.dom s → ρ'.dom s ∧ ρ'.f s = ρ.f s) := by
  obtain ⟨ρ', c₂', h', hs', hag, -⟩ := runTree_sim (n := 0) (L := fun _ => False) A tid tree ρ c c' s c₂
    ⟨hrel, hb, hpd, hall, hiv, hivb, Nat.zero_le _, hnf.fgnSep 0 _⟩ (staleFree_bot A tid iv 0 tree c) h
  exact ⟨ρ', c₂', h', hs'.rel, hag.1⟩

end Tree

/-! ## One instruction, thread level (proved)

`stepOne_sim` lifts `runTree_sim` through `instrViews` and `finishInstr`: the
register views of the target thread are at most the floor images of the
source's (`ThreadRel`). Chaining it over a run of instructions, with other
threads' messages appended to both memories (`freshMap`), is the multi-step
form every consumer uses. -/

section ThreadLevel

variable {I : ISA} (A : Arch) (tid : Nat)

theorem getElem!_set! (a : Array View) (i j x : Nat) :
    (a.set! i x)[j]! = if i = j ∧ i < a.size then x else a[j]! := by
  simp only [Array.set!, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hlt : i < a.size
    · simp [hlt]
    · simp [hlt]
  · simp [hij]

theorem size_set! (a : Array View) (i x : Nat) : (a.set! i x).size = a.size := by simp [Array.set!]

theorem arr_le {a : Array View} {n i : Nat} (h : ∀ v ∈ a, v ≤ n) : a[i]! ≤ n := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  match hi : a[i]? with
  | none => exact Nat.zero_le _
  | some v => exact h v (Array.mem_iff_getElem?.mpr ⟨i, hi⟩)

theorem ThreadRel.setRegView {ρ : TMap} {t t' : Thread I} (h : ThreadRel ρ t t') (r : I.RegId)
    {rv rv' wv wv' : View} (hr : rv' ≤ ρ.fv rv) (hw : wv' ≤ ρ.fv wv) :
    ThreadRel ρ (t.setRegView r rv wv) (t'.setRegView r rv' wv') := by
  refine ⟨h.st, ?_, ?_, fun i => ?_, fun i => ?_, h.views, h.prom⟩
  · show (t'.rview.set! _ rv').size = (t.rview.set! _ rv).size
    rw [size_set!, size_set!, h.rsize]
  · show (t'.wview.set! _ wv').size = (t.wview.set! _ wv).size
    rw [size_set!, size_set!, h.wsize]
  · show (t'.rview.set! _ rv')[i]! ≤ ρ.fv ((t.rview.set! _ rv)[i]!)
    rw [getElem!_set!, getElem!_set!, h.rsize]
    by_cases hc : (I.regIndex r).val = i ∧ (I.regIndex r).val < t.rview.size
    · rw [ite_eq_left hc, ite_eq_left hc]; exact hr
    · rw [ite_eq_right hc, ite_eq_right hc]; exact h.rv i
  · show (t'.wview.set! _ wv')[i]! ≤ ρ.fv ((t.wview.set! _ wv)[i]!)
    rw [getElem!_set!, getElem!_set!, h.wsize]
    by_cases hc : (I.regIndex r).val = i ∧ (I.regIndex r).val < t.wview.size
    · rw [ite_eq_left hc, ite_eq_left hc]; exact hw
    · rw [ite_eq_right hc, ite_eq_right hc]; exact h.wv i

private theorem foldl_rel' {α β γ : Type} (R : β → γ → Prop) (f : β → α → β) (g : γ → α → γ)
    (hf : ∀ b c x, R b c → R (f b x) (g c x)) : ∀ (xs : List α) (b : β) (c : γ), R b c → R (xs.foldl f b) (xs.foldl g c)
  | [], _, _, h => h
  | x :: xs, b, c, h => foldl_rel' R f g hf xs (f b x) (g c x) (hf b c x h)

theorem joinViews_le' {ρ : TMap} {t t' : Thread I} (h : ThreadRel ρ t t') (rs : List I.RegId) :
    (t'.joinViews rs).1 ≤ ρ.fv (t.joinViews rs).1 ∧ (t'.joinViews rs).2 ≤ ρ.fv (t.joinViews rs).2 := by
  unfold Thread.joinViews
  apply foldl_rel' (fun (b a : View × View) => a.1 ≤ ρ.fv b.1 ∧ a.2 ≤ ρ.fv b.2)
  · intro a b x hab
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    exact ⟨le_fv_max hab.1 (h.rv _), le_fv_max hab.2 (h.wv _)⟩
  · rw [ρ.fv_zero]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem instrViews_le' {ρ : TMap} {t t' : Thread I} (h : ThreadRel ρ t t') (d : InstrDeps I.RegId) :
    IVLe ρ (instrViews t' d) (instrViews t d) := by
  have ha := joinViews_le' h d.addrRegs
  have hd := joinViews_le' h d.dataRegs
  have hc := joinViews_le' h d.condRegs
  have hdv : (if d.dataRegsPer.isEmpty = true then t'.joinViews d.dataRegs else (0, 0)).1 ≤
      ρ.fv (if d.dataRegsPer.isEmpty = true then t.joinViews d.dataRegs else (0, 0)).1 ∧
      (if d.dataRegsPer.isEmpty = true then t'.joinViews d.dataRegs else (0, 0)).2 ≤
      ρ.fv (if d.dataRegsPer.isEmpty = true then t.joinViews d.dataRegs else (0, 0)).2 := by
    split
    · exact hd
    · rw [ρ.fv_zero]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨ha.1, ha.2, hdv.1, hdv.2, hc.2, ?_⟩
  show Rel2 _ (d.dataRegsPer.map t'.joinViews) (d.dataRegsPer.map t.joinViews)
  generalize d.dataRegsPer = rss
  induction rss with
  | nil => exact .nil
  | cons rs rss ih => exact .cons (joinViews_le' h rs) ih

theorem Rel2.length_eq {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β} (h : Rel2 R xs ys) :
    xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Rel2.foldl_max {ρ : TMap} {ys xs : List View} (h : Rel2 (fun a' a => a' ≤ ρ.fv a) ys xs) :
    ∀ a' a, a' ≤ ρ.fv a → ys.foldl max a' ≤ ρ.fv (xs.foldl max a) := by
  induction h with
  | nil => intro a' a h; exact h
  | cons hab _ ih => intro a' a h; exact ih _ _ (le_fv_max h hab)

theorem zip_fold_le {ρ : TMap} : ∀ (rs : List I.RegId) (ys xs : List View) (a b : Thread I),
    Rel2 (fun a' a => a' ≤ ρ.fv a) ys xs → ThreadRel ρ a b →
    ThreadRel ρ ((rs.zip xs).foldl (fun t (rv : I.RegId × View) => t.setRegView rv.1 rv.2 rv.2) a)
      ((rs.zip ys).foldl (fun t (rv : I.RegId × View) => t.setRegView rv.1 rv.2 rv.2) b)
  | [], _, _, _, _, _, hab => by simpa using hab
  | _ :: _, [], [], _, _, _, hab => by simpa using hab
  | _ :: _, [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, _, h, _ => by cases h
  | r :: rs, y :: ys, x :: xs, a, b, h, hab => by
    cases h with
    | cons hyx h' =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      exact zip_fold_le rs ys xs _ _ h' (hab.setRegView r hyx hyx)

/-- `finishInstr` on related threads, contexts and instruction views. -/
theorem finishInstr_sim {ρ : TMap} {t t' : Thread I} {d : InstrDeps I.RegId} {iv iv' : InstrViews} {st : I.State}
    {c c' : Ctx} (h : ThreadRel ρ t t') (hc : CtxRel ρ c c') (hiv : IVLe ρ iv' iv) :
    ∀ th ∈ finishInstr t d iv st c, ∃ th' ∈ finishInstr t' d iv' st c', ThreadRel ρ th th' := by
  intro th hth
  have hload := hc.loadViews.foldl_max 0 0 (by rw [ρ.fv_zero]; exact Nat.le_refl _)
  have hlen : (d.loadDefs.length == c'.loadViews.length) = (d.loadDefs.length == c.loadViews.length) := by
    rw [hc.loadViews.length_eq]
  have hinR : (if d.isPick then max iv'.addrR iv'.dataR else max (max iv'.addrR iv'.dataR) iv'.condW) ≤
      ρ.fv (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW) := by
    split
    · exact le_fv_max hiv.addrR hiv.dataR
    · exact le_fv_max (le_fv_max hiv.addrR hiv.dataR) hiv.condW
  have hinW := le_fv_max (le_fv_max hiv.addrW hiv.dataW) hiv.condW
  have h1 : ThreadRel ρ { t with st, views := c.views, prom := c.prom } { t' with st, views := c'.views, prom := c'.prom } :=
    ⟨rfl, h.rsize, h.wsize, h.rv, h.wv, hc.views, hc.prom⟩
  have h2 : ThreadRel ρ
      (d.statusDefs.foldl (fun t r => t.setRegView r c.succView c.succView)
        (d.defs.foldl (fun t r => t.setRegView r
          (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW)
          (max (max iv.addrW iv.dataW) iv.condW)) { t with st, views := c.views, prom := c.prom }))
      (d.statusDefs.foldl (fun t r => t.setRegView r c'.succView c'.succView)
        (d.defs.foldl (fun t r => t.setRegView r
          (if d.isPick then max iv'.addrR iv'.dataR else max (max iv'.addrR iv'.dataR) iv'.condW)
          (max (max iv'.addrW iv'.dataW) iv'.condW)) { t' with st, views := c'.views, prom := c'.prom })) := by
    apply foldl_rel' (ThreadRel ρ)
    · intro a b x hab; exact hab.setRegView x hc.succView hc.succView
    · apply foldl_rel' (ThreadRel ρ) _ _ _ _ _ _ h1
      intro a b x hab; exact hab.setRegView x hinR hinW
  have finish : ∀ a b : Thread I, ThreadRel ρ a b →
      ThreadRel ρ (if d.isBranch then { a with views := { a.views with vCAP := max a.views.vCAP iv.condW } } else a)
        (if d.isBranch then { b with views := { b.views with vCAP := max b.views.vCAP iv'.condW } } else b) := by
    intro a b hab
    split
    · have hv := hab.views
      exact ⟨hab.st, hab.rsize, hab.wsize, hab.rv, hab.wv, ⟨hv.coh, hv.vrNew, hv.vrOld, hv.vrOldNR, hv.vwNew,
        hv.vwOld, hv.vwOldNT, le_fv_max hv.vCAP hiv.condW, hv.vRel, hv.fwd, hv.xclb⟩, hab.prom⟩
    · exact hab
  have h3 : ∀ a b : Thread I, ThreadRel ρ a b → ThreadRel ρ
      (if d.loadDefs.length == c.loadViews.length then
        (d.loadDefs.zip c.loadViews).foldl (fun t (r, v) => t.setRegView r v v) a
      else d.loadDefs.foldl (fun t r => t.setRegView r (c.loadViews.foldl max 0) (c.loadViews.foldl max 0)) a)
      (if d.loadDefs.length == c'.loadViews.length then
        (d.loadDefs.zip c'.loadViews).foldl (fun t (r, v) => t.setRegView r v v) b
      else d.loadDefs.foldl (fun t r => t.setRegView r (c'.loadViews.foldl max 0) (c'.loadViews.foldl max 0)) b) := by
    intro a b hab
    rw [hlen]
    split
    · exact zip_fold_le _ _ _ _ _ hc.loadViews hab
    · apply foldl_rel' (ThreadRel ρ) _ _ _ _ _ _ hab
      intro a b x hab; exact hab.setRegView x hload hload
  have h4 : ∀ a b : Thread I, ThreadRel ρ a b → ThreadRel ρ
      (d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r) (max (t.wviewOf r) (c.loadViews.foldl max 0))) a)
      (d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r) (max (t.wviewOf r) (c'.loadViews.foldl max 0))) b) := by
    intro a b hab
    apply foldl_rel' (ThreadRel ρ) _ _ _ _ _ _ hab
    intro a b x hab; exact hab.setRegView x (hab.rv _) (le_fv_max (hab.wv _) hload)
  simp only [finishInstr] at hth ⊢
  rw [hc.rmwWrote]
  split at hth
  · rename_i hcw
    simp only [hcw, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hth ⊢
    rcases hth with rfl | rfl
    · exact ⟨_, .inl rfl, finish _ _ (h4 _ _ h2)⟩
    · exact ⟨_, .inr rfl, finish _ _ (h3 _ _ h2)⟩
  · rename_i hcw
    simp only [hcw, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hth ⊢
    subst hth
    exact ⟨_, rfl, finish _ _ (h3 _ _ h2)⟩

/-- Register views lift along an extension when they are bounded. -/
theorem ThreadRel.lift {ρ ρ' : TMap} {t t' : Thread I} {m : Nat} (h : ThreadRel ρ t t') (hb : t.RegsLe m)
    (hext : Ext ρ ρ' m) {vs vs' : Views} {p p' : List Time} (hv : ViewsLe ρ' vs' vs) (hp : PromRel ρ' p p') :
    ThreadRel ρ' { t with views := vs, prom := p } { t' with views := vs', prom := p' } :=
  ⟨h.st, h.rsize, h.wsize, fun i => by rw [hext.2 _ (arr_le hb.1)]; exact h.rv i,
    fun i => by rw [hext.2 _ (arr_le hb.2)]; exact h.wv i, hv, hp⟩

variable {n : Nat} {L : Loc → Prop}

variable {N : Nat → Prop}

/-- **One instruction, thread level.** A source instruction of a bounded
thread is matched by the target thread's instruction, ending in related
threads and memories for an extension of the map, provided the event tree's
run is `StaleFree` at every threshold in `N` (vacuous without foreign
messages). General form of `stepOne_sim`, foreign messages separated at a set
of thresholds (`FgnSepAt`). -/
theorem stepOne_simAt {ρ : TMap} {t t' : Thread I} {mem mem' : Memory}
    (hT : ThreadRel ρ t t') (hm : MemRel ρ mem mem') (hb : t.Bnd mem.last)
    (hpd : ∀ s ∈ t.prom, ρ.dom s) (hall : ∀ s ≤ mem.last, ρ.dom s) (hn : ∀ n, N n → n ≤ mem.last)
    (hfg : FgnSepAt ρ mem' N L)
    (hsf : ∀ tree, I.exec t.st = some tree → ∀ n, N n → StaleFree A tid (instrViews t (I.deps t.st)) n L
      { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } tree)
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    ∃ ρ' : TMap, ∃ outs' o', stepOne A t' tid mem' = some outs' ∧ .ok o' ∈ outs' ∧
      ThreadRel ρ' o.thread o'.thread ∧ MemRel ρ' o.mem o'.mem ∧ Ext ρ ρ' mem.last ∧
      (∀ s ∈ o.thread.prom, ρ'.dom s) ∧ (∀ s ≤ o.mem.last, ρ'.dom s) ∧ (∀ n, N n → n ≤ o.mem.last) ∧
      FgnSepAt ρ' o'.mem N L ∧ o.thread.Bnd o.mem.last := by
  unfold stepOne at hstep ⊢
  rw [hT.st]
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c2⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hiv := instrViews_le' hT (I.deps t.st)
      have hivb := instrViews_le hb.regs (I.deps t.st)
      have hs : SimInvAt ρ N L (instrViews t (I.deps t.st)) (instrViews t' (I.deps t.st))
          { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }
          { views := t'.views, prom := t'.prom, mem := mem', log := [.instr tid (I.showInstr t.st)] } :=
        ⟨⟨hm, hT.views, hT.prom, .nil, Nat.zero_le _, rfl, rfl⟩,
          ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩, hpd, hall, hiv, hivb, hn, hfg⟩
      obtain ⟨ρ', c2', hr', hs2, hext, hml⟩ := runTree_simAt A tid tree ρ _ _ st c2 hs (hsf tree hex) hr
      have h0 := hT.lift hb.regs hext hs2.rel.views hs2.rel.prom
      have e : finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st c2 =
          finishInstr { t with views := c2.views, prom := c2.prom } (I.deps t.st) (instrViews t (I.deps t.st)) st c2 :=
        rfl
      have e' : finishInstr t' (I.deps t.st) (instrViews t' (I.deps t.st)) st c2' =
          finishInstr { t' with views := c2'.views, prom := c2'.prom } (I.deps t.st)
            (instrViews t' (I.deps t.st)) st c2' := rfl
      rw [e] at hth
      obtain ⟨th', hth', hrel⟩ := finishInstr_sim h0 hs2.rel (hiv.lift hivb hext.2) th hth
      rw [← e'] at hth'
      rw [← e] at hth
      refine ⟨ρ', _, _, rfl, List.mem_flatMap.mpr ⟨.ok (st, c2'), hr', List.mem_map.mpr ⟨th', hth', rfl⟩⟩,
        hrel, hs2.rel.mem, hext, ?_, hs2.domAll, hs2.nle, hs2.fgn, ?_⟩
      · rw [(finishInstr_relKey hth).1]; exact hs2.promDom
      · exact finishInstr_bnd hs2.bnd.views hs2.bnd.loadViews hs2.bnd.succView (hivb.mono hml)
          (hb.regs.mono hml) th hth

/-- **One instruction, thread level.** A source instruction of a bounded
thread is matched by the target thread's instruction, ending in related
threads and memories for an extension of the map, provided the event tree's
run is `StaleFree` (vacuous without foreign messages). -/
theorem stepOne_sim {ρ : TMap} {t t' : Thread I} {mem mem' : Memory}
    (hT : ThreadRel ρ t t') (hm : MemRel ρ mem mem') (hb : t.Bnd mem.last)
    (hpd : ∀ s ∈ t.prom, ρ.dom s) (hall : ∀ s ≤ mem.last, ρ.dom s) (hn : n ≤ mem.last)
    (hfg : FgnSep ρ mem' n L)
    (hsf : ∀ tree, I.exec t.st = some tree → StaleFree A tid (instrViews t (I.deps t.st)) n L
      { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } tree)
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    ∃ ρ' : TMap, ∃ outs' o', stepOne A t' tid mem' = some outs' ∧ .ok o' ∈ outs' ∧
      ThreadRel ρ' o.thread o'.thread ∧ MemRel ρ' o.mem o'.mem ∧ Ext ρ ρ' mem.last ∧
      (∀ s ∈ o.thread.prom, ρ'.dom s) ∧ (∀ s ≤ o.mem.last, ρ'.dom s) ∧ n ≤ o.mem.last ∧
      FgnSep ρ' o'.mem n L ∧ o.thread.Bnd o.mem.last := by
  obtain ⟨ρ', outs', o', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    stepOne_simAt A tid (N := (· = n)) hT hm hb hpd hall (fun m hm => hm ▸ hn) hfg.toAt
      (fun tree he m hm => by subst hm; exact hsf tree he) hstep ho
  exact ⟨ρ', outs', o', h1, h2, h3, h4, h5, h6, h7, h8 n rfl, h9.toSep, h10⟩

/-- Promise-free solo runs (`ThreadNP`) whose every instruction's event tree
is `StaleFree` for `n`, `L` (the source-run side condition of B2 / O11). -/
inductive ThreadSF (n : Nat) (L : Loc → Prop) : Thread I × Memory → Thread I × Memory → Prop
  | refl (p : Thread I × Memory) : ThreadSF n L p p
  | step {p q r : Thread I × Memory} : ThreadStep A tid p q →
      (∀ tree, I.exec p.1.st = some tree → StaleFree A tid (instrViews p.1 (I.deps p.1.st)) n L
        { views := p.1.views, prom := p.1.prom, mem := p.2, log := [.instr tid (I.showInstr p.1.st)] } tree) →
      ThreadSF n L q r → ThreadSF n L p r

/-- Promise-free solo runs (`ThreadNP`) whose every instruction's event tree
is `StaleFree` at every threshold in `N` for `L`: `ThreadSF` with several
thresholds (interleaved foreign appends). -/
inductive ThreadSFAt (N : Nat → Prop) (L : Loc → Prop) : Thread I × Memory → Thread I × Memory → Prop
  | refl (p : Thread I × Memory) : ThreadSFAt N L p p
  | step {p q r : Thread I × Memory} : ThreadStep A tid p q →
      (∀ tree, I.exec p.1.st = some tree → ∀ n, N n → StaleFree A tid (instrViews p.1 (I.deps p.1.st)) n L
        { views := p.1.views, prom := p.1.prom, mem := p.2, log := [.instr tid (I.showInstr p.1.st)] } tree) →
      ThreadSFAt N L q r → ThreadSFAt N L p r

/-- A single-threshold `StaleFree` run is a `ThreadSFAt` run at `N = {n}`. -/
theorem ThreadSF.toAt {p r : Thread I × Memory} (h : ThreadSF A tid n L p r) : ThreadSFAt A tid (· = n) L p r := by
  induction h with
  | refl p => exact .refl p
  | step hs hsf _ ih => exact .step hs (fun tree he m hm => by subst hm; exact hsf tree he) ih

/-- Without watched locations every solo run qualifies. -/
theorem ThreadNP.toSF {p r : Thread I × Memory} (h : ThreadNP A tid p r) (n : Nat) :
    ThreadSF A tid n (fun _ => False) p r := by
  induction h with
  | refl p => exact .refl p
  | step hs _ ih => exact .step hs (fun tree _ => staleFree_bot A tid _ n tree _) ih

/-- **Solo runs, multi-step, several thresholds.** A `StaleFree` promise-free solo run of a
bounded thread is matched by a solo run of the related target thread. The
foreign target messages are fixed before the run (`FgnSepAt` at the start);
the thread's own writes extend the map (`freshMap`). For foreign messages
appended *during* the run use `SimState.step` / `SimState.appendForeign`. -/
theorem threadSFAt_sim {p r : Thread I × Memory} (h : ThreadSFAt A tid N L p r) :
    ∀ (ρ : TMap) (t' : Thread I) (mem' : Memory), ThreadRel ρ p.1 t' → MemRel ρ p.2 mem' →
      p.1.Bnd p.2.last → (∀ s ∈ p.1.prom, ρ.dom s) → (∀ s ≤ p.2.last, ρ.dom s) → (∀ n, N n → n ≤ p.2.last) →
      FgnSepAt ρ mem' N L →
      ∃ ρ' : TMap, ∃ r' : Thread I × Memory, ThreadNP A tid (t', mem') r' ∧
        ThreadRel ρ' r.1 r'.1 ∧ MemRel ρ' r.2 r'.2 ∧ (∀ s, ρ.dom s → ρ'.dom s ∧ ρ'.f s = ρ.f s) ∧
        (∀ s ∈ r.1.prom, ρ'.dom s) ∧ FgnSepAt ρ' r'.2 N L := by
  induction h with
  | refl p =>
    intro ρ t' mem' hT hm _ hpd _ _ hfg
    exact ⟨ρ, (t', mem'), .refl _, hT, hm, fun _ h => ⟨h, rfl⟩, hpd, hfg⟩
  | step hs hsf _ ih =>
    intro ρ t' mem' hT hm hb hpd hall hn hfg
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
    obtain ⟨ρ1, outs', o', hstep', ho', hT1, hm1, hext1, hpd1, hall1, hn1, hfg1, hb1⟩ :=
      stepOne_simAt A tid hT hm hb hpd hall hn hfg hsf hstep ho
    obtain ⟨ρ2, r', hr', hT2, hm2, hag2, hpd2, hfg2⟩ :=
      ih ρ1 o'.thread o'.mem hT1 hm1 hb1 hpd1 hall1 hn1 hfg1
    exact ⟨ρ2, r', .step ⟨outs', o', hstep', ho', rfl⟩ hr', hT2, hm2,
      fun s hs => ⟨(hag2 s (hext1.1 s hs).1).1, by rw [(hag2 s (hext1.1 s hs).1).2, (hext1.1 s hs).2]⟩,
      hpd2, hfg2⟩

/-- **Solo runs, multi-step.** A `StaleFree` promise-free solo run of a
bounded thread is matched by a solo run of the related target thread. The
foreign target messages are fixed before the run (`FgnSep` at the start); the
thread's own writes extend the map (`freshMap`). -/
theorem threadSF_sim {p r : Thread I × Memory} (h : ThreadSF A tid n L p r) :
    ∀ (ρ : TMap) (t' : Thread I) (mem' : Memory), ThreadRel ρ p.1 t' → MemRel ρ p.2 mem' →
      p.1.Bnd p.2.last → (∀ s ∈ p.1.prom, ρ.dom s) → (∀ s ≤ p.2.last, ρ.dom s) → n ≤ p.2.last →
      FgnSep ρ mem' n L →
      ∃ ρ' : TMap, ∃ r' : Thread I × Memory, ThreadNP A tid (t', mem') r' ∧
        ThreadRel ρ' r.1 r'.1 ∧ MemRel ρ' r.2 r'.2 ∧ (∀ s, ρ.dom s → ρ'.dom s ∧ ρ'.f s = ρ.f s) ∧
        (∀ s ∈ r.1.prom, ρ'.dom s) ∧ FgnSep ρ' r'.2 n L := by
  intro ρ t' mem' hT hm hb hpd hall hn hfg
  obtain ⟨ρ', r', h1, h2, h3, h4, h5, h6⟩ :=
    threadSFAt_sim A tid h.toAt ρ t' mem' hT hm hb hpd hall (fun m hm => hm ▸ hn) hfg.toAt
  exact ⟨ρ', r', h1, h2, h3, h4, h5, h6.toSep⟩

/-! ### Interleaved foreign appends: the step-by-step form

When other threads append to the target memory *between* the replayed steps,
the replay is a game: the source thread steps (`SimState.step`), or another
thread appends a message to a watched location (`SimState.appendForeign`).
`SimState ρ N L p q` relates the source thread and memory `p` to the target
`q`; each foreign append adds the current source memory size to the set of
thresholds `N`, and each source step must be `StaleFree` at every threshold
in force. -/

/-- The thread-level simulation state, foreign messages separated at a set of
thresholds: what `stepOne_simAt` needs and re-establishes. -/
structure SimState (ρ : TMap) (N : Nat → Prop) (L : Loc → Prop) (p q : Thread I × Memory) : Prop where
  thread : ThreadRel ρ p.1 q.1
  mem : MemRel ρ p.2 q.2
  bnd : p.1.Bnd p.2.last
  promDom : ∀ s ∈ p.1.prom, ρ.dom s
  domAll : ∀ s ≤ p.2.last, ρ.dom s
  nle : ∀ n, N n → n ≤ p.2.last
  fgn : FgnSepAt ρ q.2 N L

/-- **Foreign append.** Another thread appends `w`, to a watched location, to
the target memory: the state survives, with the current source memory size as
a new threshold. -/
theorem SimState.appendForeign {ρ : TMap} {p : Thread I × Memory} {t' : Thread I} {M' : Memory}
    (h : SimState ρ N L p (t', M')) {w : Msg} (hw : L w.loc) :
    SimState ρ (fun n => N n ∨ n = p.2.last) L p (t', (M'.append w).1) :=
  ⟨h.thread, h.mem.appendForeign w, h.bnd, h.promDom, h.domAll,
    fun n hn => hn.elim (h.nle n) (fun e => e ▸ Nat.le_refl _), h.fgn.appendForeign h.mem hw⟩

/-- **Source step.** A source thread step whose event tree is `StaleFree` at
every threshold in force is matched by a target thread step; the state
survives for an extension of the map. -/
theorem SimState.step {ρ : TMap} {p p₁ q : Thread I × Memory} (h : SimState ρ N L p q)
    (hs : ThreadStep A tid p p₁)
    (hsf : ∀ tree, I.exec p.1.st = some tree → ∀ n, N n → StaleFree A tid (instrViews p.1 (I.deps p.1.st)) n L
      { views := p.1.views, prom := p.1.prom, mem := p.2, log := [.instr tid (I.showInstr p.1.st)] } tree) :
    ∃ ρ' : TMap, ∃ q₁, ThreadStep A tid q q₁ ∧ SimState ρ' N L p₁ q₁ ∧ Ext ρ ρ' p.2.last := by
  obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
  obtain ⟨ρ1, outs', o', hstep', ho', hT1, hm1, hext1, hpd1, hall1, hn1, hfg1, hb1⟩ :=
    stepOne_simAt A tid h.thread h.mem h.bnd h.promDom h.domAll h.nle h.fgn hsf hstep ho
  exact ⟨ρ1, (o'.thread, o'.mem), ⟨outs', o', hstep', ho', rfl⟩, ⟨hT1, hm1, hb1, hpd1, hall1, hn1, hfg1⟩, hext1⟩

/-- More thresholds (still below the source memory size) and more watched
locations only weaken the state. -/
theorem SimState.mono {ρ : TMap} {p q : Thread I × Memory} {N' : Nat → Prop} {L' : Loc → Prop}
    (h : SimState ρ N L p q) (hN : ∀ n, N n → N' n) (hN' : ∀ n, N' n → n ≤ p.2.last) (hL : ∀ l, L l → L' l) :
    SimState ρ N' L' p q :=
  ⟨h.thread, h.mem, h.bnd, h.promDom, h.domAll, hN', h.fgn.mono hN hL⟩

end ThreadLevel


end Sim

end Kraken.Promising
