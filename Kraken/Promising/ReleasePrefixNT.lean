/-
(S2′) and (S1′) with pending non-temporal stores: the release-prefix facts of
`Kraken/Promising/ReleasePrefix.lean` for every program, x86 `movnti`
included, with no `Thread.NoNTStores`/`Thread.NextNoNT` hypothesis.

A non-temporal store raises `vwOldNT`, which a later release store's
pre-view does not include (SDM: an ordinary store may overtake an older
`movnti`). So while a release promise `ts ≤ |M|` is outstanding, its thread
may still append non-temporal messages above `|M|`, and may read them back by
store forwarding. Everything else is as in the restricted case: the
release-bounded thread reads below `ts` and its ordinary writes fulfil
promises at or below `|M|`.

- `Config.Bnd`: every view, register, forwarding and load-exclusive value of
  every thread is at most `|M|`; holds in every reachable configuration
  (`Config.Bnd.reachable`, `Config.init_bnd`).
- (S2′) `stutterStepNT_path`, `stutterStepNT_release`: a step of the thread
  while `ts` is outstanding extends memory only by its own messages, each at
  most its `vwOldNT` (non-temporal), keeps `vwOld < ts`, and reads below `ts`
  or at most `vwOldNT`. With a release at the end of the path, also
  `vwNew < ts` (`EvTree.RelFulfils.vwNew_lt`): no `sfence`/`mfence`/locked
  instruction occurs in the window (it would fold `vwOldNT ≥ |M| + 1` into
  `vwNew`), so pending non-temporal stores stay pending.
- (S1′) `Config.advanceableNT_of_path`: `Config.AdvanceableNT`, i.e.
  `Config.Advanceable` except that the thread's promise-free run may append
  its own messages above `|c.mem|`, and the release fulfilment is against the
  run's final memory. Proof by a *clamped* simulation (`Thread.Sim`,
  `Ctx.Sim`): along the path the thread's own instructions are replayed
  against `c.mem` extended by the replay's own fresh writes; views agree up to
  clamping at `|c.mem| + 1` (`VR`, `Views.Rel`); a non-temporal write above
  `|c.mem|` is replayed as a fresh write at the end of the replay memory
  (`write_fresh_sim`), and a read of one is forwarded in both runs (`NtCoh`).
  `readSuccs_sim`/`writeSuccs_sim` → `runTree_sim` → `stepOne_sim` →
  `advanceNT_path`; the fulfilment by `EvTree.RelFulfils.sim`. Needs
  `c0.Bnd` besides `c0.Wf`.
- Virtual configurations: `Config.VirtualOfNT` (each advanced thread against
  its own run memory, `v.mem` one of them), `Config.AdvanceableNT.virtualOfNT`,
  `Config.VirtualOf.toNT`, `Config.VirtualOfNT.toVirtualOf`, and the
  `VirtualRel` instance `VirtualRel.nt` (`refl`, `eq_of_final`).

The restricted theorems of `ReleasePrefix.lean` (`Config.advanceable_of_path`
with `Thread.NoNTStores`/`Thread.NextNoNT`) are the special case where the run
appends nothing (`Config.Advanceable.advanceableNT`).
-/
import Kraken.Promising.ReleasePrefix

namespace Kraken.Promising

open Kraken.Promising.Live.Bridge

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

private theorem ite_none_left_nt {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rwa [ite_eq_right hp] at h

private theorem ite_none_right_nt {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then y else none) = some x) : y = some x := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

private theorem mem_ite_nil_nt {α : Type} {p : Prop} [Decidable p] {ys : List α} {x : α}
    (h : x ∈ (if p then ys else [])) : x ∈ ys := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

private theorem mem_ite_nil_iff_nt {α : Type} {p : Prop} [Decidable p] {ys : List α} {x : α} :
    x ∈ (if p then ys else []) ↔ p ∧ x ∈ ys := by
  by_cases hp : p
  · rw [ite_eq_left hp]; exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩
  · rw [ite_eq_right hp]; exact ⟨fun h => absurd h List.not_mem_nil, fun h => absurd h.1 hp⟩

/-! ## Bounded views: every value a thread holds is at most `|M|` -/

theorem Views.Le.mono {vs : Views} {n n' : Nat} (h : vs.Le n) (hn : n ≤ n') : vs.Le n' :=
  ⟨fun l => Nat.le_trans (h.coh l) hn, Nat.le_trans h.vrNew hn, Nat.le_trans h.vrOld hn,
   Nat.le_trans h.vrOldNR hn, Nat.le_trans h.vwNew hn, Nat.le_trans h.vwOld hn, Nat.le_trans h.vCAP hn,
   Nat.le_trans h.vRel hn, fun l f hf => Nat.le_trans (h.fwd l f hf) hn, Nat.le_trans h.vwOldNT hn⟩

/-- Every value of `vs` is at most `n`: `Views.Le` together with the
forwarding timestamps and the pending load exclusive. -/
structure Views.Bnd (vs : Views) (n : Nat) : Prop where
  le : vs.Le n
  fwdTime : ∀ l f, vs.getFwd l = some f → f.time ≤ n
  xclb : ∀ t ν l, vs.xclb = some (t, ν, l) → t ≤ n ∧ ν ≤ n

theorem Views.Bnd.mono {vs : Views} {n n' : Nat} (h : vs.Bnd n) (hn : n ≤ n') : vs.Bnd n' :=
  ⟨h.le.mono hn, fun l f hf => Nat.le_trans (h.fwdTime l f hf) hn,
   fun t ν l hx => ⟨Nat.le_trans (h.xclb t ν l hx).1 hn, Nat.le_trans (h.xclb t ν l hx).2 hn⟩⟩

/-- The view of the pending load exclusive (`0` if none) is at most `n`. -/
theorem Views.Bnd.xclRead {vs : Views} {n : Nat} (h : vs.Bnd n) : (vs.xclb.map (·.2.1)).getD 0 ≤ n := by
  rcases e : vs.xclb with _ | ⟨t, ν, l⟩
  · exact Nat.zero_le _
  · exact (h.xclb t ν l e).2

/-- A thread whose views and register views are at most `n`. -/
structure Thread.Bnd (t : Thread I) (n : Nat) : Prop where
  views : t.views.Bnd n
  regs : t.RegsLe n

theorem Thread.Bnd.mono {t : Thread I} {n n' : Nat} (h : t.Bnd n) (hn : n ≤ n') : t.Bnd n' :=
  ⟨h.views.mono hn, h.regs.mono hn⟩

/-- An instruction's context with every value at most its memory's `|M|`. -/
structure Ctx.Bnd (c : Ctx) : Prop where
  views : c.views.Bnd c.mem.last
  loadViews : ∀ ν ∈ c.loadViews, ν ≤ c.mem.last
  succView : c.succView ≤ c.mem.last

theorem Ctx.Bnd.grow {c c0 : Ctx} (hc : c.Bnd) (hv : c0.views = c.views) (hl : c0.loadViews = c.loadViews)
    (hs : c0.succView = c.succView) (hm : c.mem.last ≤ c0.mem.last) : c0.Bnd :=
  ⟨hv ▸ hc.views.mono hm, fun ν hν => Nat.le_trans (hc.loadViews ν (hl ▸ hν)) hm, hs ▸ Nat.le_trans hc.succView hm⟩

theorem Views.Bnd.read {vs : Views} {n : Nat} (hs : vs.Bnd n) {l : Loc} {νpost a : View}
    {acq xcl noRet : Bool} {t : Time} (hν : νpost ≤ n) (ha : a ≤ n) (ht : t ≤ n) :
    Views.Bnd
      { (vs.setCoh l νpost) with
        vrOld := if noRet then vs.vrOld else max vs.vrOld νpost
        vrOldNR := if noRet then max vs.vrOldNR νpost else vs.vrOldNR
        vrNew := if acq then max vs.vrNew νpost else vs.vrNew
        vwNew := if acq then max vs.vwNew νpost else vs.vwNew
        vCAP := max vs.vCAP a
        xclb := if xcl then some (t, νpost, l) else vs.xclb } n := by
  have hle := hs.le
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hle.vwOld, ?_, hle.vRel, hle.fwd, hle.vwOldNT⟩, hs.fwdTime, ?_⟩
  · intro l'
    show (vs.setCoh l νpost).getCoh l' ≤ n
    rw [Views.getCoh_setCoh]
    have := hle.coh l; have := hle.coh l'
    split <;> omega_t
  · show (if acq = true then max vs.vrNew νpost else vs.vrNew) ≤ n
    have := hle.vrNew; split <;> omega_t
  · show (if noRet = true then vs.vrOld else max vs.vrOld νpost) ≤ n
    have := hle.vrOld; split <;> omega_t
  · show (if noRet = true then max vs.vrOldNR νpost else vs.vrOldNR) ≤ n
    have := hle.vrOldNR; split <;> omega_t
  · show (if acq = true then max vs.vwNew νpost else vs.vwNew) ≤ n
    have := hle.vwNew; split <;> omega_t
  · show max vs.vCAP a ≤ n
    have := hle.vCAP; omega_t
  · intro t' ν' l' h
    have h' : (if xcl = true then some (t, νpost, l) else vs.xclb) = some (t', ν', l') := h
    split at h'
    · simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      exact ⟨ht, hν⟩
    · exact hs.xclb t' ν' l' h'

theorem Views.Bnd.setNew {vs : Views} {n : Nat} (hs : vs.Bnd n) {r w : View} (hr : r ≤ n) (hw : w ≤ n) :
    ({ vs with vrNew := r, vwNew := w } : Views).Bnd n :=
  ⟨⟨hs.le.coh, hr, hs.le.vrOld, hs.le.vrOldNR, hw, hs.le.vwOld, hs.le.vCAP, hs.le.vRel, hs.le.fwd, hs.le.vwOldNT⟩,
   hs.fwdTime, hs.xclb⟩

theorem Views.Bnd.setVCAP {vs : Views} {n : Nat} (hs : vs.Bnd n) {x : View} (hx : x ≤ n) :
    ({ vs with vCAP := x } : Views).Bnd n :=
  ⟨⟨hs.le.coh, hs.le.vrNew, hs.le.vrOld, hs.le.vrOldNR, hs.le.vwNew, hs.le.vwOld, hx, hs.le.vRel, hs.le.fwd,
    hs.le.vwOldNT⟩, hs.fwdTime, hs.xclb⟩

theorem Views.Bnd.xclbNone {vs : Views} {n : Nat} (hs : vs.Bnd n) : ({ vs with xclb := none } : Views).Bnd n :=
  ⟨hs.le.xclb none, hs.fwdTime, fun _ _ _ h => by cases h⟩

private theorem getLastD_le {xs : List View} {n : Nat} (h : ∀ ν ∈ xs, ν ≤ n) :
    ∀ d, d ≤ n → xs.getLastD d ≤ n := by
  induction xs with
  | nil => intro d hd; exact hd
  | cons a l ih =>
    intro d _
    rw [List.getLastD_cons]
    exact ih (fun ν hν => h ν (List.mem_cons_of_mem _ hν)) a (h a List.mem_cons_self)

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_bnd {c : Ctx} (hc : c.Bnd) (hiv : iv.Le c.mem.last) {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    x.2.2.Bnd ∧ x.1 ≤ c.mem.last ∧ x.2.2.mem = c.mem := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, htr, ht⟩ := hx
  have htle : t ≤ c.mem.last := Nat.le_of_lt_succ (List.mem_range.mp htr)
  split at ht
  · cases ht
  · have h := ite_none_left_nt ht
    simp only [Option.some.injEq] at h
    subst h
    have hif : (if (A.loadKind k == LoadKind.acq) = true then c.views.vRel else 0) ≤ c.mem.last := by
      split
      · exact hc.views.le.vRel
      · exact Nat.zero_le _
    have hrv := readView_le A (k := A.loadKind k) (f := c.views.getFwd l) (hc.views.le.fwd l) htle
    have haddrR := hiv.addrR
    have hvrNew := hc.views.le.vrNew
    refine ⟨⟨Views.Bnd.read hc.views (by omega_t) hiv.addrW htle, ?_, hc.succView⟩, htle, rfl⟩
    intro ν hν
    rcases List.mem_append.mp hν with h | h
    · exact hc.loadViews ν h
    · rw [List.mem_singleton] at h; subst h; omega_t

theorem afterWrite_bnd {xr : View} {c : Ctx} (hc : c.Bnd) (hiv : iv.Le c.mem.last) {k : StoreKind} {xcl : Bool} {l : Loc}
    {v : Val} {t : Time} {νfwd : View} {ful : Bool} (ht : t ≤ c.mem.last) (hν : νfwd ≤ c.mem.last) :
    (afterWrite A iv c k xcl l v t νfwd ful xr).Bnd := by
  have hle := hc.views.le
  refine ⟨⟨⟨?_, hle.vrNew, hle.vrOld, hle.vrOldNR, hle.vwNew, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, hc.loadViews, ?_⟩
  · intro l'
    show (c.views.setCoh l t).getCoh l' ≤ c.mem.last
    rw [Views.getCoh_setCoh]; have := hle.coh l; have := hle.coh l'; split <;> omega_t
  · show (if (k == StoreKind.nt) = true then c.views.vwOld else max c.views.vwOld t) ≤ c.mem.last
    have := hle.vwOld; split <;> omega_t
  · show max c.views.vCAP iv.addrW ≤ c.mem.last
    have := hle.vCAP; have := hiv.addrW; omega_t
  · show (if (k == StoreKind.rel) = true then max c.views.vRel t else c.views.vRel) ≤ c.mem.last
    have := hle.vRel; split <;> omega_t
  · intro l' f hf
    have hf' : (c.views.setFwd l { time := t, view := νfwd, xcl, xclRead := xr }).getFwd l' = some f := hf
    rw [Views.getFwd_setFwd] at hf'
    split at hf'
    · cases hf'; exact hν
    · exact hle.fwd l' f hf'
  · show (if (k == StoreKind.nt) = true then max c.views.vwOldNT t else c.views.vwOldNT) ≤ c.mem.last
    have := hle.vwOldNT; split <;> omega_t
  · intro l' f hf
    have hf' : (c.views.setFwd l { time := t, view := νfwd, xcl, xclRead := xr }).getFwd l' = some f := hf
    rw [Views.getFwd_setFwd] at hf'
    split at hf'
    · cases hf'; exact ht
    · exact hc.views.fwdTime l' f hf'
  · intro t0 ν l0 h
    have h' : (if xcl = true then none else c.views.xclb) = some (t0, ν, l0) := h
    split at h'
    · cases h'
    · exact hc.views.xclb t0 ν l0 h'
  · show (if A.succViewBot = true then 0 else t) ≤ c.mem.last
    split <;> omega_t

theorem writeSuccs_bnd {xr : View} {c : Ctx} (hc : c.Bnd) (hiv : iv.Le c.mem.last) {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (hextra : extra ≤ c.mem.last) {c' : Ctx}
    (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : c'.Bnd ∧ c.mem.last ≤ c'.mem.last := by
  have hν : max iv.addrR (max iv.dataR extra) ≤ c.mem.last := by
    have := hiv.addrR; have := hiv.dataR; omega_t
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · rename_i w hw
      have h := ite_none_right_nt h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨afterWrite_bnd A iv hc hiv (c.mem.last_le_of_get?_eq_some hw) hν, Nat.le_refl _⟩
    · cases h
  · split at h
    rename_i _ mem' t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨-, rfl⟩ := h
    have ht : t = c.mem.last + 1 := (congrArg Prod.snd hok).symm
    have hm : mem' = (c.mem.append { loc := l, val := v, tid }).1 := (congrArg Prod.fst hok).symm
    have hl : mem'.last = c.mem.last + 1 := hm ▸ Memory.last_append _ _
    have hle : c.mem.last ≤ mem'.last := by rw [hl]; omega_t
    have hc0 : ∀ pn, Ctx.Bnd { c with mem := mem', prom := c.prom ++ [t], promisedNow := pn } :=
      fun _ => hc.grow rfl rfl rfl hle
    exact ⟨afterWrite_bnd A iv (hc0 _) (hiv.mono hle) (by show t ≤ mem'.last; omega_t) (Nat.le_trans hν hle), hle⟩

theorem fenceStep_bnd {c : Ctx} (hc : c.Bnd) (k : FenceKind) : (fenceStep c k).Bnd := by
  have hle := hc.views.le
  have h1 := hle.vrNew; have h2 := hle.vwNew; have h3 := hle.vrOld; have h4 := hle.vwOld; have h5 := hle.vCAP
  have h6 := hle.vrOldNR; have h7 := hle.vwOldNT
  cases k
  all_goals
    simp only [fenceStep]
    exact ⟨Views.Bnd.setNew hc.views (by omega_t) (by omega_t), hc.loadViews, hc.succView⟩

theorem fenceOpt_bnd {c : Ctx} (hc : c.Bnd) (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).Bnd ∧ (if b then fenceStep c k else c).mem = c.mem := by
  cases b
  · exact ⟨hc, rfl⟩
  · exact ⟨fenceStep_bnd hc k, fenceStep_mem c k⟩

theorem rmwPost_bnd {c : Ctx} (hc : c.Bnd) (k : RmwKind) (noRet : Bool) (l : Loc) :
    (rmwPost A k noRet l c).Bnd ∧ (rmwPost A k noRet l c).mem = c.mem := by
  have hle := hc.views.le
  have h1 := hle.vrNew; have h2 := hle.vwNew; have h3 := hle.coh l
  unfold rmwPost
  split
  · exact ⟨⟨Views.Bnd.setNew hc.views (by omega_t) (by omega_t), hc.loadViews, hc.succView⟩, rfl⟩
  · exact ⟨⟨hc.views, hc.loadViews, hc.succView⟩, rfl⟩

theorem runTree_bnd {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), c.Bnd → iv.Le c.mem.last → .ok (s, c') ∈ runTree A tid iv c tree →
      c'.Bnd ∧ c.mem.last ≤ c'.mem.last := by
  induction tree with
  | done s0 =>
    intro c s c' hc _ h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hc, Nat.le_refl _⟩
  | fault msg =>
    intro c s c' _ _ h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' hc hiv h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hc hiv hi
  | load k xcl l ret ih =>
    intro c s c' hc hiv h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    have hr := readSuccs_bnd A iv hc hiv h0
    have hm0 : c0.mem = c.mem := hr.2.2
    obtain ⟨hb, hl⟩ := ih v c0 s c' hr.1 (hm0 ▸ hiv) h
    exact ⟨hb, hm0 ▸ hl⟩
  | store k xcl l v ret ih =>
    intro c s c' hc hiv h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      obtain ⟨hb0, hl0⟩ := writeSuccs_bnd A tid _ hc (hiv.forStore c.stores) (Nat.zero_le _) hc0
      obtain ⟨hb, hl⟩ := ih true c0 s c' hb0 (hiv.mono hl0) h
      exact ⟨hb, Nat.le_trans hl0 hl⟩
    · rw [List.mem_ite_nil_right] at h
      have h0 : Ctx.Bnd
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        ⟨hc.views.xclbNone, hc.loadViews, Nat.zero_le _⟩
      have := ih false _ s c' h0 (by exact hiv) h.2
      exact this
  | fence k ret ih =>
    intro c s c' hc hiv h
    simp only [runTree] at h
    have hm := fenceStep_mem c k
    obtain ⟨hb, hl⟩ := ih () _ s c' (fenceStep_bnd hc k) (hm ▸ hiv) h
    exact ⟨hb, hm ▸ hl⟩
  | rmw k noRet l op ret ih =>
    intro c s c' hc hiv h
    simp only [runTree] at h
    obtain ⟨hb1, hm1⟩ := fenceOpt_bnd hc A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h hb1 hm1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have hr := readSuccs_bnd A iv hb1 (hm1 ▸ hiv) h2
    have hb2 : c2.Bnd := hr.1
    have hm2 : c2.mem = c.mem := hr.2.2.trans hm1
    simp only at h
    split at h
    · obtain ⟨hb3, hm3⟩ := fenceOpt_bnd hb2 A.rmwFence .sy
      obtain ⟨hb, hl⟩ := ih old _ s c' hb3 (by rw [hm3, hm2]; exact hiv) h
      rw [hm3, hm2] at hl
      exact ⟨hb, hl⟩
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      obtain ⟨hb3, hl3⟩ := writeSuccs_bnd A tid iv hb2 (hm2 ▸ hiv) (getLastD_le hb2.loadViews 0 (Nat.zero_le _)) hc3
      obtain ⟨hb4, hm4⟩ := rmwPost_bnd A hb3 k noRet l
      obtain ⟨hb5, hm5⟩ := fenceOpt_bnd hb4 A.rmwFence .sy
      have hl35 : c.mem.last ≤ (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy
          else rmwPost A k noRet l c3).mem.last := by rw [hm5, hm4, ← hm2]; exact hl3
      obtain ⟨hb, hl⟩ := ih old _ s c' hb5 (hiv.mono hl35) h
      exact ⟨hb, Nat.le_trans hl35 hl⟩

end Rules

private theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (xs : List α) (b : β), P b → (∀ b x, x ∈ xs → P b → P (f b x)) → P (xs.foldl f b)
  | [], _, hb, _ => hb
  | x :: xs, b, hb, hf =>
    foldl_inv P f xs (f b x) (hf b x List.mem_cons_self hb)
      (fun b' x' hx' => hf b' x' (List.mem_cons_of_mem _ hx'))

private theorem foldl_max_le {xs : List View} {n : Nat} (h : ∀ ν ∈ xs, ν ≤ n) :
    ∀ acc, acc ≤ n → xs.foldl max acc ≤ n := by
  induction xs with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc hacc
    rw [List.foldl_cons]
    have := h x List.mem_cons_self
    exact ih (fun ν hν => h ν (List.mem_cons_of_mem _ hν)) _ (by omega_t)

/-- `finishInstr` keeps every value of the thread at most `n` when the
context's and the instruction's are. -/
theorem finishInstr_bnd {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {n : Nat} (hv : c.views.Bnd n) (hlv : ∀ ν ∈ c.loadViews, ν ≤ n) (hsv : c.succView ≤ n) (hiv : iv.Le n)
    (hregs : t.RegsLe n) : ∀ th ∈ finishInstr t d iv st c, th.Bnd n := by
  intro th hth
  have hload : c.loadViews.foldl max 0 ≤ n := foldl_max_le hlv 0 (Nat.zero_le _)
  let P : Thread I → Prop := fun t => t.views = c.views ∧ t.RegsLe n
  have hstep : ∀ (t : Thread I) (r : I.RegId) (rv wv : View), P t → rv ≤ n → wv ≤ n → P (t.setRegView r rv wv) :=
    fun t r _ _ hp hr hw => ⟨hp.1, hp.2.setRegView r hr hw⟩
  let t1 : Thread I := { t with st, views := c.views, prom := c.prom }
  have h1 : P t1 := ⟨rfl, hregs⟩
  have hinR : (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW) ≤ n := by
    have := hiv.addrR; have := hiv.dataR; have := hiv.condW; split <;> omega_t
  have hinW : max (max iv.addrW iv.dataW) iv.condW ≤ n := by
    have := hiv.addrW; have := hiv.dataW; have := hiv.condW; omega_t
  have h2 : P ((d.statusDefs.foldl (fun t r => t.setRegView r c.succView c.succView)
        (d.defs.foldl (fun t r => t.setRegView r
          (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW)
          (max (max iv.addrW iv.dataW) iv.condW)) t1))) := by
    apply foldl_inv P
    · apply foldl_inv P _ _ _ h1
      intro b x _ hb
      exact hstep b x _ _ hb hinR hinW
    · intro b x _ hb
      exact hstep b x _ _ hb hsv hsv
  have finish : ∀ t2 : Thread I, P t2 →
      ∀ th, th = (if d.isBranch then { t2 with views := { t2.views with vCAP := max t2.views.vCAP iv.condW } } else t2) →
      th.Bnd n := by
    intro t2 ⟨hviews, hregs⟩ th hth
    subst hth
    split
    · refine ⟨?_, hregs⟩
      show ({ t2.views with vCAP := max t2.views.vCAP iv.condW } : Views).Bnd n
      rw [hviews]
      have := hiv.condW; have := hv.le.vCAP
      exact hv.setVCAP (by omega_t)
    · exact ⟨hviews ▸ hv, hregs⟩
  have h3 : ∀ t2 : Thread I, P t2 → P
      (if d.loadDefs.length == c.loadViews.length then
        (d.loadDefs.zip c.loadViews).foldl (fun t (r, v) => t.setRegView r v v) t2
      else d.loadDefs.foldl (fun t r => t.setRegView r (c.loadViews.foldl max 0) (c.loadViews.foldl max 0)) t2) := by
    intro t2 h2
    split
    · apply foldl_inv P _ _ _ h2
      intro b x hx hb
      obtain ⟨r, v⟩ := x
      have hv' : v ≤ n := hlv v (List.of_mem_zip hx).2
      exact hstep b r v v hb hv' hv'
    · apply foldl_inv P _ _ _ h2
      intro b x _ hb
      exact hstep b x _ _ hb hload hload
  simp only [finishInstr] at hth
  split at hth
  · rw [List.mem_cons, List.mem_singleton] at hth
    rcases hth with rfl | rfl
    · refine finish _ ?_ _ rfl
      apply foldl_inv P _ _ _ h2
      intro b x _ hb
      have := b.rviewOf_le hb.2 x; have := b.wviewOf_le hb.2 x
      exact hstep b x _ _ hb (by omega_t) (by omega_t)
    · exact finish _ (h3 _ h2) _ rfl
  · rw [List.mem_singleton] at hth
    subst hth
    exact finish _ (h3 _ h2) _ rfl

/-- One instruction keeps a thread's values at most `|M|`. -/
theorem stepOne_bnd (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (ht : t.Bnd mem.last) : o.thread.Bnd o.mem.last ∧ mem.last ≤ o.mem.last := by
  unfold stepOne at hstep
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
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hc : Ctx.Bnd { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } :=
        ⟨ht.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
      have hiv := instrViews_le ht.regs (I.deps t.st)
      obtain ⟨hc', hl⟩ := runTree_bnd A tid _ tree _ st c' hc hiv hr
      exact ⟨finishInstr_bnd hc'.views hc'.loadViews hc'.succView (hiv.mono hl) (ht.regs.mono hl) th hth, hl⟩

/-- Every thread's values are at most `|M|`. Holds initially
(`Config.init_bnd`) and in every reachable configuration
(`Config.Bnd.reachable`). -/
def Config.Bnd (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → t.Bnd c.mem.last

theorem Config.init_bnd (states : List I.State) (initMem : List (Loc × Val)) :
    (Config.init states initMem : Config I).Bnd := by
  intro i t h
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨st, -, rfl⟩ := h
  refine ⟨⟨⟨fun l => by simp [Thread.init, Views.getCoh], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun l f hf => by simp [Thread.init, Views.getFwd] at hf,
    Nat.zero_le _⟩, fun l f hf => by simp [Thread.init, Views.getFwd] at hf, fun _ _ _ h => by simp [Thread.init] at h⟩,
    fun v hv => ?_, fun v hv => ?_⟩
  · simp only [Thread.init, Array.mem_replicate] at hv; omega_t
  · simp only [Thread.init, Array.mem_replicate] at hv; omega_t

/-- A `SuccKind` step keeps `Config.Bnd` (the `ReachableK` twin of `Config.Bnd.succ`). -/
theorem Config.Bnd.succK {A : Arch} {c c' : Config I} (hb : c.Bnd)
    (h : SuccKind A c c') : c'.Bnd := by
  cases h with
  | @instr j tj outs o hj hstep ho =>
    obtain ⟨hb', hl⟩ := stepOne_bnd A hstep ho (hb j tj hj)
    intro i t' h'
    rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at h'
    split at h'
    · cases h'; exact hb'
    · exact (hb i t' h').mono hl
  | @promise j tj p hj _ =>
    have hl : c.mem.last ≤ (c.mem.append { p.1 with tid := j }).1.last := by
      rw [Memory.last_append]; omega_t
    intro i t' h'
    rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at h'
    split at h'
    · cases h'; exact ⟨(hb j tj hj).views.mono hl, (hb j tj hj).regs.mono hl⟩
    · exact (hb i t' h').mono hl

theorem Config.Bnd.succ {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I} (hb : c.Bnd)
    (h : c' ∈ (succs A c fuel).1) : c'.Bnd :=
  hb.succK (succs_cases h)

/-- **Every reachable configuration is bounded** (from a bounded one, e.g.
`Config.init`). -/
theorem Config.Bnd.reachable {A : Arch} {c c' : Config I} (hb : c.Bnd)
    (h : ReachableK A c c') : c'.Bnd := by
  induction h with
  | refl => exact hb
  | step hs _ ih => exact ih (hb.succK hs)

/-! ## (S2′): a step inside the release window -/

/-- Every message of `c`'s memory above `m` is by `tid` and at most one of its
writes (`vwAll`). -/
def Ctx.OwnAbove (tid m : Nat) (c : Ctx) : Prop :=
  ∀ t w, m < t → c.mem.get? t = some w → w.tid = tid ∧ t ≤ c.views.vwAll

theorem Ctx.OwnAbove.of_le {tid m : Nat} {c c' : Ctx} (h : c.OwnAbove tid m) (hm : c'.mem = c.mem)
    (hv : c.views.vwAll ≤ c'.views.vwAll) : c'.OwnAbove tid m := by
  intro t w ht hw
  rw [hm] at hw
  obtain ⟨h1, h2⟩ := h t w ht hw
  exact ⟨h1, Nat.le_trans h2 hv⟩

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem afterWrite_vwAll {xr : View} (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time) (νfwd : View)
    (ful : Bool) : max c.views.vwAll t ≤ (afterWrite A iv c k xcl l v t νfwd ful xr).views.vwAll := by
  simp only [afterWrite, Views.setCoh, Views.vwAll]
  split <;> omega_t

theorem writeSuccs_own {xr : View} {m : Nat} {c : Ctx} (h : c.OwnAbove tid m) {k : StoreKind} {xcl : Bool} {l : Loc}
    {v : Val} {tr : Option Time} {extra : View} {c' : Ctx} (hc : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) :
    c'.OwnAbove tid m := by
  unfold writeSuccs at hc
  rw [List.mem_append, List.mem_filterMap] at hc
  rcases hc with ⟨t, -, hc⟩ | hc
  · split at hc
    · have hc := ite_none_right_nt hc
      simp only [Option.some.injEq] at hc
      subst hc
      have := afterWrite_vwAll (xr := xr) A iv c (A.storeKind k) xcl l v t (max iv.addrR (max iv.dataR extra)) true
      exact h.of_le rfl (by omega_t)
    · cases hc
  · split at hc
    rename_i _ mem' t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at hc
    obtain ⟨-, rfl⟩ := hc
    have ht : t = c.mem.last + 1 := (congrArg Prod.snd hok).symm
    have hm : mem' = (c.mem.append { loc := l, val := v, tid }).1 := (congrArg Prod.fst hok).symm
    have key : ∀ (c0 : Ctx), c0.views = c.views → c0.mem = mem' → ∀ (k' : StoreKind) (xcl' : Bool) (νfwd : View)
        (ful : Bool), (afterWrite A iv c0 k' xcl' l v t νfwd ful xr).OwnAbove tid m := by
      intro c0 hv hm0 k' xcl' νfwd ful t' w ht' hw
      have hall := afterWrite_vwAll (xr := xr) A iv c0 k' xcl' l v t νfwd ful
      rw [hv] at hall
      change c0.mem.get? t' = some w at hw
      rw [hm0, hm] at hw
      rcases Memory.get?_append_eq_some _ _ hw with ⟨_, hw'⟩ | ⟨rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := h t' w ht' hw'
        exact ⟨h1, by omega_t⟩
      · exact ⟨rfl, by omega_t⟩
    apply key <;> rfl

theorem runTree_own {σ : Type} {m : Nat} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), c.OwnAbove tid m → .ok (s, c') ∈ runTree A tid iv c tree → c'.OwnAbove tid m := by
  induction tree with
  | done s0 =>
    intro c s c' hc h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hc
  | fault msg =>
    intro c s c' _ h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' hc h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hc hi
  | load k xcl l ret ih =>
    intro c s c' hc h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    have hv : c0.views.vwAll = c.views.vwAll := by
      have := readSuccs_vwOldNT A iv h0
      unfold readSuccs at h0
      rw [List.mem_filterMap] at h0
      obtain ⟨t', -, ht'⟩ := h0
      split at ht'
      · cases ht'
      · have h' := ite_none_left_nt ht'
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨-, -, rfl⟩ := h'
        rfl
    exact ih v c0 s c' (hc.of_le (readSuccs_mp A iv h0).1 (Nat.le_of_eq hv.symm)) h
  | store k xcl l v ret ih =>
    intro c s c' hc h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact ih true c0 s c' (writeSuccs_own A tid _ hc hc0) h
    · rw [List.mem_ite_nil_right] at h
      refine ih false _ s c' ?_ h.2
      exact hc.of_le rfl (Nat.le_refl _)
  | fence k ret ih =>
    intro c s c' hc h
    simp only [runTree] at h
    obtain ⟨-, -, h3, -, -, -, h7⟩ := fenceStep_fields c k
    exact ih () _ s c' (hc.of_le (fenceStep_mem c k) (by simp only [Views.vwAll, h3, h7]; omega_t)) h
  | rmw k noRet l op ret ih =>
    intro c s c' hc h
    simp only [runTree] at h
    have hfo : ∀ (c : Ctx), c.OwnAbove tid m → (if A.rmwFence then fenceStep c .sy else c).OwnAbove tid m := by
      intro c hc
      generalize A.rmwFence = b
      cases b
      · exact hc
      · show (fenceStep c .sy).OwnAbove tid m
        obtain ⟨-, -, h3, -, -, -, h7⟩ := fenceStep_fields c .sy
        exact hc.of_le (fenceStep_mem c .sy) (by simp only [Views.vwAll, h3, h7]; omega_t)
    have h1 := hfo c hc
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have hv2 : c2.views.vwAll = c1.views.vwAll := by
      unfold readSuccs at h2
      rw [List.mem_filterMap] at h2
      obtain ⟨t', -, ht'⟩ := h2
      split at ht'
      · cases ht'
      · have h' := ite_none_left_nt ht'
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨-, -, rfl⟩ := h'
        rfl
    have hc2 : c2.OwnAbove tid m := h1.of_le (readSuccs_mp A iv h2).1 (Nat.le_of_eq hv2.symm)
    simp only at h
    split at h
    · exact ih old _ s c' (hfo c2 hc2) h
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      have hc3' := writeSuccs_own A tid iv hc2 hc3
      have hc4 : (rmwPost A k noRet l c3).OwnAbove tid m := by
        unfold rmwPost
        split
        · exact hc3'.of_le rfl (Nat.le_refl _)
        · exact hc3'.of_le rfl (Nat.le_refl _)
      exact ih old _ s c' (hfo _ hc4) h

end Rules

/-- One instruction appends only messages of its thread, each at most the
thread's new `vwAll`. -/
theorem stepOne_own (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    ∀ ts w, mem.last < ts → o.mem.get? ts = some w → w.tid = tid ∧ ts ≤ o.thread.views.vwAll := by
  unfold stepOne at hstep
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
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have h0 : Ctx.OwnAbove tid mem.last { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } :=
        fun ts w hts hw => absurd hw (by rw [Memory.get?_eq_none_of_last_lt _ hts]; simp)
      have hc' := runTree_own A tid _ tree _ st c' h0 hr
      obtain ⟨-, hv⟩ := finishInstr_relKey hth
      obtain ⟨-, hvw, -⟩ := Views.relPre_congr hv
      have hnt := Views.vwOldNT_congr hv
      have hall : th.views.vwAll = c'.views.vwAll := by simp only [Views.vwAll, hvw, hnt]
      intro ts w hts hw
      rw [hall]
      exact hc' ts w hts hw

/-- **(S2′) for one instruction outcome `o` from memory `mem`**, with
non-temporal stores: if the promise `ts` is still outstanding afterwards, the
step only extended memory, by messages of thread `tid` that are its
non-temporal writes (at most `vwOldNT`, above `|mem| ≥ ts`); its ordinary
writes stay below `ts`; and every read is below `ts` or at most `vwOldNT` (a
read at or above `ts` is forwarded from the thread's own non-temporal write).
With no non-temporal store this is `StutterStep` (`StutterStepNT.stutterStep`). -/
def StutterStepNT (ts : Time) (mem : Memory) (tid : Nat) (o : Outcome I) : Prop :=
  ts ∈ o.thread.prom → mem.Prefix o.mem ∧
    (∀ t w, mem.last < t → o.mem.get? t = some w → w.tid = tid ∧ t ≤ o.thread.views.vwOldNT) ∧
    o.thread.views.vwOld < ts ∧
    ∀ l t v ν, TraceEv.read l t v ν ∈ o.log → t < ts ∨ t ≤ o.thread.views.vwOldNT

/-- Without non-temporal stores (`vwOldNT < ts`, e.g. `0`) a `StutterStepNT`
from a memory containing `ts` is a `StutterStep`. -/
theorem StutterStepNT.stutterStep {ts : Time} {mem : Memory} {tid : Nat} {o : Outcome I}
    (h : StutterStepNT ts mem tid o) (hts : ts ≤ mem.last) (hnt : o.thread.views.vwOldNT < ts) :
    StutterStep ts mem o := by
  intro hin
  obtain ⟨hp, hown, -, hr⟩ := h hin
  refine ⟨?_, fun l t v ν hm => ?_⟩
  · obtain ⟨hi, rest, hrest⟩ := hp
    have hnil : rest = [] := by
      cases rest with
      | nil => rfl
      | cons w rest =>
        exfalso
        have hlen := congrArg List.length hrest
        simp only [List.length_append, List.length_cons, Array.length_toList] at hlen
        have hget : o.mem.get? (mem.last + 1) = some w := by
          have : o.mem.msgs[mem.msgs.size]? = some w := by
            rw [← Array.getElem?_toList, ← hrest]; simp
          simpa [Memory.get?, Memory.last] using this
        have := (hown _ w (by omega_t) hget).2
        omega_t
    subst hnil
    cases o with
    | mk th m pn lg =>
      cases m with
      | mk init msgs =>
        cases mem with
        | mk init' msgs' =>
          simp only [List.append_nil] at hrest
          simp only at hi hrest ⊢
          rw [hi, Array.toList_inj.mp hrest]
  · rcases hr l t v ν hm with h | h
    · exact h
    · omega_t

/-- **(S2′) on machine paths, for every program.** Let thread `tid` take an
instruction step `o` from a well-formed configuration `c` while its promise
`ts` is outstanding, and let the path continue, under any schedule, to a
configuration where the thread is release-bounded for `ts`. Then the step is
a `StutterStepNT`. No hypothesis on the program: non-temporal stores in the
window are allowed. -/
theorem stutterStepNT_path {A : Arch} {c c1 : Config I} (hwf : c.Wf)
    {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) {ts : Time} (hts : ts ∈ t.prom)
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid c.mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hr : ReachableK A (c.withThread tid o.thread o.mem) c1)
    {t1 : Thread I} (ht1 : c1.threads[tid]? = some t1) (hb : t1.views.relPre < ts) :
    StutterStepNT ts c.mem tid o := by
  intro _
  have h1 : (c.withThread tid o.thread o.mem).threads[tid]? = some o.thread := by
    simp only [Config.withThread_get? c _ _ (lt_size_of_get? ht), ↓reduceIte]
  obtain ⟨t', h', hle⟩ := hr.relPre_mono (hwf.instr ht hstep ho) h1
  rw [ht1] at h'; cases h'
  have hrel : o.thread.views.relPre < ts := Nat.lt_of_le_of_lt hle hb
  have htsM : ts ≤ c.mem.last := (hwf tid t ht).2 ts hts
  obtain ⟨-, -, -, -, hrd, -⟩ := stepOne_silent_nt A hstep ho (hwf tid t ht).1
  have hown := stepOne_own A hstep ho
  have hvw : o.thread.views.vwOld < ts := by
    simp only [Views.relPre] at hrel; omega_t
  refine ⟨Memory.Prefix.stepOne hstep ho, fun t w hlt hw => ?_, hvw, fun l tr v ν hm => ?_⟩
  · obtain ⟨h1, h2⟩ := hown t w hlt hw
    exact ⟨h1, by simp only [Views.vwAll] at h2; omega_t⟩
  · have := hrd l tr v ν hm
    simp only [Views.relPreNT] at this
    omega_t

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **No fence in the window**: the state before an instruction that fulfils
`ts` with a release store has `vwNew < ts` (every write's pre-view includes
`vwNew`, and `vwNew` only grows). A `sfence`, `mfence` or locked RMW folds
`vwOldNT` into `vwNew`, so none can follow a non-temporal store above `ts`
before the release; pending non-temporal stores stay pending. -/
theorem EvTree.RelFulfils.vwNew_lt {ts : Time} {σ : Type} (tree : EvTree σ) :
    ∀ c : Ctx, EvTree.RelFulfils A tid iv ts c tree → c.views.vwNew < ts := by
  induction tree with
  | done s => intro c h; exact h.elim
  | fault m => intro c h; exact h.elim
  | choose n k ih =>
    intro c ⟨i, h⟩
    exact ih i c h
  | load k xcl l ret ih =>
    intro c ⟨x, hx, h⟩
    exact Nat.lt_of_le_of_lt (readSuccs_word A iv hx).vwNew (ih x.2.1 x.2.2 h)
  | store k xcl l v ret ih =>
    intro c h
    rcases h with ⟨c', hc', h | h⟩ | h
    · exact (writeSuccs_word A tid _ hc').prom ts h.2.1 h.2.2
    · exact Nat.lt_of_le_of_lt (writeSuccs_word A tid _ hc').vwNew (ih true c' h)
    · have := ih false _ h
      exact this
  | fence k ret ih =>
    intro c h
    exact Nat.lt_of_le_of_lt (Ctx.WOrd.fenceStep c k).vwNew (ih () _ h)
  | rmw k noRet l op ret ih =>
    intro c ⟨x, hx, h⟩
    have h2 := (Ctx.WOrd.fenceOpt c A.rmwFence .sy).trans (readSuccs_word A iv hx)
    rcases h with h | ⟨new, -, c', hc', h | h⟩
    · exact Nat.lt_of_le_of_lt (h2.trans (Ctx.WOrd.fenceOpt _ A.rmwFence .sy)).vwNew (ih x.2.1 _ h)
    · exact Nat.lt_of_le_of_lt h2.vwNew ((writeSuccs_word A tid _ hc').prom ts h.2.1 h.2.2)
    · have h3 := (h2.trans (writeSuccs_word A tid _ hc')).trans
        ((Ctx.WOrd.rmwPost A c' k noRet l).trans (Ctx.WOrd.fenceOpt _ A.rmwFence .sy))
      exact Nat.lt_of_le_of_lt h3.vwNew (ih x.2.1 _ h)

end Rules

theorem Thread.RelFulfils.vwNew_lt {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory}
    (h : t.RelFulfils A tid ts mem) : t.views.vwNew < ts := by
  obtain ⟨tree, -, h⟩ := h
  exact EvTree.RelFulfils.vwNew_lt A tid _ tree _ h

/-- Along any `ReachableK` path a thread's `vwNew` only grows (the `ReachableK` twin
of `Reachable.vwNew_mono`). -/
theorem Live.Bridge.ReachableK.vwNew_mono {A : Arch} {c c' : Config I}
    (h : ReachableK A c c') (hwf : c.Wf) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) :
    ∃ t', c'.threads[tid]? = some t' ∧ t.views.vwNew ≤ t'.views.vwNew :=
  h.views_mono Views.vwNew (fun hstep ho _ => (stepOne_word _ hstep ho).1) hwf ht

/-- Along any machine path a thread's `vwNew` only grows. -/
theorem Reachable.vwNew_mono {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') (hwf : c.Wf) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) :
    ∃ t', c'.threads[tid]? = some t' ∧ t.views.vwNew ≤ t'.views.vwNew :=
  (ReachableK.of_reachable h).vwNew_mono hwf ht

/-- **(S2′) for release promises, for every program.** Every instruction step
thread `tid` takes from a reachable configuration while its promise `ts` is
outstanding, on any path along which the thread later reaches an instruction
that fulfils `ts` with a release store, is a `StutterStepNT`, and leaves
`vwNew < ts`: no fence orders the window's non-temporal stores (they stay
pending until after the release). -/
theorem stutterStepNT_release {A : Arch} {c0 c c1 : Config I} (h0 : c0.Wf)
    (hc : ReachableK A c0 c) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) {ts : Time}
    (hts : ts ∈ t.prom) {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid c.mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hr : ReachableK A (c.withThread tid o.thread o.mem) c1)
    {t1 : Thread I} (ht1 : c1.threads[tid]? = some t1) (hrel : t1.RelFulfils A tid ts c1.mem) :
    StutterStepNT ts c.mem tid o ∧ o.thread.views.vwNew < ts := by
  have hwf := h0.reachable hc
  have hwf' := hwf.instr ht hstep ho
  have hwf1 := hwf'.reachable hr
  refine ⟨stutterStepNT_path hwf ht hts hstep ho hr ht1 (hrel.relPre_lt (hwf1 tid t1 ht1).1), ?_⟩
  have h1 : (c.withThread tid o.thread o.mem).threads[tid]? = some o.thread := by
    simp only [Config.withThread_get? c _ _ (lt_size_of_get? ht), ↓reduceIte]
  obtain ⟨t', h', hle⟩ := hr.vwNew_mono hwf' h1
  rw [ht1] at h'; cases h'
  exact Nat.lt_of_le_of_lt hle hrel.vwNew_lt

/-! ## (S1′) with pending non-temporal stores: a clamped simulation

The thread's run along the machine path is replayed by the thread alone from
`M` (`m = |M|`). Its ordinary accesses lie within `M` and replay exactly; its
non-temporal writes land above `m` in both runs, at different timestamps (the
other threads append in between on the path, not in the replay). The replay
state agrees with the real one up to clamping every value at `m + 1`
(`VR m`): everything at most `m` is equal, everything above `m` is above `m` in
both. That suffices because a value above `m` only ever comes from the
thread's own non-temporal writes, and the replay mirrors them: `NtCoh` (a
coherence view above `m` is the thread's latest non-temporal write to that
location, in both memories, with the same value) and `OwnAbove'` (every
replay message above `m` is the thread's own, below its coherence view). -/

/-- `x` and `y` agree once clamped at `m + 1`. -/
def VR (m x y : Nat) : Prop := min x (m + 1) = min y (m + 1)

/-- Unfold the given `VR` facts and the goal, then `omega`. Only for a few
facts at a time: `omega` splits every `min`. -/
local macro "vr" : tactic => `(tactic| ((try simp only [VR, Time, View] at ⊢); omega))

theorem VR.refl (m x : Nat) : VR m x x := rfl

theorem VR.symm {m x y : Nat} (h : VR m x y) : VR m y x := Eq.symm h

theorem VR.trans {m x y z : Nat} (h : VR m x y) (h' : VR m y z) : VR m x z := Eq.trans h h'

theorem VR.eq {m x y : Nat} (h : VR m x y) (hx : x ≤ m) : y = x := by unfold VR at h; omega

theorem VR.eq' {m x y : Nat} (h : VR m x y) (hy : y ≤ m) : x = y := by unfold VR at h; omega

theorem VR.gt {m x y : Nat} (h : VR m x y) (hx : m < x) : m < y := by unfold VR at h; omega

theorem VR.gt' {m x y : Nat} (h : VR m x y) (hy : m < y) : m < x := by unfold VR at h; omega

theorem VR.of_gt {m x y : Nat} (hx : m < x) (hy : m < y) : VR m x y := by vr

theorem VR.max {m x y x' y' : Nat} (h : VR m x y) (h' : VR m x' y') : VR m (max x x') (max y y') := by
  unfold VR at h h' ⊢; omega

theorem VR.min {m x y x' y' : Nat} (h : VR m x y) (h' : VR m x' y') : VR m (min x x') (min y y') := by
  unfold VR at h h' ⊢; omega

theorem VR.ite {m x y x' y' : Nat} {p : Prop} [Decidable p] (h : VR m x y) (h' : VR m x' y') :
    VR m (if p then x else x') (if p then y else y') := by
  split
  · exact h
  · exact h'

/-- Forwarding entries agreeing up to clamping. -/
def FwdR (m : Nat) : Option FwdItem → Option FwdItem → Prop
  | none, none => True
  | some f, some g => VR m f.time g.time ∧ VR m f.view g.view ∧ f.xcl = g.xcl ∧ VR m f.xclRead g.xclRead
  | _, _ => False

/-- Pending load exclusives agreeing up to clamping. -/
def XclbR (m : Nat) : Option (Time × View × Loc) → Option (Time × View × Loc) → Prop
  | none, none => True
  | some (t, ν, l), some (t', ν', l') => VR m t t' ∧ VR m ν ν' ∧ l = l'
  | _, _ => False

/-- Related pending load exclusives have related post-views. -/
theorem XclbR.xclRead {m : Nat} {a b : Option (Time × View × Loc)} (h : XclbR m a b) :
    VR m ((a.map (·.2.1)).getD 0) ((b.map (·.2.1)).getD 0) := by
  rcases a with _ | ⟨t, ν, l⟩ <;> rcases b with _ | ⟨t', ν', l'⟩
  · exact VR.refl _ _
  · exact (h : False).elim
  · exact (h : False).elim
  · exact h.2.1

/-- Optional timestamps agreeing up to clamping. -/
def OptR (m : Nat) : Option Time → Option Time → Prop
  | none, none => True
  | some t, some t' => VR m t t'
  | _, _ => False

/-- Two views agreeing up to clamping at `m + 1`. -/
structure Views.Rel (m : Nat) (a b : Views) : Prop where
  coh : ∀ l, VR m (a.getCoh l) (b.getCoh l)
  vrNew : VR m a.vrNew b.vrNew
  vrOld : VR m a.vrOld b.vrOld
  vrOldNR : VR m a.vrOldNR b.vrOldNR
  vwNew : VR m a.vwNew b.vwNew
  vwOld : VR m a.vwOld b.vwOld
  vwOldNT : VR m a.vwOldNT b.vwOldNT
  vCAP : VR m a.vCAP b.vCAP
  vRel : VR m a.vRel b.vRel
  fwd : ∀ l, FwdR m (a.getFwd l) (b.getFwd l)
  xclb : XclbR m a.xclb b.xclb

theorem Views.Rel.refl (m : Nat) (a : Views) : a.Rel m a := by
  refine ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun l => ?_, ?_⟩
  · cases a.getFwd l <;> simp [FwdR, VR]
  · rcases a.xclb with _ | ⟨t, ν, l⟩ <;> simp [XclbR, VR]

theorem Views.Rel.relPre {m : Nat} {a b : Views} (h : a.Rel m b) : VR m a.relPre b.relPre :=
  (h.vrOld.max h.vrOldNR).max h.vwOld

theorem Views.Rel.read {m : Nat} {vs vs' : Views} (h : vs.Rel m vs') {l : Loc} {ν ν' a a' : View}
    {acq xcl noRet : Bool} {t t' : Time} (hν : VR m ν ν') (ha : VR m a a') (ht : VR m t t') :
    Views.Rel m
      { (vs.setCoh l ν) with
        vrOld := if noRet then vs.vrOld else max vs.vrOld ν
        vrOldNR := if noRet then max vs.vrOldNR ν else vs.vrOldNR
        vrNew := if acq then max vs.vrNew ν else vs.vrNew
        vwNew := if acq then max vs.vwNew ν else vs.vwNew
        vCAP := max vs.vCAP a
        xclb := if xcl then some (t, ν, l) else vs.xclb }
      { (vs'.setCoh l ν') with
        vrOld := if noRet then vs'.vrOld else max vs'.vrOld ν'
        vrOldNR := if noRet then max vs'.vrOldNR ν' else vs'.vrOldNR
        vrNew := if acq then max vs'.vrNew ν' else vs'.vrNew
        vwNew := if acq then max vs'.vwNew ν' else vs'.vwNew
        vCAP := max vs'.vCAP a'
        xclb := if xcl then some (t', ν', l) else vs'.xclb } := by
  refine ⟨fun l' => ?_, VR.ite (h.vrNew.max hν) h.vrNew, VR.ite h.vrOld (h.vrOld.max hν),
    VR.ite (h.vrOldNR.max hν) h.vrOldNR, VR.ite (h.vwNew.max hν) h.vwNew, h.vwOld, h.vwOldNT,
    h.vCAP.max ha, h.vRel, h.fwd, ?_⟩
  · show VR m ((vs.setCoh l ν).getCoh l') ((vs'.setCoh l ν').getCoh l')
    rw [Views.getCoh_setCoh, Views.getCoh_setCoh]
    exact VR.ite ((h.coh l).max hν) (h.coh l')
  · cases xcl
    · exact h.xclb
    · exact ⟨ht, hν, rfl⟩

theorem Views.Rel.setNew {m : Nat} {vs vs' : Views} (h : vs.Rel m vs') {r r' w w' : View} (hr : VR m r r')
    (hw : VR m w w') : ({ vs with vrNew := r, vwNew := w } : Views).Rel m { vs' with vrNew := r', vwNew := w' } :=
  ⟨h.coh, hr, h.vrOld, h.vrOldNR, hw, h.vwOld, h.vwOldNT, h.vCAP, h.vRel, h.fwd, h.xclb⟩

theorem Views.Rel.setVCAP {m : Nat} {vs vs' : Views} (h : vs.Rel m vs') {x x' : View} (hx : VR m x x') :
    ({ vs with vCAP := x } : Views).Rel m { vs' with vCAP := x' } :=
  ⟨h.coh, h.vrNew, h.vrOld, h.vrOldNR, h.vwNew, h.vwOld, h.vwOldNT, hx, h.vRel, h.fwd, h.xclb⟩

theorem Views.Rel.xclbNone {m : Nat} {vs vs' : Views} (h : vs.Rel m vs') :
    ({ vs with xclb := none } : Views).Rel m { vs' with xclb := none } :=
  ⟨h.coh, h.vrNew, h.vrOld, h.vrOldNR, h.vwNew, h.vwOld, h.vwOldNT, h.vCAP, h.vRel, h.fwd, trivial⟩

/-- A list of views clamped at `m + 1`. -/
def clampL (m : Nat) (xs : List View) : List View := xs.map (min · (m + 1))

/-- The per-instruction views agreeing up to clamping. -/
structure InstrViews.Rel (m : Nat) (a b : InstrViews) : Prop where
  addrR : VR m a.addrR b.addrR
  addrW : VR m a.addrW b.addrW
  dataR : VR m a.dataR b.dataR
  dataW : VR m a.dataW b.dataW
  condW : VR m a.condW b.condW
  dataPer : a.dataPer.map (fun p => (min p.1 (m + 1), min p.2 (m + 1))) =
    b.dataPer.map (fun p => (min p.1 (m + 1), min p.2 (m + 1)))

theorem InstrViews.Rel.forStore {m : Nat} {a b : InstrViews} (h : a.Rel m b) (i : Nat) :
    (a.forStore i).Rel m (b.forStore i) := by
  have hi := congrArg (·[i]?) h.dataPer
  simp only [List.getElem?_map] at hi
  unfold InstrViews.forStore
  cases ha : a.dataPer[i]? with
  | none =>
    cases hb : b.dataPer[i]? with
    | none => exact h
    | some p => rw [ha, hb] at hi; cases hi
  | some p =>
    cases hb : b.dataPer[i]? with
    | none => rw [ha, hb] at hi; cases hi
    | some q =>
      rw [ha, hb] at hi
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hi
      exact ⟨h.addrR, h.addrW, hi.1, hi.2, h.condW, h.dataPer⟩

/-- Contexts agreeing up to clamping; the replay holds exactly the real
promises at most `m`. -/
structure Ctx.Rel (m : Nat) (c c' : Ctx) : Prop where
  views : c.views.Rel m c'.views
  prom : c'.prom = c.prom.filter (· ≤ m)
  loadViews : clampL m c.loadViews = clampL m c'.loadViews
  succView : VR m c.succView c'.succView
  rmwWrote : c.rmwWrote = c'.rmwWrote
  stores : c.stores = c'.stores

/-- A coherence view above `m` is the thread's latest (non-temporal) write to
that location, in both runs: the forwarding entry has its timestamp, and both
memories hold a message to the location there, with the same value. -/
def NtCoh (m : Nat) (vs : Views) (mem : Memory) (vs' : Views) (mem' : Memory) : Prop :=
  ∀ l, m < vs.getCoh l →
    (∃ f, vs.getFwd l = some f ∧ f.time = vs.getCoh l) ∧ (∃ f, vs'.getFwd l = some f ∧ f.time = vs'.getCoh l) ∧
    ∃ w w', mem.get? (vs.getCoh l) = some w ∧ mem'.get? (vs'.getCoh l) = some w' ∧ w.loc = l ∧ w'.loc = l ∧
      w.val = w'.val

/-- A forwarding entry above `m` is at most the coherence view. -/
def FwdCoh (m : Nat) (vs : Views) : Prop :=
  ∀ l f, vs.getFwd l = some f → m < f.time → f.time ≤ vs.getCoh l

/-- Every replay message above `m` is the thread's own, at most its coherence
view of the location. -/
def OwnAbove' (tid m : Nat) (vs : Views) (mem : Memory) : Prop :=
  ∀ u w, m < u → mem.get? u = some w → w.tid = tid ∧ u ≤ vs.getCoh w.loc

/-- The real context `c` and the replay context `c'` of an instruction of
thread `tid`, against memories extending `M`. -/
structure Ctx.Sim (M : Memory) (tid : Nat) (c c' : Ctx) : Prop where
  rel : c.Rel M.last c'
  memR : M.Prefix c.mem
  memP : M.Prefix c'.mem
  own : OwnAbove' tid M.last c'.views c'.mem
  bnd : c'.Bnd
  ntcoh : NtCoh M.last c.views c.mem c'.views c'.mem
  fwdcoh : FwdCoh M.last c.views

/-! ### Memory facts for the replay -/

theorem Memory.Prefix.writeIn_eq {M M' : Memory} (h : M.Prefix M') {l : Loc} {lo hi : Time} (hhi : hi ≤ M.last) :
    M'.writeIn l lo hi = M.writeIn l lo hi := by
  cases hw : M.writeIn l lo hi with
  | false =>
    cases hw' : M'.writeIn l lo hi with
    | false => rfl
    | true =>
      obtain ⟨t, w, h1, h2, h3, h4⟩ := (Memory.writeIn_iff _ _ _ _).mp hw'
      rw [h.get? (Nat.le_trans h2 hhi)] at h3
      rw [(Memory.writeIn_iff _ _ _ _).mpr ⟨t, w, h1, h2, h3, h4⟩] at hw; cases hw
  | true =>
    obtain ⟨t, w, h1, h2, h3, h4⟩ := (Memory.writeIn_iff _ _ _ _).mp hw
    rw [← h.get? (Nat.le_trans h2 hhi)] at h3
    exact (Memory.writeIn_iff _ _ _ _).mpr ⟨t, w, h1, h2, h3, h4⟩

theorem Memory.atomic_elim {mem : Memory} {l : Loc} {tid : Nat} {tr tw : Time} (ha : mem.atomic l tid tr tw = true)
    {v : Val} (hv : mem.read? l tr = some v) :
    ∀ u w, tr < u → u < tw → mem.get? u = some w → w.loc = l → w.tid = tid := by
  intro u w h1 h2 hw hl
  unfold Memory.atomic at ha
  rw [hv] at ha
  simp only [List.all_eq_true, List.mem_range] at ha
  have := ha (u - tr - 1) (by omega_t)
  rw [show tr + (u - tr - 1) + 1 = u by omega_t, hw] at this
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  rcases this with h | h
  · exact absurd hl h
  · exact h

theorem Memory.Prefix.atomic_eq {M M' : Memory} (h : M.Prefix M') {l : Loc} {tid : Nat} {tr tw : Time}
    (hlt : tr < tw) (htw : tw ≤ M.last) : M'.atomic l tid tr tw = M.atomic l tid tr tw := by
  cases ha : M.atomic l tid tr tw with
  | false =>
    cases ha' : M'.atomic l tid tr tw with
    | false => rfl
    | true => rw [h.atomic hlt htw ha'] at ha; cases ha
  | true =>
    unfold Memory.atomic
    rw [h.read? (by omega_t)]
    cases hv : M.read? l tr with
    | none => rfl
    | some v =>
      simp only [List.all_eq_true, List.mem_range]
      intro i hi
      rw [h.get? (by omega_t)]
      cases hw : M.get? (tr + i + 1) with
      | none => rfl
      | some w =>
        have := Memory.atomic_elim ha hv (tr + i + 1) w (by omega_t) (by omega_t) hw
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
        by_cases hl : w.loc = l
        · exact .inr (this hl)
        · exact .inl hl

/-! ### Small lemmas about the simulation invariants -/

theorem clampL_append {m : Nat} {xs ys : List View} (h : clampL m xs = clampL m ys) {a b : View} (hv : VR m a b) :
    clampL m (xs ++ [a]) = clampL m (ys ++ [b]) := by
  simp only [clampL, List.map_append, List.map_cons, List.map_nil] at h ⊢
  rw [h, show min a (m + 1) = min b (m + 1) from hv]

theorem Views.getCoh_le_setCoh (vs : Views) (l l' : Loc) (t : View) : vs.getCoh l' ≤ (vs.setCoh l t).getCoh l' := by
  rw [Views.getCoh_setCoh]
  split
  · rename_i h; subst h; omega_t
  · exact Nat.le_refl _

theorem OwnAbove'.mono {tid m : Nat} {vs vs2 : Views} {mem : Memory} (h : OwnAbove' tid m vs mem)
    (hc : ∀ l, vs.getCoh l ≤ vs2.getCoh l) : OwnAbove' tid m vs2 mem := by
  intro u w hu hw
  obtain ⟨h1, h2⟩ := h u w hu hw
  exact ⟨h1, Nat.le_trans h2 (hc _)⟩

theorem FwdCoh.congr {m : Nat} {vs vs2 : Views} (h : FwdCoh m vs) (hf : ∀ l, vs2.getFwd l = vs.getFwd l)
    (hc : ∀ l, vs.getCoh l ≤ vs2.getCoh l) : FwdCoh m vs2 := by
  intro l f hl hm
  rw [hf] at hl
  exact Nat.le_trans (h l f hl hm) (hc l)

/-- `NtCoh` survives a step that changes neither forwarding nor memory and
keeps every coherence view above `m` (on both sides) as it was. -/
theorem NtCoh.congr {m : Nat} {vs vs' vs2 vs2' : Views} {mem mem' : Memory} (h : NtCoh m vs mem vs' mem')
    (hc : ∀ l, m < vs2.getCoh l → vs2.getCoh l = vs.getCoh l ∧ vs2'.getCoh l = vs'.getCoh l)
    (hf : ∀ l, vs2.getFwd l = vs.getFwd l) (hf' : ∀ l, vs2'.getFwd l = vs'.getFwd l) :
    NtCoh m vs2 mem vs2' mem' := by
  intro l hl
  obtain ⟨e1, e2⟩ := hc l hl
  rw [e1] at hl ⊢
  rw [e2, hf, hf']
  exact h l hl

/-- Raising one coherence view to `ν ≤ m` keeps every coherence view above `m`. -/
theorem Views.getCoh_setCoh_gt {m : Nat} {vs : Views} {l l' : Loc} {ν : View} (hν : ν ≤ m)
    (h : m < (vs.setCoh l ν).getCoh l') : (vs.setCoh l ν).getCoh l' = vs.getCoh l' := by
  rw [Views.getCoh_setCoh] at h ⊢
  split at h
  · rename_i e; subst e; simp only [↓reduceIte]; omega_t
  · rename_i e; simp only [e, ↓reduceIte]

section Rules

variable (A : Arch) (tid : Nat)

/-- The pre-view of a read (`νpre` of `readSuccs`). -/
def readPre (iv : InstrViews) (c : Ctx) (k : LoadKind) : View :=
  max iv.addrR (max c.views.vrNew (if (A.loadKind k == .acq) = true then c.views.vRel else 0))

/-- The context after reading `v` from `t` (the body of `readSuccs`). -/
def readNext (iv : InstrViews) (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (t : Time)
    (v : Val) : Ctx :=
  let νpost := max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) t)
  let acq := (A.loadKind k).isAcquire
  let vs := c.views
  { c with
    views :=
      { (vs.setCoh l νpost) with
        vrOld := if noRet then vs.vrOld else max vs.vrOld νpost
        vrOldNR := if noRet then max vs.vrOldNR νpost else vs.vrOldNR
        vrNew := if acq then max vs.vrNew νpost else vs.vrNew
        vwNew := if acq then max vs.vwNew νpost else vs.vwNew
        vCAP := max vs.vCAP iv.addrW
        xclb := if xcl then some (t, νpost, l) else vs.xclb }
    loadViews := c.loadViews ++ [νpost]
    log := c.log ++ [.read l t v νpost] }

theorem mem_readSuccs {iv : InstrViews} {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} :
    x ∈ readSuccs A iv c k xcl l noRet ↔ ∃ t v, x = (t, v, readNext A iv c k xcl l noRet t v) ∧
      t ≤ c.mem.last ∧ c.mem.read? l t = some v ∧
      c.mem.writeIn l t (max (readPre A iv c k) (c.views.getCoh l)) = false ∧ c.prom.contains t = false := by
  unfold readSuccs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, h⟩
    split at h
    · cases h
    · rename_i v hv
      by_cases hc : (c.mem.writeIn l t (max (readPre A iv c k) (c.views.getCoh l)) || c.prom.contains t) = true
      · have hc' := hc
        unfold readPre at hc'
        simp only [hc', ↓reduceIte] at h; cases h
      · have hc' := hc
        unfold readPre at hc'
        simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
        injection h with h
        exact ⟨t, v, h.symm, Nat.le_of_lt_succ (List.mem_range.mp ht), hv, hc.1, hc.2⟩
  · rintro ⟨t, v, rfl, ht, hv, hw, hp⟩
    refine ⟨t, List.mem_range.mpr (Nat.lt_succ_of_le ht), ?_⟩
    simp only [hv]
    unfold readPre at hw
    simp only [hw, hp, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem readView_vr {m : Nat} {k : LoadKind} {f g : Option FwdItem} {t t' : Time} (hfg : FwdR m f g)
    (ht : VR m t t') (hiff : ∀ a b, f = some a → g = some b → (a.time = t ↔ b.time = t')) :
    VR m (readView A k f t) (readView A k g t') := by
  cases f with
  | none =>
    cases g with
    | none => exact ht
    | some b => exact hfg.elim
  | some a =>
    cases g with
    | none => exact hfg.elim
    | some b =>
      obtain ⟨-, h2, h3, h4⟩ := hfg
      have hi := hiff a b rfl rfl
      simp only [readView]
      rw [h3]
      by_cases ha : a.time = t
      · have hb := hi.mp ha
        simp only [ha, hb, decide_true, Bool.true_and]
        exact VR.ite (VR.ite (h2.max (VR.min h4 ht)) h2) ht
      · have hb : ¬ b.time = t' := fun h => ha (hi.mpr h)
        simp only [ha, hb, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact ht

theorem readSuccs_sim {M : Memory} {iv iv' : InstrViews} {c c' : Ctx} (hs : c.Sim M tid c')
    (hiv : iv.Rel M.last iv') (hiv' : iv'.Le c'.mem.last) {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) (hb : x.2.2.views.relPre ≤ M.last) :
    ∃ x' ∈ readSuccs A iv' c' k xcl l noRet, x'.2.1 = x.2.1 ∧ VR M.last x.1 x'.1 ∧ x'.1 ≤ c'.mem.last ∧
      x.2.2.Sim M tid x'.2.2 := by
  obtain ⟨t, v, rfl, htl, hv, hw, hp⟩ := (mem_readSuccs A).mp hx
  have hrel := hs.rel.views
  have hpre : VR M.last (readPre A iv c k) (readPre A iv' c' k) :=
    hiv.addrR.max (hrel.vrNew.max (VR.ite hrel.vRel (VR.refl _ _)))
  have hB : VR M.last (max (readPre A iv c k) (c.views.getCoh l)) (max (readPre A iv' c' k) (c'.views.getCoh l)) :=
    hpre.max (hrel.coh l)
  have hνm : max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) t) ≤ M.last := by
    have hb' := hb
    simp only [readNext, Views.relPre] at hb'
    cases noRet <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb' <;> omega_t
  have hprom' : ∀ t', M.last < t' → c'.prom.contains t' = false := by
    intro t' ht'
    rw [hs.rel.prom]
    cases hcon : (c.prom.filter (· ≤ M.last)).contains t'
    · rfl
    · have := (List.mem_filter.mp (List.contains_iff_mem.mp hcon)).2
      simp only [decide_eq_true_eq] at this; omega_t
  -- the replay's timestamp
  have key : ∃ t', t' ≤ c'.mem.last ∧ c'.mem.read? l t' = some v ∧
      c'.mem.writeIn l t' (max (readPre A iv' c' k) (c'.views.getCoh l)) = false ∧ c'.prom.contains t' = false ∧
      VR M.last t t' ∧
      VR M.last (readView A (A.loadKind k) (c.views.getFwd l) t) (readView A (A.loadKind k) (c'.views.getFwd l) t') := by
    by_cases htm : t ≤ M.last
    · refine ⟨t, Nat.le_trans htm hs.memP.last_le, ?_, ?_, ?_, VR.refl _ _, ?_⟩
      · rw [hs.memP.read? htm, ← hs.memR.read? htm]; exact hv
      · cases hw' : c'.mem.writeIn l t (max (readPre A iv' c' k) (c'.views.getCoh l))
        · rfl
        · exfalso
          obtain ⟨u, w, h1, h2, h3, h4⟩ := (Memory.writeIn_iff _ _ _ _).mp hw'
          by_cases hum : u ≤ M.last
          · rw [hs.memP.get? hum, ← hs.memR.get? hum] at h3
            have hub : u ≤ max (readPre A iv c k) (c.views.getCoh l) := by
              by_cases hBm : max (readPre A iv c k) (c.views.getCoh l) ≤ M.last
              · have := hB.eq hBm; omega_t
              · omega_t
            rw [(Memory.writeIn_iff _ _ _ _).mpr ⟨u, w, h1, hub, h3, h4⟩] at hw; cases hw
          · obtain ⟨-, hu⟩ := hs.own u w (by omega_t) h3
            rw [h4] at hu
            have hcm : M.last < c.views.getCoh l := (hrel.coh l).gt' (by omega_t)
            obtain ⟨-, -, w0, -, hw0, -, hw0l, -, -⟩ := hs.ntcoh l hcm
            rw [(Memory.writeIn_iff _ _ _ _).mpr ⟨_, w0, by omega_t, Nat.le_max_right _ _, hw0, hw0l⟩] at hw
            cases hw
      · rw [hs.rel.prom]
        cases hcon : (c.prom.filter (· ≤ M.last)).contains t
        · rfl
        · have := (List.mem_filter.mp (List.contains_iff_mem.mp hcon)).1
          rw [List.contains_iff_mem.mpr this] at hp; cases hp
      · refine readView_vr A (hrel.fwd l) (VR.refl _ _) (fun a b ha hb => ?_)
        have hab : FwdR M.last (some a) (some b) := ha ▸ hb ▸ hrel.fwd l
        have h1 : VR M.last a.time b.time := hab.1
        constructor
        · intro e; rw [← e] at htm ⊢; exact h1.eq htm
        · intro e; rw [← e] at htm ⊢; exact h1.eq' htm
    · have htm : M.last < t := by omega_t
      cases hf : c.views.getFwd l with
      | none =>
        exfalso; rw [hf] at hνm; simp only [readView] at hνm; omega_t
      | some f =>
        by_cases hcond : (decide (f.time = t) && (!f.xcl || (!A.fwdXclOnlyPlain || A.loadKind k == .plain))) = true
        · have hft : f.time = t := by
            rw [Bool.and_eq_true, decide_eq_true_eq] at hcond; exact hcond.1
          have htc : t ≤ c.views.getCoh l := hft ▸ hs.fwdcoh l f hf (hft ▸ htm)
          have hcm : M.last < c.views.getCoh l := by omega_t
          obtain ⟨-, ⟨g, hg, hgt⟩, w, w', hw0, hw0', hwl, hw'l, hval⟩ := hs.ntcoh l hcm
          have hteq : t = c.views.getCoh l := by
            by_cases e : t = c.views.getCoh l
            · exact e
            · exfalso
              rw [(Memory.writeIn_iff _ _ _ _).mpr ⟨_, w, by omega_t, Nat.le_max_right _ _, hw0, hwl⟩] at hw
              cases hw
          have hcm' : M.last < c'.views.getCoh l := (hrel.coh l).gt hcm
          have hvw : w.val = v := by
            rw [hteq] at hv
            simp only [Memory.read?, hw0, hwl, beq_self_eq_true, ↓reduceIte,
              show c.views.getCoh l ≠ 0 by omega_t] at hv
            exact Option.some.inj hv
          refine ⟨c'.views.getCoh l, c'.mem.last_le_of_get?_eq_some hw0', ?_, ?_, hprom' _ hcm', hteq ▸ hrel.coh l, ?_⟩
          · simp only [Memory.read?, hw0', hw'l, beq_self_eq_true, ↓reduceIte,
              show c'.views.getCoh l ≠ 0 by omega_t, ← hval, hvw]
          · cases hw' : c'.mem.writeIn l (c'.views.getCoh l) (max (readPre A iv' c' k) (c'.views.getCoh l))
            · rfl
            · exfalso
              obtain ⟨u, w2, h1, -, h3, h4⟩ := (Memory.writeIn_iff _ _ _ _).mp hw'
              obtain ⟨-, hu⟩ := hs.own u w2 (by omega_t) h3
              rw [h4] at hu; omega_t
          · refine readView_vr A (hf ▸ hrel.fwd l) (hteq ▸ hrel.coh l) (fun a b ha hb => ?_)
            cases ha
            rw [hg] at hb; cases hb
            exact ⟨fun _ => hgt, fun _ => hft⟩
        · exfalso
          rw [hf] at hνm
          simp only [readView, hcond, Bool.false_eq_true, ↓reduceIte] at hνm
          omega_t
  obtain ⟨t', htl', hv', hw', hp', ht', hrv⟩ := key
  have hx' := (mem_readSuccs A (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (noRet := noRet)
    (x := (t', v, readNext A iv' c' k xcl l noRet t' v))).mpr ⟨t', v, rfl, htl', hv', hw', hp'⟩
  have hν : VR M.last (max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) t))
      (max (readPre A iv' c' k) (readView A (A.loadKind k) (c'.views.getFwd l) t')) := hpre.max hrv
  have hνeq := hν.eq hνm
  refine ⟨_, hx', rfl, ht', htl', ⟨⟨Views.Rel.read hrel hν hiv.addrW ht', hs.rel.prom,
    clampL_append hs.rel.loadViews hν, hs.rel.succView, hs.rel.rmwWrote, hs.rel.stores⟩,
    hs.memR, hs.memP, hs.own.mono (fun l' => Views.getCoh_le_setCoh _ _ _ _),
    (readSuccs_bnd A iv' hs.bnd hiv' hx').1, ?_, hs.fwdcoh.congr (fun _ => rfl) (fun l' => Views.getCoh_le_setCoh _ _ _ _)⟩⟩
  refine hs.ntcoh.congr (fun l' hl' => ?_) (fun _ => rfl) (fun _ => rfl)
  have e1 := Views.getCoh_setCoh_gt hνm hl'
  have hold : M.last < c.views.getCoh l' := e1 ▸ hl'
  have hold' : M.last < c'.views.getCoh l' := (hrel.coh l').gt hold
  refine ⟨e1, ?_⟩
  exact Views.getCoh_setCoh_gt (by rw [hνeq]; exact hνm)
    (Nat.lt_of_lt_of_le hold' (Views.getCoh_le_setCoh _ _ _ _))

/-- The pre-view of a write (`νpre` of `writeSuccs`). -/
def writePre (iv : InstrViews) (c : Ctx) (k : StoreKind) (extra : View) : View :=
  max (max iv.addrW (max iv.dataW (max iv.condW extra))) (max (max c.views.vwNew c.views.vCAP)
    (if (A.storeKind k == .rel) = true then max (max c.views.vrOld c.views.vrOldNR) c.views.vwOld
     else if (A.storeKind k == .nt) = true then max c.views.vrOld c.views.vrOldNR else 0))

/-- The conditions of `writeSuccs` for the timestamp `t`. -/
def WriteOk (iv : InstrViews) (c : Ctx) (k : StoreKind) (l : Loc) (tr : Option Time) (extra : View)
    (t : Time) : Prop :=
  max (writePre A iv c k extra) (c.views.getCoh l) < t ∧ ∀ a, tr = some a → a < t ∧ c.mem.atomic l tid a t = true

theorem writeOk_iff {iv : InstrViews} {c : Ctx} {k : StoreKind} {l : Loc} {tr : Option Time} {extra : View}
    {t : Time} :
    (max (writePre A iv c k extra) (c.views.getCoh l) < t &&
      (match tr with | some tr => tr < t && c.mem.atomic l tid tr t | none => true)) = true ↔
    WriteOk A tid iv c k l tr extra t := by
  unfold WriteOk
  cases tr with
  | none => simp
  | some a => simp [Bool.and_eq_true, decide_eq_true_eq]

theorem mem_writeSuccs {xr : View} {iv : InstrViews} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} {c2 : Ctx} :
    c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr ↔
    (∃ t ∈ c.prom, ∃ w, c.mem.get? t = some w ∧ w.loc = l ∧ w.val = v ∧ w.tid = tid ∧
        WriteOk A tid iv c k l tr extra t ∧
        c2 = afterWrite A iv c (A.storeKind k) xcl l v t (max iv.addrR (max iv.dataR extra)) true xr) ∨
    (WriteOk A tid iv c k l tr extra (c.mem.last + 1) ∧
      c2 = afterWrite A iv
        { c with mem := (c.mem.append { loc := l, val := v, tid }).1,
                 prom := c.prom ++ [c.mem.last + 1],
                 promisedNow := c.promisedNow ++
                   [({ loc := l, val := v, tid }, max (writePre A iv c k extra) (c.views.getCoh l))] }
        (A.storeKind k) xcl l v (c.mem.last + 1) (max iv.addrR (max iv.dataR extra)) false xr) := by
  unfold writeSuccs
  rw [List.mem_append, List.mem_filterMap]
  apply or_congr
  · constructor
    · rintro ⟨t, ht, h⟩
      split at h
      · rename_i w hw
        obtain ⟨hc, h⟩ := Option.ite_none_right_eq_some.mp h
        rw [Bool.and_eq_true] at hc
        obtain ⟨hc1, hc2⟩ := hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc1
        exact ⟨t, ht, w, hw, hc1.1.1, hc1.1.2, hc1.2, (writeOk_iff A tid).mp hc2, (Option.some.inj h).symm⟩
      · cases h
    · rintro ⟨t, ht, w, hw, h1, h2, h3, h4, rfl⟩
      refine ⟨t, ht, ?_⟩
      have hok := (writeOk_iff A tid).mpr h4
      simp only [hw]
      rw [Option.ite_none_right_eq_some]
      refine ⟨?_, rfl⟩
      rw [Bool.and_eq_true]
      exact ⟨by simp only [h1, h2, h3, beq_self_eq_true, Bool.and_self], hok⟩
  · constructor
    · intro h
      simp only [Memory.append] at h
      obtain ⟨hok, h⟩ := mem_ite_nil_iff_nt.mp h
      rw [List.mem_singleton] at h
      subst h
      exact ⟨(writeOk_iff A tid).mp hok, rfl⟩
    · rintro ⟨hok, rfl⟩
      have hok' := (writeOk_iff A tid).mpr hok
      simp only [Memory.append]
      exact mem_ite_nil_iff_nt.mpr ⟨hok', List.mem_singleton.mpr rfl⟩

theorem afterWrite_getCoh (iv : InstrViews) {xr : View} (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time)
    (νfwd : View) (ful : Bool) (l' : Loc) :
    (afterWrite A iv c k xcl l v t νfwd ful xr).views.getCoh l' =
      if l' = l then max (c.views.getCoh l) t else c.views.getCoh l' :=
  Views.getCoh_setCoh c.views l l' t

theorem afterWrite_getFwd {xr : View} (iv : InstrViews) (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time)
    (νfwd : View) (ful : Bool) (l' : Loc) :
    (afterWrite A iv c k xcl l v t νfwd ful xr).views.getFwd l' =
      if l' = l then some { time := t, view := νfwd, xcl, xclRead := xr } else c.views.getFwd l' :=
  Views.getFwd_setFwd c.views l l' _

/-- `afterWrite` on related contexts. -/
theorem afterWrite_rel {m : Nat} {iv iv' : InstrViews} {c c' : Ctx} (hv : c.views.Rel m c'.views)
    (hiv : VR m iv.addrW iv'.addrW) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) {t t' : Time} (ht : VR m t t')
    {νfwd νfwd' : View} (hν : VR m νfwd νfwd') (ful ful' : Bool) {xr xr' : View} (hxr : VR m xr xr')
    (hprom : (c'.prom.erase t') = (c.prom.erase t).filter (· ≤ m))
    (hlv : clampL m c.loadViews = clampL m c'.loadViews) (hrw : c.rmwWrote = c'.rmwWrote) (hst : c.stores = c'.stores) :
    (afterWrite A iv c k xcl l v t νfwd ful xr).Rel m (afterWrite A iv' c' k xcl l v t' νfwd' ful' xr') := by
  refine ⟨⟨fun l' => ?_, hv.vrNew, hv.vrOld, hv.vrOldNR, hv.vwNew, VR.ite hv.vwOld (hv.vwOld.max ht),
    VR.ite (hv.vwOldNT.max ht) hv.vwOldNT, hv.vCAP.max hiv, VR.ite (hv.vRel.max ht) hv.vRel, fun l' => ?_, ?_⟩,
    hprom, hlv, VR.ite (VR.refl _ _) ht, hrw, congrArg (· + 1) hst⟩
  · rw [afterWrite_getCoh, afterWrite_getCoh]
    exact VR.ite ((hv.coh l).max ht) (hv.coh l')
  · rw [afterWrite_getFwd, afterWrite_getFwd]
    split
    · exact ⟨ht, hν, rfl, hxr⟩
    · exact hv.fwd l'
  · cases xcl
    · exact hv.xclb
    · trivial

theorem filter_erase_of_not {xs : List Time} {t m : Nat} (ht : m < t) :
    (xs.erase t).filter (· ≤ m) = xs.filter (· ≤ m) := by
  rw [← List.erase_filter, List.erase_of_not_mem]
  intro h
  have := (List.mem_filter.mp h).2
  simp only [decide_eq_true_eq] at this
  omega_t

/-- The replay's exclusive check passes: below `m` it sees what the real run
saw, above `m` only the thread's own messages. -/
theorem atomic_replay {M : Memory} {c c' : Ctx} (hs : c.Sim M tid c') {l : Loc} {a t t' : Time}
    (hr : a ≤ M.last → c.mem.atomic l tid a t = true) (hmt : M.last < t) :
    c'.mem.atomic l tid a t' = true := by
  by_cases ham : a ≤ M.last
  · cases hrd : c'.mem.read? l a with
    | none => unfold Memory.atomic; rw [hrd]
    | some val =>
      have hrd0 : c.mem.read? l a = some val := by rw [hs.memR.read? ham, ← hs.memP.read? ham]; exact hrd
      apply Memory.atomic_of_forall
      intro u w h1 h2 hw hl
      by_cases hum : u ≤ M.last
      · rw [hs.memP.get? hum, ← hs.memR.get? hum] at hw
        exact Memory.atomic_elim (hr ham) hrd0 u w h1 (by omega_t) hw hl
      · exact (hs.own u w (by omega_t) hw).1
  · apply Memory.atomic_of_forall
    intro u w h1 _ hw _
    exact (hs.own u w (by omega_t) hw).1

theorem afterWrite_mem_eq {xr : View} (iv : InstrViews) (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time)
    (νfwd : View) (ful : Bool) : (afterWrite A iv c k xcl l v t νfwd ful xr).mem = c.mem := rfl

theorem writePre_vr {m : Nat} {iv iv' : InstrViews} {c c' : Ctx} (hv : c.views.Rel m c'.views)
    (hiv : iv.Rel m iv') (k : StoreKind) {extra extra' : View} (hex : VR m extra extra') :
    VR m (writePre A iv c k extra) (writePre A iv' c' k extra') :=
  (hiv.addrW.max (hiv.dataW.max (hiv.condW.max hex))).max ((hv.vwNew.max hv.vCAP).max
    (VR.ite ((hv.vrOld.max hv.vrOldNR).max hv.vwOld) (VR.ite (hv.vrOld.max hv.vrOldNR) (VR.refl _ _))))

theorem writePre_le {iv : InstrViews} {c : Ctx} (hc : c.Bnd) (hiv : iv.Le c.mem.last) (k : StoreKind)
    {l : Loc} {extra : View} (hex : extra ≤ c.mem.last) : max (writePre A iv c k extra) (c.views.getCoh l) ≤ c.mem.last := by
  have hb := hc.views.le
  unfold writePre
  refine Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hiv.addrW, Nat.max_le.mpr ⟨hiv.dataW,
    Nat.max_le.mpr ⟨hiv.condW, hex⟩⟩⟩, Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hb.vwNew, hb.vCAP⟩, ?_⟩⟩, hb.coh l⟩
  split
  · exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hb.vrOld, hb.vrOldNR⟩, hb.vwOld⟩
  · split
    · exact Nat.max_le.mpr ⟨hb.vrOld, hb.vrOldNR⟩
    · exact Nat.zero_le _

/-- A real write above `m` (a non-temporal one, in practice) is replayed as a
fresh write of the same message at the end of the replay memory. `c0` is the
real context the write is performed in (`c`, or `c` with the message
appended). -/
theorem write_fresh_sim {M : Memory} {iv iv' : InstrViews} {c c' c0 : Ctx} (hs : c.Sim M tid c')
    (hiv : iv.Rel M.last iv') (hiv' : iv'.Le c'.mem.last) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr') (htr' : ∀ a, tr' = some a → a ≤ c'.mem.last)
    {extra extra' : View} (hex : VR M.last extra extra') (hex' : extra' ≤ c'.mem.last) {t : Time}
    (htm : M.last < t) (hok : WriteOk A tid iv c k l tr extra t)
    (hc0 : c0.views = c.views) (hlv0 : c0.loadViews = c.loadViews)
    (hrw0 : c0.rmwWrote = c.rmwWrote) (hst0 : c0.stores = c.stores) (hm0 : c.mem.Prefix c0.mem)
    (hw0 : ∃ w, c0.mem.get? t = some w ∧ w.loc = l ∧ w.val = v)
    (hp0 : (c0.prom.erase t).filter (· ≤ M.last) = c.prom.filter (· ≤ M.last)) (ful : Bool)
    {xr xr' : View} (hxr : VR M.last xr xr') :
    ∃ c2' ∈ writeSuccs A tid iv' c' k xcl l v tr' extra' xr',
      (afterWrite A iv c0 (A.storeKind k) xcl l v t (max iv.addrR (max iv.dataR extra)) ful xr).Sim M tid c2' := by
  have hrel := hs.rel.views
  have hB' := writePre_le A (l := l) hs.bnd hiv' k hex'
  have hML := hs.memP.last_le
  have hcl : c.views.getCoh l < t := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1
  have hok' : WriteOk A tid iv' c' k l tr' extra' (c'.mem.last + 1) := by
    refine ⟨by omega_t, fun a ha => ⟨by have := htr' a ha; omega_t, ?_⟩⟩
    refine atomic_replay tid hs (fun ham => ?_) htm
    cases tr with
    | none => cases tr' <;> simp only [OptR] at htr; cases ha
    | some r =>
      cases tr' with
      | none => exact htr.elim
      | some a' =>
        have e : a' = a := Option.some.inj ha
        subst e
        have hra : r = a' := (show VR M.last r a' from htr).eq' ham
        subst hra
        exact (hok.2 r rfl).2
  have hmem := (mem_writeSuccs A tid (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr')
    (extra := extra') (xr := xr')).mpr (Or.inr ⟨hok', rfl⟩)
  refine ⟨_, hmem, ?_⟩
  have ht' : VR M.last t (c'.mem.last + 1) := VR.of_gt htm (by omega_t)
  have hnot : c'.mem.last + 1 ∉ c'.prom := by
    rw [hs.rel.prom]; intro h
    have := (List.mem_filter.mp h).2
    simp only [decide_eq_true_eq] at this; omega_t
  obtain ⟨w0, hw0, hw0l, hw0v⟩ := hw0
  refine ⟨afterWrite_rel A (hc0 ▸ hrel) hiv.addrW (A.storeKind k) xcl l v ht' (hiv.addrR.max (hiv.dataR.max hex)) ful false hxr ?_
      (hlv0 ▸ hs.rel.loadViews) (hrw0 ▸ hs.rel.rmwWrote) (hst0 ▸ hs.rel.stores),
    hs.memR.trans hm0, hs.memP.trans (Memory.Prefix.append _ _), ?_, (writeSuccs_bnd A tid iv' hs.bnd hiv' hex' hmem).1,
    ?_, ?_⟩
  · show (c'.prom ++ [c'.mem.last + 1]).erase (c'.mem.last + 1) = _
    rw [List.erase_append_right _ hnot, hp0, ← hs.rel.prom]
    simp
  · intro u w hu hw
    rw [afterWrite_mem_eq] at hw
    rcases Memory.get?_append_eq_some _ _ hw with ⟨-, hw'⟩ | ⟨rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := hs.own u w hu hw'
      refine ⟨h1, Nat.le_trans h2 ?_⟩
      rw [afterWrite_getCoh]
      split
      · rename_i e; rw [e]; omega_t
      · exact Nat.le_refl _
    · refine ⟨rfl, ?_⟩
      rw [afterWrite_getCoh]
      simp only [↓reduceIte]
      omega_t
  · intro l' hl'
    rw [afterWrite_getCoh, hc0] at hl'
    simp only [afterWrite_getCoh, afterWrite_getFwd, afterWrite_mem_eq, hc0]
    by_cases e : l' = l
    · subst e
      simp only [↓reduceIte, Option.some.injEq, exists_eq_left']
      have e1 : max (c.views.getCoh l') t = t := by omega_t
      have e2 : max (c'.views.getCoh l') (c'.mem.last + 1) = c'.mem.last + 1 := by
        have := hs.bnd.views.le.coh l'; omega_t
      rw [e1, e2]
      refine ⟨rfl, rfl, w0, _, hw0, Memory.get?_append_last _ _, hw0l, rfl, hw0v⟩
    · simp only [e, ↓reduceIte] at hl' ⊢
      obtain ⟨h1, h2, w1, w1', hw1, hw1', h3⟩ := hs.ntcoh l' hl'
      refine ⟨h1, h2, w1, w1', ?_, ?_, h3⟩
      · rw [hm0.get? (c.mem.last_le_of_get?_eq_some hw1)]; exact hw1
      · rw [Memory.get?_append_of_le _ _ _ (c'.mem.last_le_of_get?_eq_some hw1')]; exact hw1'
  · intro l' f hf hm
    rw [afterWrite_getFwd] at hf
    rw [afterWrite_getCoh, hc0]
    by_cases e : l' = l
    · subst e
      simp only [↓reduceIte, Option.some.injEq] at hf ⊢
      subst hf
      omega_t
    · simp only [e, ↓reduceIte] at hf ⊢
      rw [hc0] at hf
      exact hs.fwdcoh l' f hf hm

/-- **One write, replayed.** A write of the real run is matched by a write of
the replay: the same fulfilment at or below `m`, a fresh write above. -/
theorem writeSuccs_sim {xr xr' : View} {M : Memory} {iv iv' : InstrViews} {c c' : Ctx} (hs : c.Sim M tid c')
    (hiv : iv.Rel M.last iv') (hiv' : iv'.Le c'.mem.last) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr tr' : Option Time} (htr : OptR M.last tr tr') (htr' : ∀ a, tr' = some a → a ≤ c'.mem.last)
    {extra extra' : View} (hex : VR M.last extra extra') (hex' : extra' ≤ c'.mem.last) {c2 : Ctx}
    (h : c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr) (hxr : VR M.last xr xr') :
    ∃ c2' ∈ writeSuccs A tid iv' c' k xcl l v tr' extra' xr', c2.Sim M tid c2' := by
  have hrel := hs.rel.views
  have hB := (writePre_vr A hrel hiv k hex).max (hrel.coh l)
  rcases (mem_writeSuccs A tid).mp h with ⟨t, htp, w, hw, hwl, hwv, hwt, hok, rfl⟩ | ⟨hok, rfl⟩
  · by_cases htm : t ≤ M.last
    · -- the same fulfilment
      have hbt : max (writePre A iv c k extra) (c.views.getCoh l) ≤ M.last := by have := hok.1; omega_t
      have hok' : WriteOk A tid iv' c' k l tr' extra' t := by
        refine ⟨by rw [hB.eq hbt]; exact hok.1, fun a ha => ?_⟩
        cases tr with
        | none => cases tr' <;> simp only [OptR] at htr; cases ha
        | some r =>
          cases tr' with
          | none => exact htr.elim
          | some a' =>
            have e : a' = a := Option.some.inj ha
            subst e
            have hr := hok.2 r rfl
            have hra : a' = r := (show VR M.last r a' from htr).eq (by omega_t)
            subst hra
            refine ⟨hr.1, ?_⟩
            rw [hs.memP.atomic_eq hr.1 htm, ← hs.memR.atomic_eq hr.1 htm]; exact hr.2
      have htp' : t ∈ c'.prom := by
        rw [hs.rel.prom]; exact List.mem_filter.mpr ⟨htp, by simpa using htm⟩
      have hw' : c'.mem.get? t = some w := by rw [hs.memP.get? htm, ← hs.memR.get? htm]; exact hw
      have hmem := (mem_writeSuccs A tid (iv := iv') (c := c') (k := k) (xcl := xcl) (l := l) (v := v) (tr := tr')
        (extra := extra') (xr := xr')).mpr (Or.inl ⟨t, htp', w, hw', hwl, hwv, hwt, hok', rfl⟩)
      refine ⟨_, hmem, afterWrite_rel A hrel hiv.addrW _ _ _ _ (VR.refl _ _) (hiv.addrR.max (hiv.dataR.max hex))
          true true hxr (by rw [hs.rel.prom, List.erase_filter]) hs.rel.loadViews hs.rel.rmwWrote hs.rel.stores,
        hs.memR, hs.memP, hs.own.mono (fun l' => Views.getCoh_le_setCoh _ _ _ _),
        (writeSuccs_bnd A tid iv' hs.bnd hiv' hex' hmem).1, ?_, ?_⟩
      · intro l' hl'
        rw [afterWrite_getCoh] at hl'
        simp only [afterWrite_getCoh, afterWrite_getFwd, afterWrite_mem_eq]
        by_cases e : l' = l
        · subst e
          simp only [↓reduceIte] at hl'
          have := hok.1; omega_t
        · simp only [e, ↓reduceIte] at hl' ⊢
          exact hs.ntcoh l' hl'
      · intro l' f hf hm
        rw [afterWrite_getFwd] at hf
        rw [afterWrite_getCoh]
        by_cases e : l' = l
        · subst e
          simp only [↓reduceIte, Option.some.injEq] at hf
          subst hf; simp only at hm; omega_t
        · simp only [e, ↓reduceIte] at hf ⊢
          exact hs.fwdcoh l' f hf hm
    · exact write_fresh_sim A tid hs hiv hiv' htr htr' hex hex' (by omega_t) hok rfl rfl rfl rfl
        (.refl _) ⟨w, hw, hwl, hwv⟩ (filter_erase_of_not (by omega_t)) true hxr
  · have htm : M.last < c.mem.last + 1 := by have := hs.memR.last_le; omega_t
    let c0r : Ctx :=
      { c with mem := (c.mem.append { loc := l, val := v, tid }).1,
               prom := c.prom ++ [c.mem.last + 1],
               promisedNow := c.promisedNow ++
                 [({ loc := l, val := v, tid }, max (writePre A iv c k extra) (c.views.getCoh l))] }
    refine write_fresh_sim A tid (c0 := c0r) hs hiv hiv' htr htr' hex hex' htm hok rfl rfl rfl rfl
      (Memory.Prefix.append _ _) ⟨_, Memory.get?_append_last _ _, rfl, rfl⟩ ?_ false hxr
    show ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).filter (· ≤ M.last) = _
    rw [filter_erase_of_not htm, List.filter_append]
    simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq]
    simp only [show ¬ (c.mem.last + 1 ≤ M.last) by omega_t, ↓reduceIte, List.append_nil]

end Rules

/-- A step that keeps coherence, forwarding, memory, promises and load views
on both sides keeps the simulation, given related views. -/
theorem Ctx.Sim.congr {M : Memory} {tid : Nat} {c c' c2 c2' : Ctx} (hs : c.Sim M tid c')
    (hv : c2.views.Rel M.last c2'.views) (hcoh : ∀ l, c2.views.getCoh l = c.views.getCoh l)
    (hcoh' : ∀ l, c2'.views.getCoh l = c'.views.getCoh l) (hf : ∀ l, c2.views.getFwd l = c.views.getFwd l)
    (hf' : ∀ l, c2'.views.getFwd l = c'.views.getFwd l) (hm : c2.mem = c.mem) (hm' : c2'.mem = c'.mem)
    (hp : c2.prom = c.prom) (hp' : c2'.prom = c'.prom) (hlv : c2.loadViews = c.loadViews)
    (hlv' : c2'.loadViews = c'.loadViews) (hsv : VR M.last c2.succView c2'.succView)
    (hrw : c2.rmwWrote = c2'.rmwWrote) (hst : c2.stores = c2'.stores) (hb : c2'.Bnd) : c2.Sim M tid c2' := by
  refine ⟨⟨hv, by rw [hp, hp', hs.rel.prom], by rw [hlv, hlv']; exact hs.rel.loadViews, hsv, hrw, hst⟩,
    hm ▸ hs.memR, hm' ▸ hs.memP, ?_, hb, ?_, hs.fwdcoh.congr hf (fun l => Nat.le_of_eq (hcoh l).symm)⟩
  · rw [hm']; exact hs.own.mono (fun l => Nat.le_of_eq (hcoh' l).symm)
  · rw [hm, hm']
    exact hs.ntcoh.congr (fun l _ => ⟨hcoh l, hcoh' l⟩) hf hf'

theorem fenceStep_sim {M : Memory} {tid : Nat} {c c' : Ctx} (hs : c.Sim M tid c') (k : FenceKind) :
    (fenceStep c k).Sim M tid (fenceStep c' k) := by
  have hv := hs.rel.views
  have hb := fenceStep_bnd hs.bnd k
  cases k
  · exact hs.congr (hv.setNew (hv.vrNew.max ((hv.vrOld.max hv.vrOldNR).max (hv.vwOld.max hv.vwOldNT)))
      (hv.vwNew.max ((hv.vrOld.max hv.vrOldNR).max (hv.vwOld.max hv.vwOldNT))))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb
  · exact hs.congr (hv.setNew (hv.vrNew.max hv.vrOld) (hv.vwNew.max hv.vrOld))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb
  · exact hs.congr (hv.setNew hv.vrNew (hv.vwNew.max (hv.vwOld.max hv.vwOldNT)))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb
  · exact hs.congr (hv.setNew (hv.vrNew.max (hv.vwOld.max hv.vwOldNT)) (hv.vwNew.max (hv.vwOld.max hv.vwOldNT)))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb
  · exact hs.congr (hv.setNew (hv.vrNew.max hv.vCAP) hv.vwNew)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      hs.rel.rmwWrote hs.rel.stores hb

theorem fenceOpt_sim {M : Memory} {tid : Nat} {c c' : Ctx} (hs : c.Sim M tid c') (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).Sim M tid (if b then fenceStep c' k else c') := by
  cases b
  · exact hs
  · exact fenceStep_sim hs k

theorem rmwPost_sim (A : Arch) {M : Memory} {tid : Nat} {c c' : Ctx} (hs : c.Sim M tid c') (k : RmwKind)
    (noRet : Bool) (l : Loc) : (rmwPost A k noRet l c).Sim M tid (rmwPost A k noRet l c') := by
  have hv := hs.rel.views
  have hb := (rmwPost_bnd A hs.bnd k noRet l).1
  revert hb
  unfold rmwPost
  by_cases hk : (A.rmwKind k == .acqRel && !noRet) = true
  · simp only [hk, ↓reduceIte]
    intro hb
    exact hs.congr (hv.setNew (hv.vrNew.max (hv.coh l)) (hv.vwNew.max (hv.coh l)))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl hs.rel.succView
      rfl hs.rel.stores hb
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    intro hb
    exact hs.congr hv (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl
      hs.rel.succView rfl hs.rel.stores hb

theorem clampL_getLastD {m : Nat} {xs ys : List View} (h : clampL m xs = clampL m ys) :
    VR m (xs.getLastD 0) (ys.getLastD 0) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact VR.refl _ _
    | cons y ys => simp [clampL] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [clampL] at h
    | cons y ys =>
      simp only [clampL, List.map_cons, List.cons.injEq] at h
      cases xs with
      | nil =>
        cases ys with
        | nil => exact h.1
        | cons _ _ => simp at h
      | cons x' xs' =>
        cases ys with
        | nil => simp at h
        | cons y' ys' =>
          rw [List.getLastD_cons, List.getLastD_cons]
          have := ih (ys := y' :: ys') h.2
          rw [List.getLastD_cons, List.getLastD_cons] at this ⊢
          exact this

section Rules

variable (A : Arch) (tid : Nat)

/-- **One instruction's event tree, replayed.** A run of the event tree from
the real context that ends with `relPre ≤ |M|` is matched by a run from the
replay context, ending in simulating contexts. -/
theorem runTree_sim {σ : Type} {M : Memory} {iv iv' : InstrViews} (hiv : iv.Rel M.last iv') (tree : EvTree σ) :
    ∀ (c c' : Ctx) (s : σ) (c2 : Ctx), c.Sim M tid c' → iv'.Le c'.mem.last → c.views.FwdOk →
      .ok (s, c2) ∈ runTree A tid iv c tree → c2.views.relPre ≤ M.last →
      ∃ c2', .ok (s, c2') ∈ runTree A tid iv' c' tree ∧ c2.Sim M tid c2' := by
  induction tree with
  | done s0 =>
    intro c c' s c2 hs _ _ h _
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨c', by simp [runTree], hs⟩
  | fault msg =>
    intro c c' s c2 _ _ _ h
    simp [runTree] at h
  | choose n k ih =>
    intro c c' s c2 hs hiv' hf h hb
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨i, hi, h⟩ := h
    obtain ⟨c2', h', hs'⟩ := ih i c c' s c2 hs hiv' hf h hb
    exact ⟨c2', ⟨i, hi, h'⟩, hs'⟩
  | load k xcl l ret ih =>
    intro c c' s c2 hs hiv' hf h hb
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨⟨t, v, c0⟩, hx, h⟩ := h
    have hs0 := readSuccs_silent A iv hf hx
    have hs1 := runTree_silent A tid iv _ c0 s c2 hs0.fwd h
    obtain ⟨⟨t', v', c0'⟩, hx', hv, -, -, hsim⟩ :=
      readSuccs_sim A tid hs hiv hiv' hx (Nat.le_trans hs1.relPre hb)
    simp only at hv
    have hm0 : c0'.mem = c'.mem := (readSuccs_mp A iv' hx').1
    obtain ⟨c2', h', hs'⟩ := ih v c0 c0' s c2 hsim (hm0 ▸ hiv') hs0.fwd h hb
    exact ⟨c2', ⟨(t', v', c0'), hx', by rw [hv]; exact h'⟩, hs'⟩
  | store k xcl l v ret ih =>
    intro c c' s c2 hs hiv' hf h hb
    have hv := hs.rel.views
    have htr : OptR M.last (if xcl then c.views.xclb.map (·.1) else none)
        (if xcl then c'.views.xclb.map (·.1) else none) := by
      cases xcl
      · trivial
      · have hx := hv.xclb
        revert hx
        rcases c.views.xclb with _ | ⟨a, b, l1⟩ <;> rcases c'.views.xclb with _ | ⟨a', b', l2⟩ <;>
          simp only [XclbR, OptR, Option.map, imp_self, ↓reduceIte]
        rintro ⟨h1, -, -⟩; exact h1
    have htr' : ∀ a, (if xcl then c'.views.xclb.map (·.1) else none) = some a → a ≤ c'.mem.last := by
      intro a ha
      cases xcl
      · cases ha
      · simp only [↓reduceIte] at ha
        cases hx : c'.views.xclb with
        | none => rw [hx] at ha; cases ha
        | some p =>
          rw [hx] at ha
          obtain ⟨a0, b0, l0⟩ := p
          simp only [Option.map_some, Option.some.injEq] at ha
          subst ha
          exact (hs.bnd.views.xclb _ _ _ hx).1
    simp only [runTree, List.mem_append] at h ⊢
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨hp, c0, hc0, h⟩ := h
      have hivs : (iv.forStore c.stores).Rel M.last (iv'.forStore c'.stores) := hs.rel.stores ▸ hiv.forStore c.stores
      obtain ⟨c0', hc0', hsim⟩ := writeSuccs_sim A tid hs hivs (hiv'.forStore c'.stores) htr htr' (VR.refl _ 0)
        (Nat.zero_le _) hc0 (VR.ite hs.rel.views.xclb.xclRead (VR.refl _ _))
      have hs0 := writeSuccs_silent A tid _ hf hc0
      have hl := (writeSuccs_bnd A tid _ hs.bnd (hiv'.forStore c'.stores) (Nat.zero_le _) hc0').2
      obtain ⟨c2', h', hs'⟩ := ih true c0 c0' s c2 hsim (hiv'.mono hl) hs0.fwd h hb
      refine ⟨c2', Or.inl ?_, hs'⟩
      rw [List.mem_ite_nil_left, List.mem_flatMap]
      refine ⟨?_, c0', hc0', h'⟩
      have hx := hv.xclb
      revert hp hx
      generalize c.views.xclb = a
      generalize c'.views.xclb = b
      rcases a with _ | ⟨a1, a2, l1⟩ <;> rcases b with _ | ⟨b1, b2, l2⟩ <;> intro hp hx
      · exact hp
      · exact (hx : False).elim
      · exact (hx : False).elim
      · obtain ⟨-, -, rfl⟩ := hx; exact hp
    · rw [List.mem_ite_nil_right] at h
      have hsim : Ctx.Sim M tid
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }
          { c' with views := { c'.views with xclb := none }, succView := 0, log := c'.log ++ [.xclFail l] } :=
        hs.congr hv.xclbNone (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl
          (VR.refl _ _) hs.rel.rmwWrote hs.rel.stores ⟨hs.bnd.views.xclbNone, hs.bnd.loadViews, Nat.zero_le _⟩
      have := ih false _ _ s c2 hsim hiv' hf h.2 hb
      obtain ⟨c2', h', hs'⟩ := this
      refine ⟨c2', Or.inr ?_, hs'⟩
      rw [List.mem_ite_nil_right]
      exact ⟨h.1, h'⟩
  | fence k ret ih =>
    intro c c' s c2 hs hiv' hf h hb
    simp only [runTree] at h ⊢
    exact ih () _ _ s c2 (fenceStep_sim hs k) (by rw [fenceStep_mem]; exact hiv')
      (Ctx.Silent.fenceStep hf k).fwd h hb
  | rmw k noRet l op ret ih =>
    intro c c' s c2 hs hiv' hf h hb
    simp only [runTree] at h ⊢
    have hs1 := fenceOpt_sim hs A.rmwFence .sy
    have hf1 := (Ctx.Silent.fenceOpt hf A.rmwFence .sy).fwd
    have hm1 : (if A.rmwFence then fenceStep c' .sy else c').mem = c'.mem := by
      split <;> simp only [fenceStep_mem]
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h hs1 hf1
    generalize (if A.rmwFence then fenceStep c' .sy else c') = c1' at hs1 hm1 ⊢
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c3⟩, hx, h⟩ := h
    have h2 := readSuccs_silent A iv hf1 hx
    simp only at h
    -- the run after the read ends with `relPre ≤ |M|`
    have hbr : c3.views.relPre ≤ M.last := by
      split at h
      · exact Nat.le_trans ((Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy).trans
          (runTree_silent A tid iv _ _ s c2 (Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy).fwd h)).relPre hb
      · rw [List.mem_flatMap] at h
        obtain ⟨c4, hc4, h⟩ := h
        change .ok (s, c2) ∈ runTree A tid iv
          (if A.rmwFence then fenceStep (rmwPost A k noRet l c4) .sy else rmwPost A k noRet l c4) (ret old) at h
        have h3 := writeSuccs_silent A tid iv h2.fwd hc4
        have h4 := h3.trans (Ctx.Silent.rmwPost h3.fwd A k noRet l)
        have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
        exact Nat.le_trans (h5.trans (runTree_silent A tid iv _ _ s c2 h5.fwd h)).relPre hb
    obtain ⟨⟨tr', old', c3'⟩, hx', hv, htr, htrl, hsim⟩ := readSuccs_sim A tid hs1 hiv (hm1 ▸ hiv') hx hbr
    simp only at hv htr htrl
    have hm3 : c3'.mem = c1'.mem := (readSuccs_mp A iv' hx').1
    split at h
    · rename_i hop
      obtain ⟨c2', h', hs'⟩ := ih old _ _ s c2 (fenceOpt_sim hsim A.rmwFence .sy)
        (by split <;> simp only [fenceStep_mem, hm3, hm1] <;> exact hiv')
        (Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy).fwd h hb
      refine ⟨c2', List.mem_flatMap.mpr ⟨(tr', old', c3'), hx', ?_⟩, hs'⟩
      simp only [hv, hop]
      exact h'
    · rename_i new hop
      rw [List.mem_flatMap] at h
      obtain ⟨c4, hc4, h⟩ := h
      change .ok (s, c2) ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c4) .sy else rmwPost A k noRet l c4) (ret old) at h
      have hiv3 : iv'.Le c3'.mem.last := by rw [hm3, hm1]; exact hiv'
      obtain ⟨c4', hc4', hsim4⟩ := writeSuccs_sim A tid hsim hiv hiv3 (tr := some tr) (tr' := some tr') htr
        (fun a ha => by cases ha; rw [hm3]; exact htrl) (clampL_getLastD hsim.rel.loadViews)
        (getLastD_le hsim.bnd.loadViews 0 (Nat.zero_le _)) hc4 (VR.refl _ _)
      have h3 := writeSuccs_silent A tid iv h2.fwd hc4
      have h4 := h3.trans (Ctx.Silent.rmwPost h3.fwd A k noRet l)
      have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
      have hl := (writeSuccs_bnd A tid iv' hsim.bnd hiv3 (getLastD_le hsim.bnd.loadViews 0 (Nat.zero_le _)) hc4').2
      have hm5 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c4') .sy else rmwPost A k noRet l c4').mem =
          c4'.mem := by
        split <;> simp only [fenceStep_mem, rmwPost_mem]
      obtain ⟨c2', h', hs'⟩ := ih old _ _ s c2 (fenceOpt_sim (rmwPost_sim A hsim4 k noRet l) A.rmwFence .sy)
        (by rw [hm5]; exact hiv3.mono hl) h5.fwd h hb
      refine ⟨c2', List.mem_flatMap.mpr ⟨(tr', old', c3'), hx', ?_⟩, hs'⟩
      simp only [hv, hop, List.mem_flatMap]
      exact ⟨c4', hc4', h'⟩

end Rules

/-! ### Threads -/

/-- Two threads agreeing up to clamping; the replay holds exactly the real
promises at most `m`. -/
structure Thread.Rel (m : Nat) (t t' : Thread I) : Prop where
  st : t.st = t'.st
  rview : t.rview.map (min · (m + 1)) = t'.rview.map (min · (m + 1))
  wview : t.wview.map (min · (m + 1)) = t'.wview.map (min · (m + 1))
  views : t.views.Rel m t'.views
  prom : t'.prom = t.prom.filter (· ≤ m)

theorem arr_get_vr {m : Nat} {a b : Array View} (h : a.map (min · (m + 1)) = b.map (min · (m + 1))) (i : Nat) :
    VR m a[i]! b[i]! := by
  have hi := congrArg (·[i]?) h
  simp only [Array.getElem?_map] at hi
  simp only [VR, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  cases ha : a[i]? <;> cases hb : b[i]? <;> rw [ha, hb] at hi <;> simp_all

theorem Thread.Rel.rviewOf {m : Nat} {t t' : Thread I} (h : t.Rel m t') (r : I.RegId) :
    VR m (t.rviewOf r) (t'.rviewOf r) := arr_get_vr h.rview _

theorem Thread.Rel.wviewOf {m : Nat} {t t' : Thread I} (h : t.Rel m t') (r : I.RegId) :
    VR m (t.wviewOf r) (t'.wviewOf r) := arr_get_vr h.wview _

theorem Thread.Rel.setRegView {m : Nat} {t t' : Thread I} (h : t.Rel m t') (r : I.RegId) {rv rv' wv wv' : View}
    (hr : VR m rv rv') (hw : VR m wv wv') : (t.setRegView r rv wv).Rel m (t'.setRegView r rv' wv') := by
  refine ⟨h.st, ?_, ?_, h.views, h.prom⟩
  · simp only [Thread.setRegView, Array.set!_eq_setIfInBounds, Array.map_setIfInBounds]
    rw [h.rview, show min rv (m + 1) = min rv' (m + 1) from hr]
  · simp only [Thread.setRegView, Array.set!_eq_setIfInBounds, Array.map_setIfInBounds]
    rw [h.wview, show min wv (m + 1) = min wv' (m + 1) from hw]

private theorem foldl_rel {α β γ : Type} (R : β → γ → Prop) (f : β → α → β) (g : γ → α → γ)
    (hf : ∀ b c x, R b c → R (f b x) (g c x)) : ∀ (xs : List α) (b : β) (c : γ), R b c → R (xs.foldl f b) (xs.foldl g c)
  | [], _, _, h => h
  | x :: xs, b, c, h => foldl_rel R f g hf xs (f b x) (g c x) (hf b c x h)

theorem joinViews_vr {m : Nat} {t t' : Thread I} (h : t.Rel m t') (rs : List I.RegId) :
    VR m (t.joinViews rs).1 (t'.joinViews rs).1 ∧ VR m (t.joinViews rs).2 (t'.joinViews rs).2 := by
  unfold Thread.joinViews
  apply foldl_rel (fun (a b : View × View) => VR m a.1 b.1 ∧ VR m a.2 b.2)
  · intro a b x hab
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    exact ⟨hab.1.max (h.rviewOf x), hab.2.max (h.wviewOf x)⟩
  · exact ⟨rfl, rfl⟩

theorem instrViews_rel {m : Nat} {t t' : Thread I} (h : t.Rel m t') (d : InstrDeps I.RegId) :
    (instrViews t d).Rel m (instrViews t' d) := by
  have ha := joinViews_vr h d.addrRegs
  have hd := joinViews_vr h d.dataRegs
  have hc := joinViews_vr h d.condRegs
  have hdv : VR m (if d.dataRegsPer.isEmpty = true then t.joinViews d.dataRegs else (0, 0)).1
      (if d.dataRegsPer.isEmpty = true then t'.joinViews d.dataRegs else (0, 0)).1 ∧
      VR m (if d.dataRegsPer.isEmpty = true then t.joinViews d.dataRegs else (0, 0)).2
      (if d.dataRegsPer.isEmpty = true then t'.joinViews d.dataRegs else (0, 0)).2 := by
    split
    · exact hd
    · exact ⟨rfl, rfl⟩
  refine ⟨ha.1, ha.2, hdv.1, hdv.2, hc.2, ?_⟩
  show (d.dataRegsPer.map t.joinViews).map _ = (d.dataRegsPer.map t'.joinViews).map _
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro rs _
  have := joinViews_vr h rs
  simp only [Function.comp, Prod.mk.injEq]
  exact ⟨this.1, this.2⟩

theorem clampL_length {m : Nat} {xs ys : List View} (h : clampL m xs = clampL m ys) : xs.length = ys.length := by
  have := congrArg List.length h
  simpa [clampL] using this

theorem clampL_foldl_max {m : Nat} : ∀ {xs ys : List View}, clampL m xs = clampL m ys → ∀ a b, VR m a b →
    VR m (xs.foldl max a) (ys.foldl max b)
  | [], [], _, _, _, h => h
  | [], _ :: _, h, _, _, _ => by simp [clampL] at h
  | _ :: _, [], h, _, _, _ => by simp [clampL] at h
  | x :: xs, y :: ys, h, a, b, hab => by
    simp only [clampL, List.map_cons, List.cons.injEq] at h
    exact clampL_foldl_max h.2 _ _ (hab.max h.1)

theorem zip_fold_rel {m : Nat} : ∀ (rs : List I.RegId) (xs ys : List View) (a b : Thread I),
    clampL m xs = clampL m ys → a.Rel m b →
    ((rs.zip xs).foldl (fun t (rv : I.RegId × View) => t.setRegView rv.1 rv.2 rv.2) a).Rel m
      ((rs.zip ys).foldl (fun t (rv : I.RegId × View) => t.setRegView rv.1 rv.2 rv.2) b)
  | [], _, _, _, _, _, hab => by simpa using hab
  | _ :: _, [], [], _, _, _, hab => by simpa using hab
  | _ :: _, [], _ :: _, _, _, h, _ => by simp [clampL] at h
  | _ :: _, _ :: _, [], _, _, h, _ => by simp [clampL] at h
  | r :: rs, x :: xs, y :: ys, a, b, h, hab => by
    simp only [clampL, List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.foldl_cons]
    exact zip_fold_rel rs xs ys _ _ h.2 (hab.setRegView r h.1 h.1)

/-- `finishInstr` on related threads, contexts and instruction views. -/
theorem finishInstr_rel {m : Nat} {t t' : Thread I} {d : InstrDeps I.RegId} {iv iv' : InstrViews} {st : I.State}
    {c c' : Ctx} (h : t.Rel m t') (hc : c.Rel m c') (hiv : iv.Rel m iv') :
    ∀ th ∈ finishInstr t d iv st c, ∃ th' ∈ finishInstr t' d iv' st c', th.Rel m th' := by
  intro th hth
  have hload := clampL_foldl_max hc.loadViews 0 0 (VR.refl _ _)
  have hlen : (d.loadDefs.length == c.loadViews.length) = (d.loadDefs.length == c'.loadViews.length) := by
    rw [clampL_length hc.loadViews]
  have hinR : VR m (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW)
      (if d.isPick then max iv'.addrR iv'.dataR else max (max iv'.addrR iv'.dataR) iv'.condW) :=
    VR.ite (hiv.addrR.max hiv.dataR) ((hiv.addrR.max hiv.dataR).max hiv.condW)
  have hinW := (hiv.addrW.max hiv.dataW).max hiv.condW
  have h1 : Thread.Rel m { t with st, views := c.views, prom := c.prom } { t' with st, views := c'.views, prom := c'.prom } :=
    ⟨rfl, h.rview, h.wview, hc.views, hc.prom⟩
  have h2 : Thread.Rel m
      (d.statusDefs.foldl (fun t r => t.setRegView r c.succView c.succView)
        (d.defs.foldl (fun t r => t.setRegView r
          (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW)
          (max (max iv.addrW iv.dataW) iv.condW)) { t with st, views := c.views, prom := c.prom }))
      (d.statusDefs.foldl (fun t r => t.setRegView r c'.succView c'.succView)
        (d.defs.foldl (fun t r => t.setRegView r
          (if d.isPick then max iv'.addrR iv'.dataR else max (max iv'.addrR iv'.dataR) iv'.condW)
          (max (max iv'.addrW iv'.dataW) iv'.condW)) { t' with st, views := c'.views, prom := c'.prom })) := by
    apply foldl_rel (Thread.Rel m)
    · intro a b x hab; exact hab.setRegView x hc.succView hc.succView
    · apply foldl_rel (Thread.Rel m) _ _ _ _ _ _ h1
      intro a b x hab; exact hab.setRegView x hinR hinW
  have finish : ∀ a b : Thread I, a.Rel m b →
      Thread.Rel m (if d.isBranch then { a with views := { a.views with vCAP := max a.views.vCAP iv.condW } } else a)
        (if d.isBranch then { b with views := { b.views with vCAP := max b.views.vCAP iv'.condW } } else b) := by
    intro a b hab
    split
    · exact ⟨hab.st, hab.rview, hab.wview, hab.views.setVCAP (hab.views.vCAP.max hiv.condW), hab.prom⟩
    · exact hab
  have h3 : ∀ a b : Thread I, a.Rel m b → Thread.Rel m
      (if d.loadDefs.length == c.loadViews.length then
        (d.loadDefs.zip c.loadViews).foldl (fun t (r, v) => t.setRegView r v v) a
      else d.loadDefs.foldl (fun t r => t.setRegView r (c.loadViews.foldl max 0) (c.loadViews.foldl max 0)) a)
      (if d.loadDefs.length == c'.loadViews.length then
        (d.loadDefs.zip c'.loadViews).foldl (fun t (r, v) => t.setRegView r v v) b
      else d.loadDefs.foldl (fun t r => t.setRegView r (c'.loadViews.foldl max 0) (c'.loadViews.foldl max 0)) b) := by
    intro a b hab
    rw [← hlen]
    split
    · exact zip_fold_rel _ _ _ _ _ hc.loadViews hab
    · apply foldl_rel (Thread.Rel m) _ _ _ _ _ _ hab
      intro a b x hab; exact hab.setRegView x hload hload
  have h4 : ∀ a b : Thread I, a.Rel m b → Thread.Rel m
      (d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r) (max (t.wviewOf r) (c.loadViews.foldl max 0))) a)
      (d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r) (max (t.wviewOf r) (c'.loadViews.foldl max 0))) b) := by
    intro a b hab
    apply foldl_rel (Thread.Rel m) _ _ _ _ _ _ hab
    intro a b x hab; exact hab.setRegView x (hab.rviewOf x) ((hab.wviewOf x).max hload)
  simp only [finishInstr] at hth ⊢
  rw [← hc.rmwWrote]
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

/-! ### One instruction, replayed -/

/-- The real thread `t` against `mem` and the replay thread `t'` against
`mem'`, both memories extending `M`: the thread-level form of `Ctx.Sim`. -/
structure Thread.Sim (M : Memory) (tid : Nat) (t : Thread I) (mem : Memory) (t' : Thread I) (mem' : Memory) :
    Prop where
  rel : t.Rel M.last t'
  memR : M.Prefix mem
  memP : M.Prefix mem'
  own : OwnAbove' tid M.last t'.views mem'
  bnd : t'.Bnd mem'.last
  ntcoh : NtCoh M.last t.views mem t'.views mem'
  fwdcoh : FwdCoh M.last t.views

theorem Views.getCoh_congr {a b : Views} (h : ({ a with vCAP := 0 } : Views) = { b with vCAP := 0 }) (l : Loc) :
    a.getCoh l = b.getCoh l := by
  have h1 := congrArg Views.coh h
  simp only at h1
  simp only [Views.getCoh, h1]

theorem Views.getFwd_congr {a b : Views} (h : ({ a with vCAP := 0 } : Views) = { b with vCAP := 0 }) (l : Loc) :
    a.getFwd l = b.getFwd l := by
  have h1 := congrArg Views.fwdb h
  simp only at h1
  simp only [Views.getFwd, h1]

/-- **One instruction, replayed.** An instruction of the real thread that
ends with `relPre ≤ |M|` is matched by an instruction of the replay thread,
ending in simulating threads. -/
theorem stepOne_sim (A : Arch) {M : Memory} {tid : Nat} {t t' : Thread I} {mem mem' : Memory}
    (hs : Thread.Sim M tid t mem t' mem') (hf : t.views.FwdOk)
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hb : o.thread.views.relPre ≤ M.last) :
    ∃ outs' o', stepOne A t' tid mem' = some outs' ∧ .ok o' ∈ outs' ∧
      Thread.Sim M tid o.thread o.mem o'.thread o'.mem := by
  unfold stepOne at hstep ⊢
  rw [← hs.rel.st]
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
      obtain ⟨-, hv⟩ := finishInstr_relKey hth
      have hb2 : c2.views.relPre ≤ M.last := (Views.relPre_congr hv).1 ▸ hb
      have hiv := instrViews_rel hs.rel (I.deps t.st)
      have hiv' := instrViews_le hs.bnd.regs (I.deps t.st)
      have hc : Ctx.Sim M tid { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }
          { views := t'.views, prom := t'.prom, mem := mem', log := [.instr tid (I.showInstr t.st)] } :=
        ⟨⟨hs.rel.views, hs.rel.prom, rfl, VR.refl _ _, rfl, rfl⟩, hs.memR, hs.memP, hs.own,
          ⟨hs.bnd.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩, hs.ntcoh, hs.fwdcoh⟩
      obtain ⟨c2', hr', hs2⟩ := runTree_sim A tid hiv tree _ _ st c2 hc hiv' hf hr hb2
      obtain ⟨hcb, hl⟩ := runTree_bnd A tid _ tree _ st c2' hc.bnd hiv' hr'
      obtain ⟨th', hth', hrel⟩ := finishInstr_rel hs.rel hs2.rel hiv th hth
      obtain ⟨-, hv'⟩ := finishInstr_relKey hth'
      refine ⟨_, _, rfl, List.mem_flatMap.mpr ⟨.ok (st, c2'), hr', List.mem_map.mpr ⟨th', hth', rfl⟩⟩, ?_⟩
      have e1 := Views.getCoh_congr hv
      have e2 := Views.getFwd_congr hv
      have e1' := Views.getCoh_congr hv'
      have e2' := Views.getFwd_congr hv'
      refine ⟨hrel, hs2.memR, hs2.memP, ?_, ?_, ?_, ?_⟩
      · exact hs2.own.mono (fun l => Nat.le_of_eq (e1' l).symm)
      · exact finishInstr_bnd hcb.views hcb.loadViews hcb.succView (hiv'.mono hl) (hs.bnd.regs.mono hl) th' hth'
      · exact NtCoh.congr hs2.ntcoh (fun l _ => ⟨e1 l, e1' l⟩) e2 e2'
      · exact FwdCoh.congr hs2.fwdcoh e2 (fun l => Nat.le_of_eq (e1 l).symm)

theorem Memory.le_last_of_get? {mem : Memory} {u : Time} {w : Msg} (h : mem.get? u = some w) : u ≤ mem.last := by
  rcases Nat.lt_or_ge mem.last u with hu | hu
  · rw [Memory.get?_eq_none_of_last_lt mem hu] at h; cases h
  · exact hu

theorem NtCoh.grow {m : Nat} {vs vs' : Views} {mem mem2 mem' : Memory} (h : NtCoh m vs mem vs' mem')
    (hm : mem.Prefix mem2) : NtCoh m vs mem2 vs' mem' := by
  intro l hl
  obtain ⟨a, b, w, w', hw, hw', hrest⟩ := h l hl
  exact ⟨a, b, w, w', by rw [hm.get? (Memory.le_last_of_get? hw)]; exact hw, hw', hrest⟩

/-- Other threads extend the real memory. -/
theorem Thread.Sim.grow {M : Memory} {tid : Nat} {t t' : Thread I} {mem mem2 mem' : Memory}
    (hs : Thread.Sim M tid t mem t' mem') (hm : mem.Prefix mem2) : Thread.Sim M tid t mem2 t' mem' :=
  ⟨hs.rel, hs.memR.trans hm, hs.memP, hs.own, hs.bnd, hs.ntcoh.grow hm, hs.fwdcoh⟩

/-- The real thread promises above `|M|`: the replay ignores it. -/
theorem Thread.Sim.promise {M : Memory} {tid : Nat} {t t' : Thread I} {mem mem2 mem' : Memory}
    (hs : Thread.Sim M tid t mem t' mem') (hm : mem.Prefix mem2) {p : Time} (hp : M.last < p) :
    Thread.Sim M tid { t with prom := t.prom ++ [p] } mem2 t' mem' := by
  refine ⟨⟨hs.rel.st, hs.rel.rview, hs.rel.wview, hs.rel.views, ?_⟩, hs.memR.trans hm, hs.memP, hs.own, hs.bnd,
    hs.ntcoh.grow hm, hs.fwdcoh⟩
  show t'.prom = (t.prom ++ [p]).filter _
  rw [List.filter_append, hs.rel.prom]
  have : ¬ p ≤ M.last := by omega_t
  simp [this]

/-- **(S1′) on machine paths, with pending non-temporal stores.** Fix a
memory `M`, a thread state `t0`, and a path to `c1` along which thread `tid`
ends in a state `t1` bounded by `M` (`relPre ≤ |M|`). If, at some
configuration on the path, the thread's state `tm` is simulated by a state
`tr` reachable from `(t0, M)` by a promise-free run of the thread alone, then
so is `t1`. Other threads, and the thread's own promises, only extend the
real memory; the thread's own instructions on the path are bounded by `M` and
replay (`stepOne_sim`), with any non-temporal write above `|M|` replayed as a
fresh write of the replay run. -/
theorem advanceNT_path {A : Arch} {M : Memory} {tid : Nat} {t0 : Thread I}
    {c1 : Config I} {t1 : Thread I} (ht1 : c1.threads[tid]? = some t1) (hb : t1.views.relPre ≤ M.last)
    {c : Config I} (hr : ReachableK A c c1) (hwf : c.Wf) {tm : Thread I}
    (htm : c.threads[tid]? = some tm) {tr : Thread I} {Mr : Memory}
    (hnp : ThreadNP A tid (t0, M) (tr, Mr)) (hs : Thread.Sim M tid tm c.mem tr Mr) :
    ∃ t1' M1, ThreadNP A tid (t0, M) (t1', M1) ∧ Thread.Sim M tid t1 c1.mem t1' M1 := by
  induction hr generalizing tm tr Mr with
  | refl => rw [ht1] at htm; cases htm; exact ⟨tr, Mr, hnp, hs⟩
  | @step c c' c'' hs' hr' ih =>
    have hwf' := hwf.succ hs'
    have hlt := lt_size_of_get? htm
    cases hs' with
    | @instr j tj outs o hj hstep ho =>
      by_cases hij : j = tid
      · subst hij
        rw [htm] at hj; cases hj
        have h1 : (c.withThread j o.thread o.mem).threads[j]? = some o.thread := by
          simp only [Config.withThread_get? c _ _ hlt, ↓reduceIte]
        obtain ⟨t', h', hle⟩ := hr'.relPre_mono hwf' h1
        rw [ht1] at h'; cases h'
        obtain ⟨outs', o', hstep', ho', hs2⟩ :=
          stepOne_sim A hs (hwf j tm htm).1 hstep ho (Nat.le_trans hle hb)
        exact ih ht1 hwf' h1 (hnp.tail ⟨outs', _, hstep', ho', rfl⟩) hs2
      · have h1 : (c.withThread j o.thread o.mem).threads[tid]? = some tm := by
          simp only [Config.withThread_get? c _ _ (lt_size_of_get? hj), hij, ↓reduceIte, htm]
        exact ih ht1 hwf' h1 hnp (hs.grow (Memory.Prefix.stepOne hstep ho))
    | @promise j tj p hj _ =>
      have hM' : c.mem.Prefix (c.mem.append { p.1 with tid := j }).1 := Memory.Prefix.append _ _
      by_cases hij : j = tid
      · subst hij
        rw [htm] at hj; cases hj
        have h1 := (Config.withThread_get? c (i := j) { tm with prom := tm.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 hlt)
        simp only [↓reduceIte] at h1
        refine ih ht1 hwf' h1 hnp (hs.promise hM' ?_)
        have := hs.memR.last_le; simp only [Memory.append, Memory.last] at this ⊢; omega_t
      · have h1 := (Config.withThread_get? c (i := tid) { tj with prom := tj.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 (lt_size_of_get? hj))
        simp only [hij, ↓reduceIte, htm] at h1
        exact ih ht1 hwf' h1 hnp (hs.grow hM')

/-- The initial contexts of an instruction of simulating threads. -/
theorem Thread.Sim.ctx {M : Memory} {tid : Nat} {t t' : Thread I} {mem mem' : Memory}
    (hs : Thread.Sim M tid t mem t' mem') (log : List TraceEv) :
    Ctx.Sim M tid { views := t.views, prom := t.prom, mem, log } { views := t'.views, prom := t'.prom, mem := mem', log } :=
  ⟨⟨hs.rel.views, hs.rel.prom, rfl, VR.refl _ _, rfl, rfl⟩, hs.memR, hs.memP, hs.own,
    ⟨hs.bnd.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩, hs.ntcoh, hs.fwdcoh⟩

section Rules

variable (A : Arch) (tid : Nat)

/-- **The release fulfilment, replayed.** A run of the event tree from the
real context that fulfils `ts ≤ |M|` with a release store is matched by one
from the replay context. Every context on the run has `relPre < ts`
(`EvTree.RelFulfils.relPre_lt`), so the replay applies; the replay holds `ts`
(it is at most `|M|`) and gives it up exactly when the real run does. -/
theorem EvTree.RelFulfils.sim {σ : Type} {M : Memory} {iv iv' : InstrViews} {ts : Time} (hiv : iv.Rel M.last iv')
    (hts : ts ≤ M.last) (tree : EvTree σ) :
    ∀ (c c' : Ctx), c.Sim M tid c' → iv'.Le c'.mem.last → c.views.FwdOk →
      EvTree.RelFulfils A tid iv ts c tree → EvTree.RelFulfils A tid iv' ts c' tree := by
  have fulfil : ∀ {c c' c2 c2' : Ctx}, c.Sim M tid c' → c2.Sim M tid c2' → ts ∈ c.prom → ts ∉ c2.prom →
      ts ∈ c'.prom ∧ ts ∉ c2'.prom := by
    intro c c' c2 c2' hs hs2 hin hout
    refine ⟨by rw [hs.rel.prom]; exact List.mem_filter.mpr ⟨hin, by simpa using hts⟩, ?_⟩
    rw [hs2.rel.prom]; exact fun h => hout (List.mem_filter.mp h).1
  have hlt : ∀ {x : Nat}, x < ts → x ≤ M.last := fun h => Nat.le_of_lt (Nat.lt_of_lt_of_le h hts)
  induction tree with
  | done s0 => intro c c' _ _ _ h; exact h.elim
  | fault msg => intro c c' _ _ _ h; exact h.elim
  | choose n k ih =>
    intro c c' hs hiv' hf h
    obtain ⟨i, h⟩ := h
    exact ⟨i, ih i c c' hs hiv' hf h⟩
  | load k xcl l ret ih =>
    intro c c' hs hiv' hf h
    obtain ⟨⟨t, v, c0⟩, hx, h⟩ := h
    have hs0 := readSuccs_silent A iv hf hx
    have hb := EvTree.RelFulfils.relPre_lt A tid iv _ c0 hs0.fwd h
    obtain ⟨⟨t', v', c0'⟩, hx', hv, -, -, hsim⟩ := readSuccs_sim A tid hs hiv hiv' hx (hlt hb)
    simp only at hv
    have hm0 : c0'.mem = c'.mem := (readSuccs_mp A iv' hx').1
    refine ⟨(t', v', c0'), hx', ?_⟩
    show EvTree.RelFulfils A tid iv' ts c0' (ret v')
    rw [hv]
    exact ih v c0 c0' hsim (hm0 ▸ hiv') hs0.fwd h
  | store k xcl l v ret ih =>
    intro c c' hs hiv' hf h
    have hv := hs.rel.views
    have htr : OptR M.last (if xcl then c.views.xclb.map (·.1) else none)
        (if xcl then c'.views.xclb.map (·.1) else none) := by
      cases xcl
      · trivial
      · have hx := hv.xclb
        revert hx
        rcases c.views.xclb with _ | ⟨a, b, l1⟩ <;> rcases c'.views.xclb with _ | ⟨a', b', l2⟩ <;>
          simp only [XclbR, OptR, Option.map, imp_self, ↓reduceIte]
        rintro ⟨h1, -, -⟩; exact h1
    have htr' : ∀ a, (if xcl then c'.views.xclb.map (·.1) else none) = some a → a ≤ c'.mem.last := by
      intro a ha
      cases xcl
      · cases ha
      · simp only [↓reduceIte] at ha
        cases hx : c'.views.xclb with
        | none => rw [hx] at ha; cases ha
        | some p =>
          rw [hx] at ha
          obtain ⟨a0, b0, l0⟩ := p
          simp only [Option.map_some, Option.some.injEq] at ha
          subst ha
          exact (hs.bnd.views.xclb _ _ _ hx).1
    rcases h with ⟨c0, hc0, h⟩ | h
    · have hivs : (iv.forStore c.stores).Rel M.last (iv'.forStore c'.stores) := hs.rel.stores ▸ hiv.forStore c.stores
      obtain ⟨c0', hc0', hsim⟩ := writeSuccs_sim A tid hs hivs (hiv'.forStore c'.stores) htr htr' (VR.refl _ 0)
        (Nat.zero_le _) hc0 (VR.ite hs.rel.views.xclb.xclRead (VR.refl _ _))
      refine Or.inl ⟨c0', hc0', ?_⟩
      rcases h with ⟨hk, hin, hout⟩ | h
      · exact Or.inl ⟨hk, fulfil hs hsim hin hout⟩
      · have hs0 := writeSuccs_silent A tid _ hf hc0
        have hl := (writeSuccs_bnd A tid _ hs.bnd (hiv'.forStore c'.stores) (Nat.zero_le _) hc0').2
        exact Or.inr (ih true c0 c0' hsim (hiv'.mono hl) hs0.fwd h)
    · have hsim : Ctx.Sim M tid
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }
          { c' with views := { c'.views with xclb := none }, succView := 0, log := c'.log ++ [.xclFail l] } :=
        hs.congr hv.xclbNone (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl rfl rfl
          (VR.refl _ _) hs.rel.rmwWrote hs.rel.stores ⟨hs.bnd.views.xclbNone, hs.bnd.loadViews, Nat.zero_le _⟩
      exact Or.inr (ih false _ _ hsim hiv' hf h)
  | fence k ret ih =>
    intro c c' hs hiv' hf h
    exact ih () _ _ (fenceStep_sim hs k) (by rw [fenceStep_mem]; exact hiv') (Ctx.Silent.fenceStep hf k).fwd h
  | rmw k noRet l op ret ih =>
    intro c c' hs hiv' hf h
    have hs1 := fenceOpt_sim hs A.rmwFence .sy
    have hf1 := (Ctx.Silent.fenceOpt hf A.rmwFence .sy).fwd
    have hm1 : (if A.rmwFence then fenceStep c' .sy else c').mem = c'.mem := by
      split <;> simp only [fenceStep_mem]
    obtain ⟨⟨tr, old, c3⟩, hx, h⟩ := h
    show ∃ x ∈ readSuccs A iv' (if A.rmwFence then fenceStep c' .sy else c')
        (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      EvTree.RelFulfils A tid iv' ts (if A.rmwFence then fenceStep x.2.2 .sy else x.2.2) (ret x.2.1) ∨
      ∃ new, op x.2.1 = some new ∧
        ∃ c4 ∈ writeSuccs A tid iv' x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
          (A.storeKind (A.rmwKind k).storeKind = .rel ∧ ts ∈ x.2.2.prom ∧ ts ∉ c4.prom) ∨
          EvTree.RelFulfils A tid iv' ts
            (if A.rmwFence then fenceStep (rmwPost A k noRet l c4) .sy else rmwPost A k noRet l c4) (ret x.2.1)
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at hx hs1 hf1
    generalize (if A.rmwFence then fenceStep c' .sy else c') = c1' at hs1 hm1 ⊢
    have h2 := readSuccs_silent A iv hf1 hx
    simp only at h
    have hbr : c3.views.relPre ≤ M.last := by
      refine hlt ?_
      rcases h with h | ⟨new, hop, c4, hc4, ⟨hk, hin, hout⟩ | h⟩
      · exact Nat.lt_of_le_of_lt (Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy).relPre
          (EvTree.RelFulfils.relPre_lt A tid iv _ _ (Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy).fwd h)
      · exact writeSuccs_rel_relPre A tid iv hc4 hk hin hout
      · have h3 := writeSuccs_silent A tid iv h2.fwd hc4
        have h4 := h3.trans (Ctx.Silent.rmwPost h3.fwd A k noRet l)
        have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
        exact Nat.lt_of_le_of_lt h5.relPre (EvTree.RelFulfils.relPre_lt A tid iv _ _ h5.fwd h)
    obtain ⟨⟨tr', old', c3'⟩, hx', hv, htr, htrl, hsim⟩ := readSuccs_sim A tid hs1 hiv (hm1 ▸ hiv') hx hbr
    simp only at hv htr htrl
    have hm3 : c3'.mem = c1'.mem := (readSuccs_mp A iv' hx').1
    refine ⟨(tr', old', c3'), hx', ?_⟩
    simp only [hv]
    rcases h with h | ⟨new, hop, c4, hc4, h⟩
    · exact Or.inl (ih old _ _ (fenceOpt_sim hsim A.rmwFence .sy)
        (by split <;> simp only [fenceStep_mem, hm3, hm1] <;> exact hiv')
        (Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy).fwd h)
    · have hiv3 : iv'.Le c3'.mem.last := by rw [hm3, hm1]; exact hiv'
      obtain ⟨c4', hc4', hsim4⟩ := writeSuccs_sim A tid hsim hiv hiv3 (tr := some tr) (tr' := some tr') htr
        (fun a ha => by cases ha; rw [hm3]; exact htrl) (clampL_getLastD hsim.rel.loadViews)
        (getLastD_le hsim.bnd.loadViews 0 (Nat.zero_le _)) hc4 (VR.refl _ _)
      refine Or.inr ⟨new, hop, c4', hc4', ?_⟩
      rcases h with ⟨hk, hin, hout⟩ | h
      · exact Or.inl ⟨hk, fulfil hsim hsim4 hin hout⟩
      · have h3 := writeSuccs_silent A tid iv h2.fwd hc4
        have h4 := h3.trans (Ctx.Silent.rmwPost h3.fwd A k noRet l)
        have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
        have hl := (writeSuccs_bnd A tid iv' hsim.bnd hiv3 (getLastD_le hsim.bnd.loadViews 0 (Nat.zero_le _)) hc4').2
        have hm5 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c4') .sy else rmwPost A k noRet l c4').mem =
            c4'.mem := by
          split <;> simp only [fenceStep_mem, rmwPost_mem]
        exact Or.inr (ih old _ _ (fenceOpt_sim (rmwPost_sim A hsim4 k noRet l) A.rmwFence .sy)
          (by rw [hm5]; exact hiv3.mono hl) h5.fwd h)

end Rules

theorem Thread.RelFulfils.sim {A : Arch} {tid : Nat} {ts : Time} {M : Memory} {t t' : Thread I} {mem mem' : Memory}
    (hs : Thread.Sim M tid t mem t' mem') (hf : t.views.FwdOk) (hts : ts ≤ M.last) (h : t.RelFulfils A tid ts mem) :
    t'.RelFulfils A tid ts mem' := by
  obtain ⟨tree, hex, h⟩ := h
  refine ⟨tree, hs.rel.st ▸ hex, ?_⟩
  rw [← hs.rel.st]
  exact EvTree.RelFulfils.sim A tid (instrViews_rel hs.rel _) hts tree _ _ (hs.ctx _)
    (instrViews_le hs.bnd.regs _) hf h

/-- (S1′) with pending non-temporal stores: as `Config.Advanceable`, but the
thread's promise-free run may append its own messages above `|c.mem|` (its
non-temporal writes, which a later release store does not wait for, replayed
as fresh writes), and the release fulfilment is against the run's final
memory `M'`. Every message of `M'` above `|c.mem|` is the thread's own. -/
def Config.AdvanceableNT (A : Arch) (c : Config I) (tid : Nat) (ts : Time) : Prop :=
  ∃ t t' M', c.threads[tid]? = some t ∧ ts ∈ t.prom ∧ ThreadNP A tid (t, c.mem) (t', M') ∧ ts ∈ t'.prom ∧
    t'.RelFulfils A tid ts M' ∧ c.mem.Prefix M' ∧ ∀ u w, c.mem.last < u → M'.get? u = some w → w.tid = tid

theorem Config.Advanceable.advanceableNT {A : Arch} {c : Config I} {tid : Nat} {ts : Time}
    (h : c.Advanceable A tid ts) : c.AdvanceableNT A tid ts := by
  obtain ⟨t, t', ht, hts, hnp, hts', hrel⟩ := h
  exact ⟨t, t', c.mem, ht, hts, hnp, hts', hrel, .refl _, fun u w hu hw => by
    rw [Memory.get?_eq_none_of_last_lt _ hu] at hw; cases hw⟩

/-- A bounded thread simulates itself against its own memory. -/
theorem Thread.Sim.self {tid : Nat} {t : Thread I} {mem : Memory} (hb : t.Bnd mem.last)
    (hp : ∀ p ∈ t.prom, p ≤ mem.last) : Thread.Sim mem tid t mem t mem := by
  refine ⟨⟨rfl, rfl, rfl, .refl _ _, ?_⟩, .refl _, .refl _, ?_, hb, ?_, ?_⟩
  · exact (List.filter_eq_self.mpr (fun p h => decide_eq_true (hp p h))).symm
  · intro u w hu hw; rw [Memory.get?_eq_none_of_last_lt _ hu] at hw; cases hw
  · intro l hl; exact absurd (hb.views.le.coh l) (Nat.not_le.mpr hl)
  · intro l f hf hl; exact absurd (hb.views.fwdTime l f hf) (Nat.not_le.mpr hl)

/-- **(S1′) for every program, with pending non-temporal stores.** As
`Config.advanceable_of_path`, without the non-temporal restriction: the
thread's promise-free run replays its own instructions on the path, against
`c.mem` extended by its own fresh writes (`advanceNT_path`), and its next
instruction fulfils `ts` with a release store against the run's memory
(`Thread.RelFulfils.sim`). Needs `c0.Bnd` (holds for `Config.init`). -/
theorem Config.advanceableNT_of_path {A : Arch} {c0 c c1 : Config I}
    (h0 : c0.Wf) (hb0 : c0.Bnd) (hc : ReachableK A c0 c) {tid : Nat} {t : Thread I}
    (ht : c.threads[tid]? = some t) {ts : Time} (hts : ts ∈ t.prom) (hr : ReachableK A c c1) {t1 : Thread I}
    (ht1 : c1.threads[tid]? = some t1) (hts1 : ts ∈ t1.prom) (hrel : t1.RelFulfils A tid ts c1.mem) :
    c.AdvanceableNT A tid ts := by
  have hwf := h0.reachable hc
  have hbc := hb0.reachable hc
  have hwf1 := hwf.reachable hr
  have hf1 := (hwf1 tid t1 ht1).1
  have hle : ts ≤ c.mem.last := (hwf tid t ht).2 ts hts
  have hb := hrel.relPre_lt hf1
  obtain ⟨t1', M1, hnp, hs1⟩ := advanceNT_path ht1 (Nat.le_of_lt (Nat.lt_of_lt_of_le hb hle)) hr hwf ht (.refl _)
    (Thread.Sim.self (hbc tid t ht) (hwf tid t ht).2)
  refine ⟨t, t1', M1, ht, hts, hnp, ?_, hrel.sim hs1 hf1 hle, hs1.memP, fun u w hu hw => (hs1.own u w hu hw).1⟩
  rw [hs1.rel.prom]
  exact List.mem_filter.mpr ⟨hts1, by simpa using hle⟩

/-! ### Virtual configurations with pending non-temporal stores -/

/-- A promise-free run of one thread only extends memory. -/
theorem ThreadNP.mem_prefix {A : Arch} {tid : Nat} {p q : Thread I × Memory} (h : ThreadNP A tid p q) :
    p.2.Prefix q.2 := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
    exact (Memory.Prefix.stepOne hstep ho).trans ih

theorem Memory.Prefix.antisymm {M M' : Memory} (h : M.Prefix M') (h' : M'.Prefix M) : M = M' := by
  obtain ⟨hi, hl⟩ := h
  obtain ⟨-, hl'⟩ := h'
  have hm : M.msgs.toList = M'.msgs.toList :=
    List.IsPrefix.eq_of_length hl (Nat.le_antisymm (List.IsPrefix.length_le hl) (List.IsPrefix.length_le hl'))
  have hm' : M.msgs = M'.msgs := Array.toList_inj.mp hm
  cases M; cases M'
  simp_all

/-- `v` is a virtual configuration of `c` with pending non-temporal stores
(design (V), variant (ii), generalised to pending non-temporal stores): as `Config.VirtualOf`, but an
advanced thread's promise-free run may append its own messages (its
non-temporal writes, replayed as fresh writes: `Config.AdvanceableNT`). Each
thread's run ends against a memory `M'` between `c.mem` and `v.mem`; `v.mem`
is `c.mem` or the run memory of a thread advanced to a pending release. Since
a run appends only the thread's own messages, at most one thread's run
appends (two runs' memories are both prefixes of `v.mem`). -/
def Config.VirtualOfNT (A : Arch) (c v : Config I) : Prop :=
  c.mem.Prefix v.mem ∧ v.threads.size = c.threads.size ∧
    (∀ i t, c.threads[i]? = some t → ∃ t' M', v.threads[i]? = some t' ∧ M'.Prefix v.mem ∧
      ThreadNP A i (t, c.mem) (t', M') ∧ ((t' = t ∧ M' = c.mem) ∨ ∃ ts ∈ t'.prom, t'.RelFulfils A i ts M')) ∧
    (v.mem = c.mem ∨ ∃ (i : Nat) (t' : Thread I), v.threads[i]? = some t' ∧ ∃ ts ∈ t'.prom, t'.RelFulfils A i ts v.mem)

theorem Config.VirtualOf.toNT {A : Arch} {c v : Config I} (hv : c.VirtualOf A v) : c.VirtualOfNT A v := by
  obtain ⟨hm, hs, ht⟩ := hv
  refine ⟨hm ▸ .refl _, hs, fun i t hc => ?_, .inl hm⟩
  obtain ⟨t', hv', hr, ho⟩ := ht i t hc
  refine ⟨t', c.mem, hv', hm ▸ .refl _, hr, ?_⟩
  rcases ho with ho | ho
  · exact .inl ⟨ho, rfl⟩
  · exact .inr ho

/-- With memory unchanged, a virtual configuration with pending
non-temporal stores is a `Config.VirtualOf` one. -/
theorem Config.VirtualOfNT.toVirtualOf {A : Arch} {c v : Config I} (hv : c.VirtualOfNT A v)
    (hm : v.mem = c.mem) : c.VirtualOf A v := by
  obtain ⟨-, hs, ht, -⟩ := hv
  refine ⟨hm, hs, fun i t hc => ?_⟩
  obtain ⟨t', M', hv', hM', hr, ho⟩ := ht i t hc
  have hMc : M' = c.mem := (Memory.Prefix.antisymm hr.mem_prefix (hm ▸ hM')).symm
  subst hMc
  refine ⟨t', hv', hr, ?_⟩
  rcases ho with ho | ho
  · exact .inl ho.1
  · exact .inr ho

/-- **In a final configuration the virtual configuration is the real one.** -/
theorem Config.VirtualOfNT.eq_of_final {A : Arch} {c v : Config I} (hf : c.final = true)
    (hv : c.VirtualOfNT A v) : v = c := by
  obtain ⟨-, hs, ht, hm⟩ := hv
  have key : ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → v.threads[i]? = some t ∧ t.prom = [] := by
    intro i t hc
    obtain ⟨t', M', hv', -, hr, -⟩ := ht i t hc
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hc
    have := (Array.all_eq_true.mp hf) i hi
    simp only [Bool.and_eq_true] at this
    have he := ThreadNP.eq_of_halted this.1 hr
    simp only [Prod.mk.injEq] at he
    exact ⟨he.1 ▸ hv', by simpa using this.2⟩
  have hm' : v.mem = c.mem := by
    rcases hm with hm | ⟨i, t', hv', ts, hts, -⟩
    · exact hm
    · exfalso
      have hi : i < c.threads.size := hs ▸ lt_size_of_get? (c := v) hv'
      obtain ⟨h1, h2⟩ := key i _ (Array.getElem?_eq_getElem hi)
      rw [h1] at hv'; cases hv'; rw [h2] at hts; cases hts
  have hth : v.threads = c.threads := by
    apply Array.ext_getElem?
    intro i
    cases hc : c.threads[i]? with
    | none =>
      have : c.threads.size ≤ i := by simpa using hc
      simp [Array.getElem?_eq_none (show v.threads.size ≤ i by omega)]
    | some t => exact (key i t hc).1
  cases v; cases c
  simp_all

/-- **(S1′) with pending non-temporal stores gives a virtual
configuration**: advance the thread alone, against its own run's memory, to
the state where its release is pending at its next instruction; every other
thread is unchanged. -/
theorem Config.AdvanceableNT.virtualOfNT {A : Arch} {c : Config I} {tid : Nat} {ts : Time}
    (h : c.AdvanceableNT A tid ts) :
    ∃ v t', c.VirtualOfNT A v ∧ v.threads[tid]? = some t' ∧ ts ∈ t'.prom ∧ t'.RelFulfils A tid ts v.mem := by
  obtain ⟨t, t', M', ht, -, hnp, hts', hrel, hpre, -⟩ := h
  have hlt := lt_size_of_get? ht
  have hget : (c.withThread tid t' M').threads[tid]? = some t' := by
    simp only [Config.withThread_get? c _ _ hlt, ↓reduceIte]
  refine ⟨c.withThread tid t' M', t', ⟨hpre, Config.withThread_size c tid t' M', fun i ti hi => ?_,
    .inr ⟨tid, t', hget, ts, hts', hrel⟩⟩, hget, hts', hrel⟩
  by_cases hij : tid = i
  · subst hij
    rw [ht] at hi; cases hi
    exact ⟨t', M', hget, .refl _, hnp, .inr ⟨ts, hts', hrel⟩⟩
  · exact ⟨ti, c.mem, by simp only [Config.withThread_get? c _ _ hlt, hij, ↓reduceIte, hi], hpre, .refl _,
      .inl ⟨rfl, rfl⟩⟩

/-- Variant (ii) with pending non-temporal stores: `Config.VirtualOfNT`. It
contains `VirtualRel.ii` (`Config.VirtualOf.toNT`) and is what
`Config.advanceableNT_of_path` provides for every program
(`Config.AdvanceableNT.virtualOfNT`). -/
def VirtualRel.nt (A : Arch) : VirtualRel I where
  rel c v := c.VirtualOfNT A v
  refl c := (Config.VirtualOf.refl A c).toNT
  eq_of_final _ _ hf hv := Config.VirtualOfNT.eq_of_final hf hv

theorem VirtualRel.ii_le_nt (A : Arch) {c v : Config I} (h : (VirtualRel.ii A).rel c v) :
    (VirtualRel.nt A).rel c v :=
  Config.VirtualOf.toNT h

end Kraken.Promising
