/-
Simulation library, part 4: instances. Memory
extension of a promise-free run (`readSuccs_memExt`, `runTree_memExt`,
`threadNP_memExt`), the whole-thread environment (`threadNP_env`) and the B2
shape for a memory extension (`certOk_memExt`).
-/
import Kraken.Promising.SLR.Sim.Run
import Kraken.Promising.SLR.Sim.Maps

namespace Kraken.Promising

namespace Sim

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Prototype: memory extension of a promise-free load

The easiest instance: the target memory extends the source memory (`M ⊑ M'`,
the foreign messages `M' ∖ M` above `|M|`), `ρ = idUpTo |M|`, the source
context bounded by `|M|` and promise-free. The target context is the source
context on the larger memory. -/

section Prototype

variable (A : Arch) (tid : Nat)

/-- Promises in `[0, n]` are their own images under `idUpTo n`. -/
theorem PromRel.self_idUpTo {n : Nat} : ∀ {xs : List Time}, (∀ s ∈ xs, s ≤ n) → PromRel (TMap.idUpTo n) xs xs
  | [], _ => .nil
  | x :: _, h => .keep (h x List.mem_cons_self) (PromRel.self_idUpTo fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- On a bounded context, `idUpTo |M|` relates the context to itself on any
extension of its memory: the instance's relation holds
(promises in the base map to themselves). -/
theorem CtxRel.memExt {c : Ctx} (hb : c.Bnd) (hp : ∀ s ∈ c.prom, s ≤ c.mem.last) {M' : Memory}
    (hM : c.mem.Prefix M') :
    CtxRel (TMap.idUpTo c.mem.last) c { c with mem := M' } := by
  have hl := hb.views.le
  have e : ∀ {x : Nat}, x ≤ c.mem.last → (TMap.idUpTo c.mem.last).fv x = x := fun h => Nat.min_eq_left h
  refine ⟨⟨hM.1, fun s hs => hs, fun s hs => Nat.le_trans hs hM.last_le, fun s hs => hM.get? hs⟩,
    ⟨fun l => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun l => ?_, ?_⟩, ?_, ?_, ?_, rfl, rfl⟩
  · show _ ≤ _; rw [e (hl.coh l)]; exact Nat.le_refl _
  · show _ ≤ _; rw [e hl.vrNew]; exact Nat.le_refl _
  · show _ ≤ _; rw [e hl.vrOld]; exact Nat.le_refl _
  · show _ ≤ _; rw [e hl.vrOldNR]; exact Nat.le_refl _
  · show _ ≤ _; rw [e hl.vwNew]; exact Nat.le_refl _
  · show _ ≤ _; rw [e hl.vwOld]; exact Nat.le_refl _
  · show _ ≤ _; rw [e hl.vwOldNT]; exact Nat.le_refl _
  · show _ ≤ _; rw [e hl.vCAP]; exact Nat.le_refl _
  · show _ ≤ _; rw [e hl.vRel]; exact Nat.le_refl _
  · show FwdLe _ (c.views.getFwd l) (c.views.getFwd l)
    cases h : c.views.getFwd l with
    | none => trivial
    | some f =>
      exact ⟨hb.views.fwdTime l f h, rfl, by rw [e (hl.fwd l f h)]; exact Nat.le_refl _, rfl,
        by rw [e (Nat.le_trans (Nat.min_le_right _ _) (hb.views.fwdTime l f h))]; exact Nat.le_refl _⟩
  · show XclLe _ c.views.xclb c.views.xclb
    cases h : c.views.xclb with
    | none => trivial
    | some p =>
      obtain ⟨t, ν, l⟩ := p
      have := hb.views.xclb t ν l h
      exact ⟨this.1, rfl, by rw [e this.2]; exact Nat.le_refl _, rfl⟩
  · show PromRel _ c.prom c.prom
    exact PromRel.self_idUpTo hp
  · show Rel2 _ c.loadViews c.loadViews
    have key : ∀ xs : List View, (∀ ν ∈ xs, ν ≤ c.mem.last) →
        Rel2 (fun a' a => a' ≤ (TMap.idUpTo c.mem.last).fv a) xs xs := by
      intro xs h
      induction xs with
      | nil => exact .nil
      | cons x xs ih =>
        refine .cons ?_ (ih fun ν hν => h ν (List.mem_cons_of_mem _ hν))
        rw [e (h x List.mem_cons_self)]; exact Nat.le_refl _
    exact key _ hb.loadViews
  · show _ ≤ _; rw [e hb.succView]; exact Nat.le_refl _

theorem IVLe.self_idUpTo {iv : InstrViews} {n : Nat} (h : iv.Le n) : IVLe (TMap.idUpTo n) iv iv := by
  have e : ∀ {x : Nat}, x ≤ n → x ≤ (TMap.idUpTo n).fv x := fun h => by
    show _ ≤ min _ _; rw [Nat.min_eq_left h]; exact Nat.le_refl _
  refine ⟨e h.addrR, e h.addrW, e h.dataR, e h.dataW, e h.condW, ?_⟩
  have key : ∀ ps : List (View × View), (∀ p ∈ ps, p.1 ≤ n ∧ p.2 ≤ n) →
      Rel2 (fun p' p => p'.1 ≤ (TMap.idUpTo n).fv p.1 ∧ p'.2 ≤ (TMap.idUpTo n).fv p.2) ps ps := by
    intro ps hp
    induction ps with
    | nil => exact .nil
    | cons p ps ih =>
      have := hp p List.mem_cons_self
      exact .cons ⟨e this.1, e this.2⟩ (ih fun q hq => hp q (List.mem_cons_of_mem _ hq))
  exact key _ h.dataPer

/-- No foreign message of `M ⊑ M'` lies at or below `|M|`: the gap condition
of a read with a bounded window holds. -/
theorem GapFree.memExt {M M' : Memory} (l : Loc) (lo hi : Time) (hhi : hi ≤ M.last) :
    GapFree (TMap.idUpTo M.last) M' l lo hi := by
  intro s' w _ h2 hfor _
  exact absurd ⟨s', Nat.le_trans h2 hhi, rfl⟩ hfor

/-- **Prototype (memory extension, load), via the schema.** A promise-free
bounded thread's read in `M` is a read of the same timestamp and value in any
extension `M'`, with related successor contexts. -/
theorem readSuccs_memExt_sim {iv : InstrViews} {c : Ctx} (hb : c.Bnd) (hp : c.prom = []) (hiv : iv.Le c.mem.last)
    {M' : Memory} (hM : c.mem.Prefix M') {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {t : Time} {v : Val}
    {c₁ : Ctx} (hx : (t, v, c₁) ∈ readSuccs A iv c k xcl l noRet) :
    ∃ c₁', (t, v, c₁') ∈ readSuccs A iv { c with mem := M' } k xcl l noRet ∧
      CtxRel (TMap.idUpTo c.mem.last) c₁ c₁' := by
  have ht : t ≤ c.mem.last := (readSuccs_bnd A iv hb hiv hx).2.1
  exact readSuccs_sim A (CtxRel.memExt hb (by rw [hp]; intro s hs; exact absurd hs List.not_mem_nil) hM) (IVLe.self_idUpTo hiv) hx ht
    (GapFree.memExt l _ _ (Nat.min_le_right _ _))

/-- **Prototype (memory extension, load), exact form.** The same read, with
the target's successor context literally the source's on the larger
memory. (Promise-freedom is not needed here: the promise list is
unchanged.) -/
theorem readSuccs_memExt {iv : InstrViews} {c : Ctx} (hb : c.Bnd) (hiv : iv.Le c.mem.last)
    {M' : Memory} (hM : c.mem.Prefix M') {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {t : Time} {v : Val}
    {c₁ : Ctx} (hx : (t, v, c₁) ∈ readSuccs A iv c k xcl l noRet) :
    (t, v, { c₁ with mem := M' }) ∈ readSuccs A iv { c with mem := M' } k xcl l noRet := by
  obtain ⟨t0, v0, he, htl, hv, hw, hpr⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  have hB : max (readPre A iv c k) (c.views.getCoh l) ≤ c.mem.last := by
    have hl := hb.views.le
    have : readPre A iv c k ≤ c.mem.last := by
      unfold readPre
      have := hiv.addrR; have := hl.vrNew; have := hl.vRel
      split <;> omega_t
    have := hl.coh l; omega_t
  refine (mem_readSuccs A).mpr ⟨t, v, rfl, Nat.le_trans htl hM.last_le, ?_, ?_, hpr⟩
  · show M'.read? l t = some v
    rw [hM.read? htl]; exact hv
  · show M'.writeIn l t (max (readPre A iv c k) (c.views.getCoh l)) = false
    rw [hM.writeIn_eq hB]; exact hw

/-- The memory-extension instance of `SimInv`: `ρ = idUpTo |M|`, `n = |M|`,
foreign messages the extension's, to locations in `L`. -/
theorem SimInv.memExt {iv : InstrViews} {c : Ctx} (hb : c.Bnd) (hp : c.prom = []) (hiv : iv.Le c.mem.last)
    {M' : Memory} (hM : c.mem.Prefix M') {L : Loc → Prop}
    (hL : ∀ s' w, c.mem.last < s' → M'.get? s' = some w → L w.loc) :
    SimInv (TMap.idUpTo c.mem.last) c.mem.last L iv iv c { c with mem := M' } := by
  refine ⟨CtxRel.memExt hb (by rw [hp]; intro s hs; exact absurd hs List.not_mem_nil) hM, hb, (by rw [hp]; intro s hs; exact absurd hs List.not_mem_nil), fun s hs => hs, IVLe.self_idUpTo hiv,
    hiv, Nat.le_refl _, ?_⟩
  intro s' w hfor hw
  have hs' : c.mem.last < s' := Nat.lt_of_not_le fun h => hfor ⟨s', h, rfl⟩
  refine ⟨hL s' w hs' hw, ?_, fun s hs hns => absurd hs (Nat.not_le_of_lt hns)⟩
  show min c.mem.last c.mem.last < s'
  rw [Nat.min_self]; exact hs'

/-- **Prototype (memory extension, one instruction).** A promise-free bounded
thread's run of an instruction's event tree in `M` is a run of the same tree,
with the same final machine state (so the same register effects), in any
extension `M'` of `M` whose new messages are to locations in `L`, provided the
run is `StaleFree` at `|M|` for `L` (it never reads a base message of an
`L`-location after its bound passed `|M|`, and never pairs an exclusive/RMW
write on one with a base read). With `L = ∅` (the extension writes no
location the run reads) the side condition is trivial. -/
theorem runTree_memExt {σ : Type} {iv : InstrViews} (tree : EvTree σ) {c : Ctx} (hb : c.Bnd) (hp : c.prom = [])
    (hiv : iv.Le c.mem.last) {M' : Memory} (hM : c.mem.Prefix M') {L : Loc → Prop}
    (hL : ∀ s' w, c.mem.last < s' → M'.get? s' = some w → L w.loc)
    (hsf : StaleFree A tid iv c.mem.last L c tree) {s : σ} {c₂ : Ctx} (h : .ok (s, c₂) ∈ runTree A tid iv c tree) :
    ∃ ρ' : TMap, ∃ c₂', .ok (s, c₂') ∈ runTree A tid iv { c with mem := M' } tree ∧
      CtxRel ρ' c₂ c₂' ∧ ∀ t ≤ c.mem.last, ρ'.dom t ∧ ρ'.f t = t := by
  obtain ⟨ρ', c₂', h', hs', hag, -⟩ := runTree_sim A tid tree _ c _ s c₂ (SimInv.memExt hb hp hiv hM hL) hsf h
  exact ⟨ρ', c₂', h', hs'.rel, fun t ht => hag.1 t ht⟩

/-- **Prototype (memory extension, solo run).** A bounded thread's (promises
in `M` allowed) `StaleFree` promise-free solo run from `M` is matched by a solo run of the same
thread from any extension `M'` of `M` whose new messages are to locations in
`L`: register views and views at most the floor images, memories related, the
base `[0, |M|]` mapped identically. (With `L = ∅`, `ThreadNP.toSF` supplies
`StaleFree`.) -/
theorem threadNP_memExt {I : ISA} {t : Thread I} {M M' : Memory} (hb : t.Bnd M.last)
    (hpb : ∀ s ∈ t.prom, s ≤ M.last)
    (hM : M.Prefix M') {L : Loc → Prop} (hL : ∀ s' w, M.last < s' → M'.get? s' = some w → L w.loc)
    {r : Thread I × Memory} (h : ThreadSF A tid M.last L (t, M) r) :
    ∃ ρ' : TMap, ∃ r' : Thread I × Memory, ThreadNP A tid (t, M') r' ∧
      ThreadRel ρ' r.1 r'.1 ∧ MemRel ρ' r.2 r'.2 ∧ ∀ s ≤ M.last, ρ'.dom s ∧ ρ'.f s = s := by
  let c : Ctx := { views := t.views, prom := t.prom, mem := M }
  have hcb : c.Bnd := ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  have hrel := CtxRel.memExt hcb hpb hM
  have e : ∀ {x : Nat}, x ≤ M.last → x ≤ (TMap.idUpTo M.last).fv x := fun h => by
    show _ ≤ min _ _; rw [Nat.min_eq_left h]; exact Nat.le_refl _
  have hT : ThreadRel (TMap.idUpTo M.last) t t :=
    ⟨rfl, rfl, rfl, fun _ => e (arr_le hb.regs.1), fun _ => e (arr_le hb.regs.2), hrel.views, hrel.prom⟩
  have hfg : FgnSep (TMap.idUpTo M.last) M' M.last L := by
    intro s' w hfor hw
    have hs' : M.last < s' := Nat.lt_of_not_le fun h => hfor ⟨s', h, rfl⟩
    refine ⟨hL s' w hs' hw, ?_, fun s hs hns => absurd hs (Nat.not_le_of_lt hns)⟩
    show min M.last M.last < s'
    rw [Nat.min_self]; exact hs'
  obtain ⟨ρ', r', hr', hT', hm', hag, -, -⟩ := threadSF_sim A tid h _ t M' hT hrel.mem hb
    hpb (fun s hs => hs) (Nat.le_refl _) hfg
  exact ⟨ρ', r', hr', hT', hm', fun s hs => hag s hs⟩

/-- **Environment instance (solo run).** Same memory, `ρ = idUpTo |M|`: a
target thread whose views and register views are at most the source's
(`ThreadRel`), with the same promises, follows every promise-free solo run of
the bounded source thread, with no side condition. -/
theorem threadNP_env {I : ISA} {t t' : Thread I} {M : Memory} (hb : t.Bnd M.last)
    (hpb : ∀ s ∈ t.prom, s ≤ M.last) (hT : ThreadRel (TMap.idUpTo M.last) t t')
    {r : Thread I × Memory} (h : ThreadNP A tid (t, M) r) :
    ∃ ρ' : TMap, ∃ r' : Thread I × Memory, ThreadNP A tid (t', M) r' ∧
      ThreadRel ρ' r.1 r'.1 ∧ MemRel ρ' r.2 r'.2 ∧ ∀ s ≤ M.last, ρ'.dom s ∧ ρ'.f s = s := by
  let c : Ctx := { views := t.views, prom := t.prom, mem := M }
  have hcb : c.Bnd := ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  have hrel := CtxRel.memExt hcb hpb (Memory.Prefix.refl M)
  obtain ⟨ρ', r', hr', hT', hm', hag, -, -⟩ := threadSF_sim A tid (ThreadNP.toSF A tid h 0) _ t' M hT hrel.mem hb
    (fun s hs => hpb s hs) (fun s hs => hs) (Nat.zero_le _)
    (NoForeign.fgnSep (fun s' _ h2 => ⟨s', h2, rfl⟩) 0 _)
  exact ⟨ρ', r', hr', hT', hm', fun s hs => hag s hs⟩

/-- **B2 shape (certification transport, memory extension).** If a bounded
thread certifies in `M` (`CertOk`) by a run that is `StaleFree` for the
locations written by `M' ∖ M`, it certifies in every extension `M'`. -/
theorem certOk_memExt {I : ISA} {t : Thread I} {M M' : Memory} (hb : t.Bnd M.last)
    (hpb : ∀ s ∈ t.prom, s ≤ M.last) (hM : M.Prefix M') {L : Loc → Prop}
    (hL : ∀ s' w, M.last < s' → M'.get? s' = some w → L w.loc)
    {r : Thread I × Memory} (h : ThreadSF A tid M.last L (t, M) r) (hr : r.1.prom = []) :
    CertOk A tid t M' := by
  obtain ⟨ρ', r', hr', hT', -, -⟩ := threadNP_memExt A tid hb hpb hM hL h
  have key : ∀ {xs ys : List Time}, PromRel ρ' xs ys → xs = [] → ys = [] := by
    intro xs ys h e; cases h with
    | nil => rfl
    | keep => cases e
    | drop => cases e
  exact ⟨r'.1, r'.2, hr', key hT'.prom hr⟩

/-- The memory-extension start state: `ρ = idUpTo |M|`, the thread related to
itself, foreign messages (to watched locations) above `|M|` at threshold
`|M|`. Without foreign messages (`M' = M`) any `N ⊆ [0, |M|]` works. -/
theorem SimState.memExt {I : ISA} {L : Loc → Prop} {t : Thread I} {M M' : Memory} (hb : t.Bnd M.last) (hpb : ∀ s ∈ t.prom, s ≤ M.last)
    (hM : M.Prefix M') (hL : ∀ s' w, M.last < s' → M'.get? s' = some w → L w.loc) :
    SimState (TMap.idUpTo M.last) (· = M.last) L (t, M) (t, M') := by
  let c : Ctx := { views := t.views, prom := t.prom, mem := M }
  have hcb : c.Bnd := ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  have hrel := CtxRel.memExt hcb hpb hM
  have e : ∀ {x : Nat}, x ≤ M.last → x ≤ (TMap.idUpTo M.last).fv x := fun h => by
    show _ ≤ min _ _; rw [Nat.min_eq_left h]; exact Nat.le_refl _
  refine ⟨⟨rfl, rfl, rfl, fun _ => e (arr_le hb.regs.1), fun _ => e (arr_le hb.regs.2), hrel.views, hrel.prom⟩,
    hrel.mem, hb, hpb, fun s hs => hs, fun n hn => hn ▸ Nat.le_refl _, ?_⟩
  intro s' w hfor hw
  have hs' : M.last < s' := Nat.lt_of_not_le fun h => hfor ⟨s', h, rfl⟩
  refine ⟨hL s' w hs' hw, M.last, rfl, ?_, fun s hs hns => absurd hs (Nat.not_le_of_lt hns)⟩
  show min M.last M.last < s'
  rw [Nat.min_self]; exact hs'

end Prototype


end Sim

end Kraken.Promising
