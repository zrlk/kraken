/-
**The value invariant with successful plain stores: the generic preservation
lemmas**. ISA-neutral.

`MemVals.ValX` asks the write condition of *every* answer of a store,
`b = false` included. The machine never answers a non-exclusive store with
`b = false` (`runTree`'s failure branch is guarded by `xcl`), and the
environment that AArch64's per-thread runs use, `SharedEnv.inv S G`, only
answers a non-exclusive store with success (`inv_step_store`), as
`A64NoFaultD`'s address runs (`AddrSafeA`, `EvTree.AllLeavesA`) do. So the
AArch64 link of the value invariant needs the store clause guarded by the
same condition:

- `ValXA L V P t`: `ValX` with the store continuation asked only at
  `b = true ∨ xcl = true` (`ValX.toValXA`: every `ValX` tree is `ValXA`);
- **`runTree_valXA`**, `stepOne_valXA`, `threadNP_valXA`, `certWrite_valXA`:
  `runTree_valX` and its consequences, the store case reading the failure
  branch off `xcl`;
- **`Reachable.valInvA`**, **`faultFree_of_valInvA`**: `Reachable.valInv`
  and `faultFree_of_valInv` for `ValXA`, promises included.

These are the generic forms: `ValXA` is the weaker tree condition, and
`MemVals.lean`'s `ValX` lemmas (`runTree_valX`, `stepOne_valX`,
`threadNP_valX`, `certWrite_valX`, `Reachable.valInv`,
`faultFree_of_valInv`) are their instances through `ValX.toValXA`.

Nothing here is stronger than the machine: a `ValXA` tree is unconstrained
exactly at the answers `runTree` never produces.
-/
import Kraken.Promising.SLR.EnvG.MemValsBase

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA} {L : Loc → Prop} {V : Val → Prop}

/-- **The tree condition with successful plain stores**: `ValX`, except that
a store's continuation is asked only at the answers the machine gives
(`b = true`, or either answer of an exclusive store). -/
def ValXA {σ : Type} (L : Loc → Prop) (V : Val → Prop) (P : σ → Prop) : EvTree σ → Prop
  | .done s => P s
  | .fault _ => True
  | .choose _ k => ∀ i, ValXA L V P (k i)
  | .load _ _ l ret => ∀ v, (L l → V v) → ValXA L V P (ret v)
  | .store _ xcl l v ret => (L l → V v) ∧ ∀ b, (b = true ∨ xcl = true) → ValXA L V P (ret b)
  | .rmw _ _ l op ret => ∀ old, (L l → V old) →
      (∀ new, op old = some new → L l → V new) ∧ ValXA L V P (ret old)
  | .fence _ ret => ∀ u, ValXA L V P (ret u)

/-- Every `ValX` tree is `ValXA`. -/
theorem ValX.toValXA {σ : Type} {P : σ → Prop} : ∀ {t : EvTree σ}, ValX L V P t → ValXA L V P t
  | .done _, h => h
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => ValX.toValXA (h i)
  | .load _ _ _ _, h => fun v hv => ValX.toValXA (h v hv)
  | .store _ _ _ _ _, h => ⟨h.1, fun b _ => ValX.toValXA (h.2 b)⟩
  | .rmw _ _ _ _ _, h => fun old ho => ⟨(h old ho).1, ValX.toValXA (h old ho).2⟩
  | .fence _ _, h => fun u => ValX.toValXA (h u)

/-- `ValXA` is monotone in the leaf condition. -/
theorem ValXA.mono {σ : Type} {P P' : σ → Prop} (hP : ∀ s, P s → P' s) :
    ∀ {t : EvTree σ}, ValXA L V P t → ValXA L V P' t
  | .done s, h => hP s h
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => ValXA.mono hP (h i)
  | .load _ _ _ _, h => fun v hv => ValXA.mono hP (h v hv)
  | .store _ _ _ _ _, h => ⟨h.1, fun b hb => ValXA.mono hP (h.2 b hb)⟩
  | .rmw _ _ _ _ _, h => fun old ho => ⟨(h old ho).1, ValXA.mono hP (h old ho).2⟩
  | .fence _ _, h => fun u => ValXA.mono hP (h u)

section Steps

variable {A : Arch} {tid : Nat} {iv : InstrViews}

/-- **The key preservation lemma for `ValXA`** (`runTree_valX`): a run of a
`ValXA` tree from a `MemVals` memory ends in a `MemVals` memory at a
`P`-leaf. A store's failure branch is taken only when it is exclusive:
`runTree`'s `fail` list (`Promising/Thread.lean`) is `if xcl then … else []`,
so `List.mem_ite_nil_right` gives `xcl = true` in the store case.
Generic form of `MemVals.runTree_valX` (its instance through `ValX.toValXA`). -/
theorem runTree_valXA (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} {P : σ → Prop} :
    ∀ (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      ValXA L V P tree → MemVals L V c.mem → MemVals L V c'.mem ∧ P s
  | .done _, c, s, c', h, hA, hm => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hm, hA⟩
  | .fault _, _, _, _, h, _, _ => by simp [runTree] at h
  | .choose _ k, c, s, c', h, hA, hm => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact runTree_valXA A tid iv (k i) c s c' h (hA i) hm
  | .load _ _ l ret, c, s, c', h, hA, hm => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨y, hy, h⟩ := h
    have hrd := readSuccs_read A iv hy
    have hm2 := (readSuccs_memProm A iv hy).1
    exact runTree_valXA A tid iv _ _ s c' h (hA _ (hm.read hrd)) (hm2 ▸ hm)
  | .store _ xcl l v ret, c, s, c', h, hA, hm => by
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact runTree_valXA A tid iv _ c0 s c' h (hA.2 true (.inl rfl)) (memVals_write hc0 hA.1 hm)
    · rw [List.mem_ite_nil_right] at h
      exact runTree_valXA A tid iv _ _ s c' h.2 (hA.2 false (.inr h.1)) hm
  | .fence k ret, c, s, c', h, hA, hm => by
    simp only [runTree] at h
    exact runTree_valXA A tid iv _ _ s c' h (hA ()) ((fenceStep_mem_prom c k).1 ▸ hm)
  | .rmw k noRet l op ret, c, s, c', h, hA, hm => by
    simp only [runTree] at h
    have h1 := (optFence_mem_prom c A.rmwFence .sy).1
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have hrd := readSuccs_read A iv h2
    have hm2 := (readSuccs_memProm A iv h2).1
    simp only at h hrd hm2
    rw [h1] at hrd
    have hold : L l → V old := hm.read hrd
    have hm1 : MemVals L V c2.mem := by rw [hm2, h1]; exact hm
    split at h
    · exact runTree_valXA A tid iv _ _ s c' h ((hA old hold).2) ((optFence_mem_prom c2 _ _).1 ▸ hm1)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      have hm3 := memVals_write hc3 ((hA old hold).1 new hnew) hm1
      have hm4 : MemVals L V (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy
          else rmwPost A k noRet l c3).mem := by
        rw [(optFence_mem_prom _ _ _).1, rmwPost_mem]
        exact hm3
      exact runTree_valXA A tid iv _ _ s c' h ((hA old hold).2) hm4

/-- **One instruction** (`stepOne_valX` for `ValXA`).
Generic form of `MemVals.stepOne_valX` (its instance through `ValX.toValXA`). -/
theorem stepOne_valXA (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {P : I.State → Prop}
    (hA : ∀ tree, I.exec t.st = some tree → ValXA L V P tree) (hm : MemVals L V mem) :
    MemVals L V o.mem ∧ P o.thread.st := by
  obtain ⟨tree, iv, c', hex, hr, -, hmo⟩ := stepOne_run A hstep ho
  rw [hmo]
  exact runTree_valXA A tid iv tree _ _ c' hr (hA tree hex) hm

/-- A promise-free solo run keeps `MemVals` and the per-thread invariant
(`threadNP_valX` for `ValXA`).
Generic form of `MemVals.threadNP_valX` (its instance through `ValX.toValXA`). -/
theorem threadNP_valXA (A : Arch) {tid : Nat} {P : I.State → Prop}
    (hP : ∀ (st : I.State) tree, P st → I.exec st = some tree → ValXA L V P tree) :
    ∀ {p q : Thread I × Memory}, ThreadNP A tid p q → P p.1.st → MemVals L V p.2 →
      P q.1.st ∧ MemVals L V q.2
  | _, _, .refl _, h1, h2 => ⟨h1, h2⟩
  | _, _, .step ⟨outs, o, hs, ho, rfl⟩ hr, h1, h2 => by
    obtain ⟨hm, hp⟩ := stepOne_valXA A hs ho (fun tree hex => hP _ tree h1 hex) h2
    exact threadNP_valXA A hP hr hp hm

/-- **A certified promise writes a `V`-value to an `L`-location**
(`certWrite_valX` for `ValXA`).
Generic form of `MemVals.certWrite_valX` (its instance through `ValX.toValXA`). -/
theorem certWrite_valXA (A : Arch) {tid : Nat} {P : I.State → Prop}
    (hP : ∀ (st : I.State) tree, P st → I.exec st = some tree → ValXA L V P tree) {t : Thread I}
    {mem : Memory} {p : Msg × View} (h : CertWrite A tid t mem p) (ht : P t.st) (hm : MemVals L V mem) :
    L p.1.loc → V p.1.val := by
  obtain ⟨t1, mem1, outs, o, hr, hs, ho, hp⟩ := h
  obtain ⟨ht1, hm1⟩ := threadNP_valXA A hP hr ht hm
  obtain ⟨hmo, -⟩ := stepOne_valXA A hs ho (fun tree hex => hP _ tree ht1 hex) hm1
  obtain ⟨-, hmsgs⟩ := stepOne_ext A hs ho
  intro hl
  have hin : p.1 ∈ o.mem.msgs.toList := by
    rw [hmsgs]; exact List.mem_append_right _ (List.mem_map_of_mem (f := (·.1)) hp)
  obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hin
  refine hmo.2 (j + 1) p.1 ?_ hl
  simp only [Memory.get?, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [Array.length_toList] at hj
  rw [Array.getElem?_eq_getElem hj, ← hjv, Array.getElem_toList]

/-- **The value invariant holds at every reachable configuration**
(`Reachable.valInv` for `ValXA`), promise steps included.
Generic form of `MemVals.Reachable.valInv` (its instance through `ValX.toValXA`). -/
theorem Reachable.valInvA {A : Arch} [I.LawfulState] {P : I.State → Prop}
    (hP : ∀ (st : I.State) tree, P st → I.exec st = some tree → ValXA L V P tree)
    {fuel : Nat} {c c' : Config I} (h : Reachable A fuel c c') (h0 : ValInvAt L V P c) :
    ValInvAt L V P c' := by
  refine h.inv (fun c c1 h0 hs => ?_) h0
  rcases succ_cases' hs with ⟨j, tj, outs, o, hj, hstep, ho, rfl⟩ | ⟨j, tj, p, hj, hcw, rfl⟩
  · obtain ⟨hm, hp⟩ := stepOne_valXA A hstep ho (fun tree hex => hP _ tree (h0.2 j tj hj) hex) h0.1
    refine ⟨by simpa [Config.withThread] using hm, fun i t ht => ?_⟩
    rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at ht
    split at ht
    · cases ht; exact hp
    · exact h0.2 i t ht
  · have hv := certWrite_valXA A hP hcw (h0.2 j tj hj) h0.1
    refine ⟨by simpa [Config.withThread] using h0.1.append (w := { p.1 with tid := j }) hv, fun i t ht => ?_⟩
    rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at ht
    split at ht
    · cases ht; exact h0.2 j tj hj
    · exact h0.2 i t ht

/-- **Program-level fault freedom from a value invariant**
(`faultFree_of_valInv` for `ValXA`): every tree of a `P`-state `ValXA` and
fault-free, and `ValInvAt` initially, give `Config.FaultFree`.
Generic form of `MemVals.faultFree_of_valInv` (its instance through `ValX.toValXA`). -/
theorem faultFree_of_valInvA {A : Arch} [I.LawfulState] {P : I.State → Prop}
    (hP : ∀ (st : I.State) tree, P st → I.exec st = some tree → ValXA L V P tree)
    (hnf : ∀ (st : I.State) tree, P st → I.exec st = some tree → tree.NoFault)
    {fuel : Nat} {c₀ : Config I} (h0 : ValInvAt L V P c₀) :
    Config.FaultFree A fuel c₀ := by
  intro c hc tid m
  by_cases ht : ∃ t, c.threads[tid]? = some t
  · obtain ⟨t, ht⟩ := ht
    have hPt := (Reachable.valInvA hP hc h0).2 tid t ht
    exact Config.not_faultStep_of_noFaultRun A ht (fun tree hex => (hnf _ tree hPt hex).run A tid _ _) m
  · rintro ⟨outs, hs, -⟩
    obtain ⟨t, ht', -⟩ := stepThread_eq_some hs
    exact ht ⟨t, ht'⟩

end Steps

end Kraken.Promising.SLR.EnvG

#print axioms Kraken.Promising.SLR.EnvG.runTree_valXA
#print axioms Kraken.Promising.SLR.EnvG.faultFree_of_valInvA
