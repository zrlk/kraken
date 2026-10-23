/-
**ISA-generic helpers for `Seg`** (`Spike/Lib/Seg.lean`), shared by the
per-ISA instance glue (`Spike/Lib/A64Ret0.lean`, `Spike/Lib/X64Ret0.lean`):
a segment from an empty fragment (`seg_false`), a fact of the entry's ghosts
taken as a hypothesis (`Seg.of_imp`), both over `SegW` too (`seg_falseW`,
`SegW.of_imp`), the round trip of `Int64` through
its bit vector, and the loaders' data symbols in address order by a
kernel-evaluable sort (`symSort`, `mergeSort_symSort`, `placeSyms_eq`).
-/
import Spike.Lib.SegW

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **A segment from an empty fragment.** -/
theorem seg_false {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {Q : Frag I} :
    Seg p lbl ms (fun _ _ => False) Q :=
  Seg.step fun _ _ h => h.elim

/-- **A fact of the entry's ghosts**: a segment from the fragment with a
proposition `L` conjoined, given one under `L`. -/
theorem Seg.of_imp {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {P Q : Frag I}
    {L : Prop} (h : L → Seg p lbl ms P Q) : Seg p lbl ms (fun s c => P s c ∧ L) Q := by
  by_cases hL : L
  · exact (h hL).mono_pre fun _ _ h => h.1
  · exact seg_false.mono_pre fun _ _ h => hL h.2

/-- **A segment from an empty fragment**, inside any `W` with any outside
moves `K`. -/
theorem seg_falseW {I : ISA} {W : Frag I} {K : I.State → I.State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {Q : Frag I} :
    SegW W K p lbl ms (fun _ _ => False) Q :=
  SegW.step (fun _ _ h => h.elim) fun _ _ h => h.elim

/-- **A fact of the entry's ghosts**, over `SegW` (`Seg.of_imp`). -/
theorem SegW.of_imp {I : ISA} {W : Frag I} {K : I.State → I.State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {P Q : Frag I}
    {L : Prop} (h : L → SegW W K p lbl ms P Q) : SegW W K p lbl ms (fun s c => P s c ∧ L) Q := by
  by_cases hL : L
  · exact (h hL).mono_pre fun _ _ h => h.1
  · exact seg_falseW.mono_pre fun _ _ h => hL h.2

theorem int64_ofBitVec_toBitVec (x : Int64) : Int64.ofBitVec x.toBitVec = x := rfl

/-! ## Data symbols in address order

The loaders place data symbols in address order with `List.mergeSort`
(`Scc.Sem.placeSyms`), which the kernel does not evaluate. `symSort`, an
insertion sort by structural recursion, gives the same list for symbols at
distinct addresses (`mergeSort_symSort`), so a placed symbol's label can be
decided. -/

/-- Insert a symbol into a list sorted by address. -/
def symIns (p : String × Nat) : List (String × Nat) → List (String × Nat)
  | [] => [p]
  | q :: l => if p.2 ≤ q.2 then p :: q :: l else q :: symIns p l

/-- **Symbols sorted by address** (insertion sort). -/
def symSort : List (String × Nat) → List (String × Nat)
  | [] => []
  | p :: l => symIns p (symSort l)

private theorem eq_of_snd_eq : ∀ {S : List (String × Nat)}, S.Pairwise (fun a b => a.2 < b.2) →
    ∀ {a b}, a ∈ S → b ∈ S → a.2 = b.2 → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | c :: S, h, a, b, ha, hb, he => by
    have h' := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; have := h'.1 b hb'; omega
    · subst hb'; have := h'.1 a ha'; omega
    · exact eq_of_snd_eq h'.2 ha' hb' he

/-- **`mergeSort` by address is any sorted permutation** of symbols at
distinct addresses (`S`, e.g. `symSort l`, with both facts decided). -/
theorem mergeSort_symSort {l S : List (String × Nat)} (hp : S.Perm l) (hS : S.Pairwise (fun a b => a.2 < b.2)) :
    l.mergeSort (fun a b => decide (a.2 ≤ b.2)) = S := by
  have hs := List.pairwise_mergeSort (le := fun a b : String × Nat => decide (a.2 ≤ b.2))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  refine List.Perm.eq_of_pairwise ?_ hs (hS.imp fun h => by simp only [decide_eq_true_eq]; omega)
    ((List.mergeSort_perm l _).trans hp.symm)
  intro a b ha hb h1 h2
  simp only [decide_eq_true_eq] at h1 h2
  exact eq_of_snd_eq hS (((List.mergeSort_perm l _).trans hp.symm).subset ha) hb (by omega)

/-- `Scc.Sem.placeSyms` over symbols already in address order. -/
def placeL {D : Type} (pad : D) (lbl : String → D) (cur : Nat) (S : List (String × Nat)) : List (D × Nat) :=
  (S.foldl (init := ([], cur)) fun (cells, c) (x, a) => (cells ++ Scc.Sem.padTo pad c a ++ [(lbl x, 0)], max a c)).1

theorem placeSyms_eq {D : Type} (pad : D) (lbl : String → D) (cur : Nat) {l S : List (String × Nat)}
    (hp : S.Perm l) (hs : S.Pairwise (fun a b => a.2 < b.2)) :
    Scc.Sem.placeSyms pad lbl cur l = placeL pad lbl cur S := by
  unfold Scc.Sem.placeSyms placeL
  rw [mergeSort_symSort hp hs]

end Spike.Lib
