import Scc.Sem.Target

/-!
# The canonical loaders' data-symbol cells, generically

The canonical targets (`Scc.Sem.A64.threadAt`, `Scc.Sem.X64.threadAt`) lay
the data symbols' label cells out around the code: those below the code
before it, from the lowest (`placeBelow`, the executable starting at
`exeStart`), the others after it (`placeSyms`), each padded up to its
address (`padTo`, no empty padding). This file proves, for any directive
type, what the per-ISA layout proofs need of those cells:

- `fold_spec`: the folds append non-empty padding and label cells of the
  folded symbols, whose sizes take the current address to the fold's new
  one, the largest address seen;
- `fold_label`: over symbols in address order, the first label cell of a
  name sits at that symbol's address;
- `placeBelow_spec`, `placeBelow_label`, `placeSyms_spec`,
  `placeSyms_label`: the same for the two cell runs, `placeBelow`'s ending
  exactly at the code;
- `exeStart_*`, `*_of_above`: with no symbol below the code, the executable
  starts at the code, `placeBelow` is empty and `symsFrom` keeps every
  symbol;
- `placeSyms_eq_old`: with every symbol above the end of the code at
  distinct addresses, `placeSyms` is the old one (`placeSymsOld`, which
  padded with a possibly empty cell).
-/

namespace Scc.Cert.PlaceSyms

open Scc.Sem

section Generic

variable {D : Type} (pad : D) (lbl : String → D)

/-- The step of `placeSyms`' and `placeBelow`'s folds. -/
def step (acc : List (D × Nat) × Nat) (xa : String × Nat) : List (D × Nat) × Nat :=
  (acc.1 ++ padTo pad acc.2 xa.2 ++ [(lbl xa.1, 0)], max xa.2 acc.2)

/-- The address order the folds sort by. -/
def le (a b : String × Nat) : Bool := decide (a.2 ≤ b.2)

theorem placeSyms_eq (cur : Nat) (syms : List (String × Nat)) :
    placeSyms pad lbl cur syms = ((syms.mergeSort le).foldl (step pad lbl) ([], cur)).1 := rfl

theorem placeBelow_eq (lo : Nat) (syms : List (String × Nat)) :
    placeBelow pad lbl lo syms =
      (((symsBelow lo syms).mergeSort le).foldl (step pad lbl) ([], exeStart lo syms)).1 ++
        padTo pad (((symsBelow lo syms).mergeSort le).foldl (step pad lbl) ([], exeStart lo syms)).2 lo := rfl

theorem padTo_mem {c a : Nat} {y : D × Nat} (h : y ∈ padTo pad c a) : y = (pad, a - c) ∧ c < a := by
  unfold padTo at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; exact ⟨h, by assumption⟩
  · simp at h

theorem padTo_sum (c a : Nat) : ((padTo pad c a).map (·.2)).sum + c = max a c := by
  unfold padTo
  split <;> simp <;> omega

/-- **The folds' cells**: non-empty padding and label cells of the folded
symbols, whose sizes take `c` to the fold's new address, the largest of `c`
and the folded addresses. -/
theorem fold_spec : ∀ (L : List (String × Nat)) (cells : List (D × Nat)) (c : Nat),
    ∃ new, (L.foldl (step pad lbl) (cells, c)).1 = cells ++ new ∧
      (∀ y ∈ new, (y.1 = pad ∧ 0 < y.2) ∨ ∃ p ∈ L, y = (lbl p.1, 0)) ∧
      (new.map (·.2)).sum + c = (L.foldl (step pad lbl) (cells, c)).2 ∧
      c ≤ (L.foldl (step pad lbl) (cells, c)).2 ∧
      ∀ B, c ≤ B → (∀ p ∈ L, p.2 ≤ B) → (L.foldl (step pad lbl) (cells, c)).2 ≤ B
  | [], cells, c => ⟨[], by simp, by simp, by simp, Nat.le_refl _, fun _ h _ => h⟩
  | (x, a) :: L, cells, c => by
    obtain ⟨new, h1, h2, h3, h4, h5⟩ := fold_spec L (cells ++ padTo pad c a ++ [(lbl x, 0)]) (max a c)
    refine ⟨padTo pad c a ++ [(lbl x, 0)] ++ new, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, step]; rw [h1]; simp
    · intro y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with (hy | rfl) | hy
      · obtain ⟨rfl, hc⟩ := padTo_mem pad hy
        exact Or.inl ⟨rfl, by simp only; omega⟩
      · exact Or.inr ⟨(x, a), List.mem_cons_self .., rfl⟩
      · rcases h2 y hy with h | ⟨p, hp, he⟩
        · exact Or.inl h
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, he⟩
    · simp only [List.foldl_cons, step] at h3 ⊢
      have := padTo_sum pad c a
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at this ⊢
      omega
    · simp only [List.foldl_cons, step] at h4 ⊢; omega
    · intro B hB hL
      simp only [List.foldl_cons, step]
      have := hL (x, a) (List.mem_cons_self ..)
      exact h5 B (by simp only at this; omega) (fun p hp => hL p (List.mem_cons_of_mem _ hp))

/-- **A label cell at its symbol's address**: over symbols in address order,
from `c` at most `a`, the first label cell named `x`, the name of `(x, a)`
only, sits after cells (none of them that label) whose sizes take `c` to
`a`. -/
theorem fold_label (hpad : ∀ x, pad ≠ lbl x) (hlbl : ∀ x y, lbl x = lbl y → x = y) :
    ∀ (L : List (String × Nat)) (cells : List (D × Nat)) (c : Nat) {x : String} {a : Nat},
    L.Pairwise (fun p q => p.2 ≤ q.2) → (x, a) ∈ L → c ≤ a → (∀ p ∈ L, p.1 = x → p.2 = a) →
    ∃ pre post, (L.foldl (step pad lbl) (cells, c)).1 = cells ++ pre ++ (lbl x, 0) :: post ∧
      (∀ y ∈ pre, y.1 ≠ lbl x) ∧ (pre.map (·.2)).sum + c = a
  | [], _, _, _, _, _, hm, _, _ => by simp at hm
  | (y, b) :: L, cells, c, x, a, hs, hm, hc, hone => by
    have hs' := List.pairwise_cons.mp hs
    by_cases hyx : y = x
    · subst hyx
      have hb : b = a := hone (y, b) (List.mem_cons_self ..) rfl
      subst hb
      obtain ⟨new, h1, -⟩ := fold_spec pad lbl L (cells ++ padTo pad c b ++ [(lbl y, 0)]) (max b c)
      refine ⟨padTo pad c b, new, ?_, ?_, ?_⟩
      · simp only [List.foldl_cons, step]; rw [h1]; simp
      · intro z hz
        rw [(padTo_mem pad hz).1]
        exact hpad y
      · have := padTo_sum pad c b; omega
    · have hm' : (x, a) ∈ L := by
        rcases List.mem_cons.mp hm with h | h
        · cases h; exact absurd rfl hyx
        · exact h
      have hba : b ≤ a := hs'.1 (x, a) hm'
      obtain ⟨pre, post, h1, h2, h3⟩ := fold_label hpad hlbl L (cells ++ padTo pad c b ++ [(lbl y, 0)])
        (max b c) hs'.2 hm' (by omega) (fun p hp => hone p (List.mem_cons_of_mem _ hp))
      refine ⟨padTo pad c b ++ [(lbl y, 0)] ++ pre, post, ?_, ?_, ?_⟩
      · simp only [List.foldl_cons, step]; rw [h1]; simp
      · intro z hz
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with (hz | rfl) | hz
        · rw [(padTo_mem pad hz).1]; exact hpad x
        · exact fun h => hyx (hlbl _ _ h)
        · exact h2 z hz
      · have := padTo_sum pad c b
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        omega

/-- The sorted symbols are in address order. -/
theorem sorted (L : List (String × Nat)) : (L.mergeSort le).Pairwise (fun p q => p.2 ≤ q.2) := by
  have := List.pairwise_mergeSort (le := le)
    (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) L
  exact this.imp fun h => by simpa only [le, decide_eq_true_eq] using h

theorem mem_sort {L : List (String × Nat)} {p : String × Nat} : p ∈ L.mergeSort le ↔ p ∈ L :=
  (List.mergeSort_perm L le).mem_iff

/-! ### The start of the executable -/

private theorem foldl_min_le : ∀ (l : List Nat) (m : Nat), l.foldl min m ≤ m ∧ ∀ x ∈ l, l.foldl min m ≤ x
  | [], m => ⟨Nat.le_refl _, by simp⟩
  | x :: l, m => by
    obtain ⟨h1, h2⟩ := foldl_min_le l (min m x)
    refine ⟨by simp only [List.foldl_cons]; omega, fun y hy => ?_⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · exact h2 y hy

theorem exeStart_le (lo : Nat) (syms : List (String × Nat)) : exeStart lo syms ≤ lo :=
  (foldl_min_le _ _).1

theorem exeStart_le_of_mem {lo : Nat} {syms : List (String × Nat)} {p : String × Nat}
    (hp : p ∈ symsBelow lo syms) : exeStart lo syms ≤ p.2 :=
  (foldl_min_le _ _).2 _ (List.mem_map_of_mem hp)

theorem mem_symsBelow {lo : Nat} {syms : List (String × Nat)} {p : String × Nat} :
    p ∈ symsBelow lo syms ↔ p ∈ syms ∧ p.2 < lo := by
  simp [symsBelow]

theorem mem_symsFrom {lo : Nat} {syms : List (String × Nat)} {p : String × Nat} :
    p ∈ symsFrom lo syms ↔ p ∈ syms ∧ lo ≤ p.2 := by
  simp [symsFrom]

theorem symsBelow_of_above {lo : Nat} {syms : List (String × Nat)} (h : ∀ p ∈ syms, lo ≤ p.2) :
    symsBelow lo syms = [] :=
  List.filter_eq_nil_iff.mpr fun p hp => by have := h p hp; simp only [decide_eq_true_eq]; omega

theorem symsFrom_of_above {lo : Nat} {syms : List (String × Nat)} (h : ∀ p ∈ syms, lo ≤ p.2) :
    symsFrom lo syms = syms :=
  List.filter_eq_self.mpr fun p hp => by simpa using h p hp

theorem exeStart_of_above {lo : Nat} {syms : List (String × Nat)} (h : ∀ p ∈ syms, lo ≤ p.2) :
    exeStart lo syms = lo := by
  simp only [exeStart, symsBelow_of_above h, List.map_nil, List.foldl_nil]

theorem placeBelow_of_above {lo : Nat} {syms : List (String × Nat)} (h : ∀ p ∈ syms, lo ≤ p.2) :
    placeBelow pad lbl lo syms = [] := by
  rw [placeBelow_eq, symsBelow_of_above h, exeStart_of_above h]
  simp [padTo]

/-! ### The two cell runs -/

/-- **The cells below the code**: non-empty padding and label cells of the
symbols below `lo`, from `exeStart lo syms` exactly to `lo`. -/
theorem placeBelow_spec (lo : Nat) (syms : List (String × Nat)) :
    (∀ y ∈ placeBelow pad lbl lo syms, (y.1 = pad ∧ 0 < y.2) ∨ ∃ p ∈ symsBelow lo syms, y = (lbl p.1, 0)) ∧
      ((placeBelow pad lbl lo syms).map (·.2)).sum + exeStart lo syms = lo := by
  obtain ⟨new, h1, h2, h3, h4, h5⟩ := fold_spec pad lbl ((symsBelow lo syms).mergeSort le) [] (exeStart lo syms)
  have hB := h5 lo (exeStart_le lo syms) (fun p hp => by
    have := (mem_symsBelow.mp (mem_sort.mp hp)).2; omega)
  rw [placeBelow_eq, h1, List.nil_append]
  refine ⟨fun y hy => ?_, ?_⟩
  · rcases List.mem_append.mp hy with hy | hy
    · rcases h2 y hy with h | ⟨p, hp, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, mem_sort.mp hp, he⟩
    · obtain ⟨rfl, hc⟩ := padTo_mem pad hy
      exact Or.inl ⟨rfl, by simp only; omega⟩
  · have := padTo_sum pad (((symsBelow lo syms).mergeSort le).foldl (step pad lbl) ([], exeStart lo syms)).2 lo
    simp only [List.map_append, List.sum_append]
    omega

/-- **A symbol below the code at its label**: the first label cell named
`x` among the cells below the code, for a symbol `(x, a)` below `lo` and
the only address of `x` there, follows cells (none of them that label)
from `exeStart lo syms` to `a`. -/
theorem placeBelow_label (hpad : ∀ x, pad ≠ lbl x) (hlbl : ∀ x y, lbl x = lbl y → x = y)
    {lo : Nat} {syms : List (String × Nat)} {x : String} {a : Nat} (hm : (x, a) ∈ symsBelow lo syms)
    (hone : ∀ p ∈ symsBelow lo syms, p.1 = x → p.2 = a) :
    ∃ pre post, placeBelow pad lbl lo syms = pre ++ (lbl x, 0) :: post ∧
      (∀ y ∈ pre, y.1 ≠ lbl x) ∧ (pre.map (·.2)).sum + exeStart lo syms = a := by
  obtain ⟨pre, post, h1, h2, h3⟩ := fold_label pad lbl hpad hlbl ((symsBelow lo syms).mergeSort le) []
    (exeStart lo syms) (sorted _) (mem_sort.mpr hm) (exeStart_le_of_mem hm)
    (fun p hp => hone p (mem_sort.mp hp))
  refine ⟨pre, post ++ padTo pad (((symsBelow lo syms).mergeSort le).foldl (step pad lbl)
    ([], exeStart lo syms)).2 lo, ?_, h2, h3⟩
  rw [placeBelow_eq, h1]; simp

/-- **The cells after the code**: non-empty padding and label cells of
`syms`, from `cur` to the largest of `cur` and the symbols' addresses. -/
theorem placeSyms_spec (cur : Nat) (syms : List (String × Nat)) :
    (∀ y ∈ placeSyms pad lbl cur syms, (y.1 = pad ∧ 0 < y.2) ∨ ∃ p ∈ syms, y = (lbl p.1, 0)) ∧
      ∀ B, cur ≤ B → (∀ p ∈ syms, p.2 ≤ B) → ((placeSyms pad lbl cur syms).map (·.2)).sum + cur ≤ B := by
  obtain ⟨new, h1, h2, h3, h4, h5⟩ := fold_spec pad lbl (syms.mergeSort le) [] cur
  rw [placeSyms_eq, h1, List.nil_append]
  refine ⟨fun y hy => ?_, fun B hc hB => ?_⟩
  · rcases h2 y hy with h | ⟨p, hp, he⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, mem_sort.mp hp, he⟩
  · rw [h3]; exact h5 B hc fun p hp => hB p (mem_sort.mp hp)

/-- **A symbol after the code at its label**: the first label cell named `x`
among the cells after the code, for a symbol `(x, a)` at or above `cur`
and the only address of `x`, follows cells (none of them that label) from
`cur` to `a`. -/
theorem placeSyms_label (hpad : ∀ x, pad ≠ lbl x) (hlbl : ∀ x y, lbl x = lbl y → x = y)
    {cur : Nat} {syms : List (String × Nat)} {x : String} {a : Nat} (hm : (x, a) ∈ syms) (hc : cur ≤ a)
    (hone : ∀ p ∈ syms, p.1 = x → p.2 = a) :
    ∃ pre post, placeSyms pad lbl cur syms = pre ++ (lbl x, 0) :: post ∧
      (∀ y ∈ pre, y.1 ≠ lbl x) ∧ (pre.map (·.2)).sum + cur = a := by
  obtain ⟨pre, post, h1, h2, h3⟩ := fold_label pad lbl hpad hlbl (syms.mergeSort le) [] cur (sorted _)
    (mem_sort.mpr hm) hc (fun p hp => hone p (mem_sort.mp hp))
  exact ⟨pre, post, by rw [placeSyms_eq, h1, List.nil_append], h2, h3⟩

/-! ### The layout before symbols below the code -/

/-- **`placeSyms` before symbols below the code**, verbatim: a padding cell before every label
cell, empty for a symbol at the current address. -/
def placeSymsOld (cur : Nat) (syms : List (String × Nat)) : List (D × Nat) :=
  ((syms.mergeSort fun a b => a.2 ≤ b.2).foldl (init := ([], cur)) fun (cells, c) (x, a) =>
    (cells ++ [(pad, a - c), (lbl x, 0)], max a c)).1

private def stepOld (acc : List (D × Nat) × Nat) (xa : String × Nat) : List (D × Nat) × Nat :=
  (acc.1 ++ [(pad, xa.2 - acc.2), (lbl xa.1, 0)], max xa.2 acc.2)

private theorem fold_eq_old : ∀ (L : List (String × Nat)) (cells : List (D × Nat)) (c : Nat),
    (∀ p ∈ L, c < p.2) → L.Pairwise (fun p q => p.2 < q.2) →
    L.foldl (step pad lbl) (cells, c) = L.foldl (stepOld pad lbl) (cells, c)
  | [], _, _, _, _ => rfl
  | (x, a) :: L, cells, c, hL, hs => by
    have ha := hL (x, a) (List.mem_cons_self ..)
    have hs' := List.pairwise_cons.mp hs
    simp only [List.foldl_cons, step, stepOld]
    have hp : padTo pad c a = [(pad, a - c)] := by simp only at ha; simp [padTo, ha]
    rw [hp, List.append_assoc]
    exact fold_eq_old L _ _ (fun p hp => by have := hs'.1 p hp; simp only at ha this ⊢; omega) hs'.2

/-- **`placeSyms` is the old one** when every symbol is above `cur` and
no two share an address (the old padding cells were then all non-empty). -/
theorem placeSyms_eq_old {cur : Nat} {syms : List (String × Nat)} (h : ∀ p ∈ syms, cur < p.2)
    (hnd : (syms.map (·.2)).Nodup) : placeSyms pad lbl cur syms = placeSymsOld pad lbl cur syms := by
  have hnd' : ((syms.mergeSort le).map (·.2)).Nodup := hnd.perm ((List.mergeSort_perm syms le).map _).symm
  have hlt : (syms.mergeSort le).Pairwise (fun p q => p.2 < q.2) := by
    refine (List.Pairwise.and (sorted syms) (List.pairwise_map.mp hnd')).imp fun h => ?_
    omega
  rw [placeSyms_eq]
  show _ = ((syms.mergeSort le).foldl (stepOld pad lbl) ([], cur)).1
  rw [fold_eq_old pad lbl _ _ _ (fun p hp => h p (mem_sort.mp hp)) hlt]

end Generic

end Scc.Cert.PlaceSyms
