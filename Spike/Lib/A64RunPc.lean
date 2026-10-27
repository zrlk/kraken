/-
**Distinct instructions sit at distinct pcs** (AArch64): in a layout of a
directive list (`Lays`), the `j`-th instruction of the run after a label `l`
(`Scc.Cert.Rt.A64.run`, the instructions up to the next label) sits at
`lab l + 4 j`, the address of its cell (`pc_run`); two positions `(l, j)`
in runs (`InRun`) that differ sit at different pcs (`pc_ne_of_inRun`). So
pcs named label-relatively (a label and an instruction offset) are told
apart by their names alone, at any layout: no numeric pc table.

- `InRun prog l j`: `l` labels `prog` and its run has more than `j` instructions.
- `inRun_of_blockAt`: every instruction of a block (`blockAt`) is in its run.
- `pc_run`: the address of the `j`-th cell after the label's.
- `pc_ne_of_inRun`: distinct positions, distinct pcs.
-/
import Scc.Cert.Rt.LayoutA64

namespace Scc.Cert.Rt.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- **`(l, j)` is an instruction of `prog`**: `l` labels `prog`, and the run
after its first occurrence has more than `j` instructions. -/
def InRun (prog : List Directive) (l : Label) (j : Nat) : Prop :=
  (labelIdx prog l).isSome ∧ j < (run prog l).length

/-- **A block's instructions are in its run.** -/
theorem inRun_of_blockAt {prog : List Directive} {l : Label} {k : Nat} {b : List Directive}
    (h : blockAt prog l k b = true) {i : Nat} (hi : i < b.length) : InRun prog l (k + i) := by
  simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  have hl := congrArg List.length h.2
  simp only [List.length_take, List.length_drop] at hl
  omega

/-- A position of `takeWhile` is the list's there. -/
theorem getElem?_takeWhile {p : Directive → Bool} : ∀ {ds : List Directive} {j : Nat}
    (hj : j < (ds.takeWhile p).length), ds[j]? = some (ds.takeWhile p)[j]
  | [], _, hj => by simp at hj
  | d :: ds, j, hj => by
    by_cases hd : p d = true
    · simp only [List.takeWhile_cons, hd, ↓reduceIte] at hj ⊢
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.length_cons] at hj
        simpa using getElem?_takeWhile (ds := ds) (j := j) (by omega)
    · simp [hd] at hj

/-- The `j`-th instruction of the run after `prog[i] = label l`. -/
theorem getElem_run {prog : List Directive} {l : Label} {i j : Nat} (hl : labelIdx prog l = some i)
    (hj : j < (run prog l).length) : ∃ x, prog[i + 1 + j]? = some (.instr x) := by
  simp only [run, hl] at hj
  have hins := mem_takeWhile (List.getElem_mem hj)
  have hg : prog[i + 1 + j]? = some ((prog.drop (i + 1)).takeWhile isIns)[j] := by
    rw [← getElem?_takeWhile hj, List.getElem?_drop]
  revert hins hg
  generalize ((prog.drop (i + 1)).takeWhile isIns)[j] = d
  intro hins hg
  cases d with
  | instr x => exact ⟨x, hg⟩
  | _ => simp [isIns] at hins

/-- **The address of the `j`-th cell after a label's** (`j` at most the
run's length): the label's address plus `4 j`, the run's cells 4 bytes each. -/
theorem pc_run {exe : Executable} [hv : Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) {l : Label} {i j : Nat} (hl : labelIdx prog l = some i)
    (hj : j ≤ (run prog l).length) :
    (_root_.Executable.labels exe).label l + Int64.ofNat (4 * j) = Kraken.Executable.addrOf exe (kp + (i + 1 + j)) := by
  obtain ⟨hpi, hfi⟩ := labelIdx_spec hl
  obtain ⟨zi, hzi⟩ := getElem?_fst hp hpi
  have hz0 := hv.label_size _ l zi hzi
  subst hz0
  rw [Kraken.Executable.label_addrOf exe l _ hzi (hp.first hpi hfi)]
  induction j with
  | zero =>
    rw [show kp + (i + 1 + 0) = kp + i + 1 by omega, Kraken.Executable.addrOf_succ exe hzi]
  | succ m ih =>
    obtain ⟨x, hx⟩ := getElem_run hl (show m < (run prog l).length by omega)
    obtain ⟨z, hz⟩ := getElem?_fst hp hx
    have h4 : z = 4 := hv.instr_size _ x z hz
    subst h4
    rw [show kp + (i + 1 + (m + 1)) = kp + (i + 1 + m) + 1 by omega, Kraken.Executable.addrOf_succ exe hz,
      ← ih (by omega), Int64.add_assoc, show 4 * (m + 1) = 4 * m + 4 by omega, Int64.ofNat_add]

/-- **Distinct positions in runs sit at distinct pcs**: the cells' indices
differ (a run holds no label, so a label's index is not inside another's
run), and an instruction's cell occupies bytes. -/
theorem pc_ne_of_inRun {exe : Executable} [hv : Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) {l₁ l₂ : Label} {j₁ j₂ : Nat} (h₁ : InRun prog l₁ j₁) (h₂ : InRun prog l₂ j₂)
    (hne : (l₁, j₁) ≠ (l₂, j₂)) :
    (_root_.Executable.labels exe).label l₁ + Int64.ofNat (4 * j₁) ≠
      (_root_.Executable.labels exe).label l₂ + Int64.ofNat (4 * j₂) := by
  obtain ⟨i₁, hi₁⟩ := Option.isSome_iff_exists.mp h₁.1
  obtain ⟨i₂, hi₂⟩ := Option.isSome_iff_exists.mp h₂.1
  have hj₁ := h₁.2
  have hj₂ := h₂.2
  rw [pc_run hp hi₁ (Nat.le_of_lt hj₁), pc_run hp hi₂ (Nat.le_of_lt hj₂)]
  obtain ⟨x₁, hx₁⟩ := getElem_run hi₁ hj₁
  obtain ⟨x₂, hx₂⟩ := getElem_run hi₂ hj₂
  have hl₁ := (labelIdx_spec hi₁).1
  have hl₂ := (labelIdx_spec hi₂).1
  -- the label `l₂` is not inside `l₁`'s run up to `j₁`, and conversely
  have hout : ∀ {ia ib ja : Nat} {la lb : Label}, labelIdx prog la = some ia → ja < (run prog la).length →
      prog[ib]? = some (.label lb) → ¬ (ia < ib ∧ ib ≤ ia + 1 + ja) := by
    intro ia ib ja la lb ha hja hb ⟨h1, h2⟩
    obtain ⟨y, hy⟩ := getElem_run ha (show ib - (ia + 1) < (run prog la).length by omega)
    rw [show ia + 1 + (ib - (ia + 1)) = ib by omega, hb] at hy
    cases hy
  have hidx : kp + (i₁ + 1 + j₁) ≠ kp + (i₂ + 1 + j₂) := by
    intro heq
    rcases Nat.lt_trichotomy i₁ i₂ with hlt | heq' | hgt
    · exact hout hi₁ hj₁ hl₂ ⟨hlt, by omega⟩
    · subst heq'
      rw [hl₁] at hl₂
      cases hl₂
      exact hne (by rw [show j₁ = j₂ by omega])
    · exact hout hi₂ hj₂ hl₁ ⟨hgt, by omega⟩
  -- the lower index is an instruction's cell, so the addresses differ
  have hlen : ∀ {n : Nat} {x : Instr}, prog[n]? = some (.instr x) → kp + n < exe.2.length := by
    intro n x hn
    obtain ⟨z, hz⟩ := getElem?_fst hp hn
    exact (List.getElem?_eq_some_iff.mp hz).1
  intro heq
  rcases Nat.lt_or_gt_of_ne hidx with hlt | hgt
  · obtain ⟨l, z, hlz⟩ := Kraken.Executable.label_between_of_addrOf_eq exe (Nat.le_refl _) hlt
      (Nat.le_of_lt (hlen hx₂)) heq
    obtain ⟨z', hz'⟩ := getElem?_fst hp hx₁
    rw [hz'] at hlz
    cases hlz
  · obtain ⟨l, z, hlz⟩ := Kraken.Executable.label_between_of_addrOf_eq exe (Nat.le_refl _) hgt
      (Nat.le_of_lt (hlen hx₁)) heq.symm
    obtain ⟨z', hz'⟩ := getElem?_fst hp hx₂
    rw [hz'] at hlz
    cases hlz

-- No axioms beyond Lean's.

/-- info: 'Scc.Cert.Rt.A64.pc_ne_of_inRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pc_ne_of_inRun

end Scc.Cert.Rt.A64
