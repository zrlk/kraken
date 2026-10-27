/-
**Distinct instructions sit at distinct pcs** (x86-64): the byte-offset
twin of `Spike/Lib/A64RunPc.lean`. In a layout of a cell list (`Lays`), the
`j`-th cell of the run after a label `l` (`Scc.Cert.Rt.X64.run`, the
non-label cells up to the next label) sits at `lab l` plus the sizes of the
`j` cells before it (`pc_runB`); two positions `(l, off)` in runs
(`InRunB`, `off` a cell's byte offset in the run) that differ sit at
different pcs (`pc_ne_of_inRunB`). So pcs named label-relatively (a label
and a byte offset) are told apart by their names alone, at any layout: no
numeric pc table.

- `InRunB cells l off`: `l` labels `cells`, and some cell of its run starts
  `off` bytes after it.
- `inRunB_of_blockAt`: every cell of a block (`blockAt`) is in its run.
- `pc_runB`: the address of the `j`-th cell after the label's.
- `pc_ne_of_inRunB`: distinct positions, distinct pcs.
-/
import Scc.Cert.Rt.LaysX64

namespace Scc.Cert.Rt.X64

open Kraken Kraken.Promising Kraken.Promising.X64

/-- **`(l, off)` is a cell of `cells`**: `l` labels `cells`, and a cell of
the run after its first occurrence starts `off` bytes after it. -/
def InRunB (cells : List (Directive × Nat)) (l : Label) (off : Nat) : Prop :=
  (labelIdx cells l).isSome ∧ ∃ j < (run cells l).length, (((run cells l).take j).map (·.2)).sum = off

/-- **A block's cells are in its run.** -/
theorem inRunB_of_blockAt {cells : List (Directive × Nat)} {l : Label} {k off : Nat} {b : List (Directive × Nat)}
    (h : blockAt cells l k off b = true) {i : Nat} (hi : i < b.length) :
    InRunB cells l (off + ((b.take i).map (·.2)).sum) := by
  simp only [blockAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hoff⟩, hb⟩ := h
  refine ⟨hl, k + i, ?_, ?_⟩
  · have hl' := congrArg List.length hb
    simp only [List.length_take, List.length_drop] at hl'
    omega
  · rw [List.take_add, List.map_append, List.sum_append, hoff]
    congr 2
    conv => rhs; rw [← hb]
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hi)]

/-- The `j`-th cell of the run after `cells[i] = label l`: a non-label cell. -/
theorem getElem_runB {cells : List (Directive × Nat)} {l : Label} {i j : Nat} (hl : labelIdx cells l = some i)
    (hj : j < (run cells l).length) :
    ∃ c, cells[i + 1 + j]? = some c ∧ c.1.isLabel = false := by
  simp only [run, hl] at hj
  refine ⟨_, ?_, by simpa using mem_takeWhile (List.getElem_mem hj)⟩
  rw [← List.getElem?_drop]
  conv => lhs; rw [← List.takeWhile_append_dropWhile (p := fun c : Directive × Nat => !c.1.isLabel)
    (l := cells.drop (i + 1))]
  rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]

/-- **The address of the `j`-th cell after a label's** (`j` at most the
run's length): the label's address plus the sizes of the run's first `j`
cells. -/
theorem pc_runB {exe : _root_.Executable} [hv : Executable.ValidLayout exe] {cells : List (Directive × Nat)}
    {kp : Nat} (hp : Lays exe cells kp) {l : Label} {i j : Nat} (hl : labelIdx cells l = some i)
    (hj : j ≤ (run cells l).length) :
    (_root_.Executable.labels exe).label l + Int64.ofNat (((run cells l).take j).map (·.2)).sum =
      Kraken.Executable.addrOf exe (kp + i + 1 + j) := by
  obtain ⟨⟨z0, hz0⟩, hfirst⟩ := labelIdx_spec hl
  have hz0' := hp.getElem? hz0
  have hzz := hv.label_size _ l z0 hz0'
  subst hzz
  have hlab := Executable.label_addrOf exe l _ hz0' (hp.first hz0 hfirst)
  have hnl : i < cells.length := (List.getElem?_eq_some_iff.mp hz0).1
  obtain ⟨ext, hx⟩ := hp.drop
  have hR : run cells l = (cells.drop (i + 1)).takeWhile (fun c => !c.1.isLabel) := by simp only [run, hl]
  obtain ⟨rest, hsplit⟩ : ∃ rest, cells.drop (i + 1) = run cells l ++ rest :=
    ⟨_, by rw [hR]; exact (List.takeWhile_append_dropWhile).symm⟩
  have hd : exe.2.drop (kp + i + 1) = run cells l ++ (rest ++ ext) := by
    rw [show kp + i + 1 = kp + (i + 1) by omega, ← List.drop_drop, hx,
      List.drop_append_of_le_length (by omega), hsplit, List.append_assoc]
  have hlen : j ≤ (exe.2.drop (kp + i + 1)).length := by rw [hd]; simp; omega
  have := addrOf_past hz0' j hlen
  rw [hd, List.take_append_of_le_length hj, ← hlab] at this
  exact this.symm

/-- **Distinct positions in runs sit at distinct pcs**: the cells' indices
differ (a run holds no label, so a label's index is not inside another's
run), and a non-label cell occupies bytes. -/
theorem pc_ne_of_inRunB {exe : _root_.Executable} [hv : Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) {l₁ l₂ : Label} {o₁ o₂ : Nat}
    (h₁ : InRunB cells l₁ o₁) (h₂ : InRunB cells l₂ o₂) (hne : (l₁, o₁) ≠ (l₂, o₂)) :
    (_root_.Executable.labels exe).label l₁ + Int64.ofNat o₁ ≠
      (_root_.Executable.labels exe).label l₂ + Int64.ofNat o₂ := by
  obtain ⟨i₁, hi₁⟩ := Option.isSome_iff_exists.mp h₁.1
  obtain ⟨i₂, hi₂⟩ := Option.isSome_iff_exists.mp h₂.1
  obtain ⟨j₁, hj₁, rfl⟩ := h₁.2
  obtain ⟨j₂, hj₂, rfl⟩ := h₂.2
  rw [pc_runB hp hi₁ (Nat.le_of_lt hj₁), pc_runB hp hi₂ (Nat.le_of_lt hj₂)]
  obtain ⟨c₁, hc₁, hn₁⟩ := getElem_runB hi₁ hj₁
  obtain ⟨c₂, hc₂, hn₂⟩ := getElem_runB hi₂ hj₂
  obtain ⟨⟨z₁, hl₁⟩, -⟩ := labelIdx_spec hi₁
  obtain ⟨⟨z₂, hl₂⟩, -⟩ := labelIdx_spec hi₂
  -- the label `l₂` is not inside `l₁`'s run up to `j₁`, and conversely
  have hout : ∀ {ia ib ja : Nat} {la lb : Label} {zb : Nat}, labelIdx cells la = some ia →
      ja < (run cells la).length → cells[ib]? = some (.label lb, zb) → ¬ (ia < ib ∧ ib ≤ ia + 1 + ja) := by
    intro ia ib ja la lb zb ha hja hb ⟨h1, h2⟩
    obtain ⟨y, hy, hyl⟩ := getElem_runB ha (show ib - (ia + 1) < (run cells la).length by omega)
    rw [show ia + 1 + (ib - (ia + 1)) = ib by omega, hb] at hy
    cases hy
    exact Bool.noConfusion hyl
  have hidx : kp + i₁ + 1 + j₁ ≠ kp + i₂ + 1 + j₂ := by
    intro heq
    rcases Nat.lt_trichotomy i₁ i₂ with hlt | heq' | hgt
    · exact hout hi₁ hj₁ hl₂ ⟨hlt, by omega⟩
    · subst heq'
      rw [hl₁] at hl₂
      cases hl₂
      exact hne (by rw [show j₁ = j₂ by omega])
    · exact hout hi₂ hj₂ hl₁ ⟨hgt, by omega⟩
  -- the lower index is a non-label cell, so the addresses differ
  have hlen : ∀ {n : Nat} {c : Directive × Nat}, cells[n]? = some c → kp + n < exe.2.length := by
    intro n c hn
    exact (List.getElem?_eq_some_iff.mp (hp.getElem? hn)).1
  have hlab : ∀ {n : Nat} {c : Directive × Nat}, cells[n]? = some c → c.1.isLabel = false →
      ∀ l z, exe.2[kp + n]? ≠ some (.label l, z) := by
    intro n c hn hc l z h
    rw [hp.getElem? hn] at h
    cases h
    exact Bool.noConfusion hc
  intro heq
  rcases Nat.lt_or_gt_of_ne hidx with hlt | hgt
  · obtain ⟨l, z, hlz⟩ := Kraken.Executable.label_between_of_addrOf_eq exe (Nat.le_refl _) hlt
      (Nat.le_of_lt (by have := hlen hc₂; omega)) heq
    exact hlab hc₁ hn₁ l z (by rw [← hlz]; congr 1; omega)
  · obtain ⟨l, z, hlz⟩ := Kraken.Executable.label_between_of_addrOf_eq exe (Nat.le_refl _) hgt
      (Nat.le_of_lt (by have := hlen hc₁; omega)) heq.symm
    exact hlab hc₂ hn₂ l z (by rw [← hlz]; congr 1; omega)

-- No axioms beyond Lean's.

/-- info: 'Scc.Cert.Rt.X64.pc_ne_of_inRunB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pc_ne_of_inRunB

end Scc.Cert.Rt.X64
