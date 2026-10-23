import Kraken.CodeAt

/-!
# Code at labels of an emitted x86-64 program

The x64 counterpart of `LayoutA64.lean`, for laid-out programs whose
instructions have the assembler's sizes. The checks are on the laid-out
cell list (`exe.2`: each directive with its size, from scc's certificate
size table), decided by evaluation (`decide +kernel`) once per program:

- `blockAt cells l k off b`: the cells `b` are the run of non-label cells
  starting `k` cells after the first `label l`, and `off` is the size of
  the `k` cells before them; `codeAt_blockAt` gives
  `codeAt exe (label l + off) = b ++ rest`, the form Kraken's cell lemmas
  (`CellAt`, `codeAt_segment`) consume;
- `labelGap cells a b off`: the first `label b` follows the first
  `label a` after non-label cells of total size `off`; `label_labelGap`
  gives `label b = label a + off`.

The checks scan the cell list up to the label once per block; no
whole-program size computation.
-/

namespace Scc.Cert.Rt.X64

open Kraken

/-- The index of the first cell `label l`. -/
def labelIdx : List (Directive × Nat) → Label → Option Nat
  | [], _ => none
  | c :: cs, l => if c.1 = .label l then some 0 else (labelIdx cs l).map (· + 1)

/-- The cells after the first `label l`, up to the next label. -/
def run (cells : List (Directive × Nat)) (l : Label) : List (Directive × Nat) :=
  match labelIdx cells l with
  | some n => (cells.drop (n + 1)).takeWhile (fun c => !c.1.isLabel)
  | none => []

/-- `b` is the run after `label l` from its `k`-th cell on (a prefix), and
the cells before it take `off` bytes. -/
def blockAt (cells : List (Directive × Nat)) (l : Label) (k off : Nat) (b : List (Directive × Nat)) : Bool :=
  (labelIdx cells l).isSome && (((run cells l).take k).map (·.2)).sum == off &&
    decide (((run cells l).drop k).take b.length = b)

/-- The first `label b` follows the first `label a` after `n` non-label
cells of total size `off`. -/
def labelGap (cells : List (Directive × Nat)) (a b : Label) (n off : Nat) : Bool :=
  match labelIdx cells a, labelIdx cells b with
  | some i, some j =>
    j == i + 1 + n && ((cells.drop (i + 1)).take n).all (fun c => !c.1.isLabel) &&
      (((cells.drop (i + 1)).take n).map (·.2)).sum == off
  | _, _ => false

theorem labelIdx_spec : ∀ {cells : List (Directive × Nat)} {l : Label} {n : Nat}, labelIdx cells l = some n →
    (∃ z, cells[n]? = some (.label l, z)) ∧ ∀ c ∈ cells.take n, c.1 ≠ .label l
  | [], _, _, h => by simp [labelIdx] at h
  | c :: cs, l, n, h => by
    unfold labelIdx at h
    split at h
    · cases h; obtain ⟨d, z⟩ := c; simp_all
    · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨h1, h2⟩ := labelIdx_spec hm
      refine ⟨by simpa using h1, ?_⟩
      intro c' hc'
      rw [List.take_succ_cons, List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · assumption
      · exact h2 c' hc'

theorem mem_takeWhile {α} {p : α → Bool} : ∀ {l : List α} {x : α}, x ∈ l.takeWhile p → p x = true
  | [], _, h => by simp at h
  | y :: l, x, h => by
    by_cases hy : p y = true
    · simp only [List.takeWhile_cons, hy, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact hy
      · exact mem_takeWhile h
    · simp [hy] at h

/-- The address `m` cells past a label at index `i`: the label takes no
bytes, then the sizes of the cells. -/
theorem addrOf_past {e : Kraken.Executable Directive} [hv : Executable.ValidLayout e] {i : Nat} {l : Label}
    (hi : e.2[i]? = some (.label l, 0)) :
    ∀ m, m ≤ (e.2.drop (i + 1)).length →
      e.addrOf (i + 1 + m) = e.addrOf i + Int64.ofNat (((e.2.drop (i + 1)).take m).map (·.2)).sum
  | 0, _ => by simpa using Executable.addrOf_succ e hi
  | m + 1, hm => by
    have hlt : m < (e.2.drop (i + 1)).length := by omega
    have hc : e.2[i + 1 + m]? = some (e.2.drop (i + 1))[m] := by
      rw [← List.getElem?_drop, List.getElem?_eq_getElem hlt]
    rw [show i + 1 + (m + 1) = (i + 1 + m) + 1 by omega, Executable.addrOf_succ e hc,
      addrOf_past hi m (by omega), List.take_add_one, List.getElem?_eq_getElem hlt]
    simp only [List.map_append, List.sum_append, Option.toList_some, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc]
    rfl

/-- The cells from index `n` of the run after a label at `i`. -/
theorem drop_run {cells : List (Directive × Nat)} {i k : Nat} :
    cells.drop (i + 1 + k) = ((cells.drop (i + 1)).takeWhile (fun c => !c.1.isLabel)).drop k ++
      (cells.drop (i + 1)).dropWhile (fun c => !c.1.isLabel) ∨
    ((cells.drop (i + 1)).takeWhile (fun c => !c.1.isLabel)).length < k := by
  rcases Nat.lt_or_ge ((cells.drop (i + 1)).takeWhile (fun c => !c.1.isLabel)).length k with h | h
  · exact .inr h
  · left
    conv => lhs; rw [← List.drop_drop,
      ← List.takeWhile_append_dropWhile (p := fun c => !c.1.isLabel) (l := cells.drop (i + 1))]
    rw [List.drop_append_of_le_length h]

/-- **A block of the run after a label is the code at its address.** -/
theorem codeAt_blockAt {exe : Kraken.Executable Directive} [hv : Executable.ValidLayout exe] {l : Label}
    {k off : Nat} {b : List (Directive × Nat)} (h : blockAt exe.2 l k off b = true) :
    ∃ rest, exe.codeAt ((_root_.Executable.labels exe).label l + Int64.ofNat off) = b ++ rest := by
  simp only [blockAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hoff⟩, hb⟩ := h
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨⟨z, hz⟩, hfirst⟩ := labelIdx_spec hn
  have hz0 := hv.label_size n l z hz
  subst hz0
  simp only [run, hn] at hoff hb
  generalize hR : (exe.2.drop (n + 1)).takeWhile (fun c => !c.1.isLabel) = R at hoff hb
  by_cases hk : k ≤ R.length
  · have hRlen : R.length ≤ (exe.2.drop (n + 1)).length := by
      rw [← hR]; exact (List.takeWhile_prefix _).length_le
    have hpre : R.take k = (exe.2.drop (n + 1)).take k := by
      rw [← hR]
      conv => rhs; rw [← List.takeWhile_append_dropWhile (p := fun c => !c.1.isLabel) (l := exe.2.drop (n + 1))]
      rw [List.take_append_of_le_length (by rw [hR]; exact hk)]
    have hnlen : n < exe.2.length := by
      rcases Nat.lt_or_ge n exe.2.length with hc | hc
      · exact hc
      · rw [List.getElem?_eq_none hc] at hz; cases hz
    rw [Executable.label_addrOf exe l n hz hfirst, ← hoff, hpre,
      ← addrOf_past hz k (by omega), Executable.codeAt_addrOf_drop exe (by simp at hRlen ⊢; omega)]
    rcases (drop_run (cells := exe.2) (i := n) (k := k)) with hd | hd
    · rw [hd, hR]
      cases hRk : R.drop k with
      | nil =>
        rw [hRk] at hb
        simp only [List.take_nil] at hb
        exact ⟨_, by rw [← hb]; rfl⟩
      | cons c cs =>
        have hc : c.1.isLabel = false := by
          have := mem_takeWhile (p := fun c => !c.1.isLabel) (x := c)
            (by rw [hR]; exact List.mem_of_mem_drop (i := k) (by rw [hRk]; exact List.mem_cons_self ..))
          simpa using this
        rw [List.cons_append, List.dropWhile_cons, hc]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hRk] at hb
        refine ⟨((c :: cs).drop b.length) ++ (exe.2.drop (n + 1)).dropWhile (fun c => !c.1.isLabel), ?_⟩
        show (c :: cs) ++ _ = _
        obtain ⟨m, hm⟩ : ∃ m, b.length = m := ⟨_, rfl⟩
        rw [hm] at hb ⊢
        rw [← hb, ← List.append_assoc, List.take_append_drop]
    · rw [hR] at hd; omega
  · -- past the run: `b` is empty
    rw [List.drop_eq_nil_of_le (by omega), List.take_nil] at hb
    exact ⟨_, by rw [← hb]; rfl⟩

/-- `codeAt_blockAt` for an executable whose cells are given. -/
theorem codeAt_blockAt_of {exe : Kraken.Executable Directive} [Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} (hc : exe.2 = cells) {l : Label} {k off : Nat} {b : List (Directive × Nat)}
    (h : blockAt cells l k off b = true) :
    ∃ rest, exe.codeAt ((_root_.Executable.labels exe).label l + Int64.ofNat off) = b ++ rest :=
  codeAt_blockAt (hc ▸ h)

/-- A block has no label cell. -/
theorem blockAt_noLabel {cells : List (Directive × Nat)} {l : Label} {k off : Nat} {b : List (Directive × Nat)}
    (h : blockAt cells l k off b = true) : ∀ c ∈ b, c.1.isLabel = false := by
  simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq] at h
  intro c hc
  rw [← h.2] at hc
  unfold run at hc
  split at hc
  · have := mem_takeWhile (List.mem_of_mem_drop (List.mem_of_mem_take hc))
    simpa using this
  · simp at hc

/-- **The distance between two labels.** -/
theorem label_labelGap {exe : Kraken.Executable Directive} [hv : Executable.ValidLayout exe] {a b : Label}
    {n off : Nat} (h : labelGap exe.2 a b n off = true) :
    (_root_.Executable.labels exe).label b = (_root_.Executable.labels exe).label a + Int64.ofNat off := by
  unfold labelGap at h
  split at h
  next i j hi hj =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, -⟩, rfl⟩ := h
    obtain ⟨⟨zi, hzi⟩, hfi⟩ := labelIdx_spec hi
    obtain ⟨⟨zj, hzj⟩, hfj⟩ := labelIdx_spec hj
    have := hv.label_size i a zi hzi
    have := hv.label_size _ b zj hzj
    subst zi zj
    have hlen : n ≤ (exe.2.drop (i + 1)).length := by
      rcases Nat.lt_or_ge (i + 1 + n) exe.2.length with hc | hc
      · simp; omega
      · rw [List.getElem?_eq_none hc] at hzj; cases hzj
    rw [Executable.label_addrOf exe a i hzi hfi, Executable.label_addrOf exe b _ hzj hfj, addrOf_past hzi n hlen]
  next => simp at h

end Scc.Cert.Rt.X64
