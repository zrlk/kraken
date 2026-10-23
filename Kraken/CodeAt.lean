/-
`codeAt` on a laid-out executable, by index.

`Executable.codeAt e pc` (the cells at `pc` past the labels there) is defined
through `withAddresses`, which is well-founded recursion and does not reduce.
These lemmas compute it from the directive list `e.2` instead, under
`ValidLayout e`:

- `codeAt_start`: at the start address, the list past leading labels;
- `codeAt_addrOf_drop`: at the address of index `n`, the list from `n` past labels;
- `codeAt_pos`: a nonempty `codeAt` is a cell of the list at its own address;
- `codeAt_succ`: past a cell `(d, z)` (`pc + z`) is the rest past labels;
- `codeAt_label`: at a label's address, the list behind the label past labels;
- `codeAt_segment`: a label-free run of cells at `pc`, cell `j` at
  `pc + (sizes of the cells before j)`;
- `codeAt_ne_end`: a cell's address is not the end of the text.

The AArch64 twin is `Kraken/AArch64/WP/CodeAt.lean` (which also has the
4-byte forms `codeAt_segment4` and `codeAt_instr_size`).
-/
import Kraken.Step

namespace Kraken.Executable

private theorem ofNat_add' (a b : Nat) : Int64.ofNat (a + b) = Int64.ofNat a + Int64.ofNat b := by
  apply Int64.toBitVec_inj.mp
  simp

/-- A label cell occupies no bytes: the next index has the same address. -/
private theorem addrOf_succ_label (e : Kraken.Executable Directive) [hv : ValidLayout e] {n : Nat}
    {c : Directive × Nat} (hc : e.2[n]? = some c) (hl : c.1.isLabel = true) :
    e.addrOf (n + 1) = e.addrOf n := by
  obtain ⟨d, z⟩ := c
  cases d with
  | label l =>
    rw [addrOf_succ e hc, hv.label_size n l z hc]
    show e.addrOf n + 0 = _
    exact Int64.add_zero _
  | _ => simp [Directive.isLabel] at hl

/-- Every cell in `[j, n)` a label: indices `j` and `n` share an address. -/
private theorem addrOf_eq_of_labels (e : Kraken.Executable Directive) [ValidLayout e] {j : Nat} :
    ∀ {n : Nat}, j ≤ n → (∀ i, j ≤ i → i < n → ∃ c, e.2[i]? = some c ∧ c.1.isLabel = true) →
      e.addrOf n = e.addrOf j
  | 0, h, _ => by rw [Nat.le_zero.mp h]
  | n + 1, h, hl => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · obtain ⟨c, hc, hcl⟩ := hl n (by omega) (by omega)
      rw [addrOf_succ_label e hc hcl]
      exact addrOf_eq_of_labels e (by omega) fun i hi hin => hl i hi (by omega)
    · rw [h]

/-- `dropWhile` past a run of cells satisfying the predicate. -/
private theorem dropWhile_drop_of_all {α} {p : α → Bool} {l : List α} {j : Nat} :
    ∀ {n : Nat}, j ≤ n → n ≤ l.length → (∀ i, j ≤ i → i < n → ∃ c, l[i]? = some c ∧ p c = true) →
      (l.drop j).dropWhile p = (l.drop n).dropWhile p
  | 0, h, _, _ => by rw [Nat.le_zero.mp h]
  | n + 1, h, hn, hl => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [dropWhile_drop_of_all (n := n) (by omega) (by omega) fun i hi hin => hl i hi (by omega)]
      obtain ⟨c, hc, hpc⟩ := hl n (by omega) (by omega)
      rw [List.drop_eq_getElem_cons (by omega), List.dropWhile_cons]
      have : l[n] = c := by rw [List.getElem?_eq_getElem (by omega)] at hc; exact Option.some.inj hc
      simp [this, hpc]
    · rw [h]

/-- A nonempty `dropWhile` of a suffix: its head is a cell at or after the
cut, every cell between satisfying the predicate. -/
private theorem dropWhile_drop_eq_cons {α} {p : α → Bool} :
    ∀ {l : List α} {k : Nat} {x : α} {r : List α}, (l.drop k).dropWhile p = x :: r →
      ∃ m, k ≤ m ∧ l[m]? = some x ∧ r = l.drop (m + 1) ∧
        ∀ i, k ≤ i → i < m → ∃ c, l[i]? = some c ∧ p c = true
  | [], k, x, r, h => by simp at h
  | a :: l, 0, x, r, h => by
    rw [List.drop_zero, List.dropWhile_cons] at h
    by_cases ha : p a
    · simp only [ha, ite_true] at h
      obtain ⟨m, -, hm, hr, hb⟩ := dropWhile_drop_eq_cons (l := l) (k := 0) (by simpa using h)
      refine ⟨m + 1, by omega, by simpa using hm, by simpa using hr, fun i _ hi => ?_⟩
      cases i with
      | zero => exact ⟨a, rfl, ha⟩
      | succ i => simpa using hb i (by omega) (by omega)
    · simp only [ha, ite_false, Bool.false_eq_true] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨0, Nat.le_refl _, rfl, rfl, fun i h1 h2 => by omega⟩
  | a :: l, k + 1, x, r, h => by
    rw [List.drop_succ_cons] at h
    obtain ⟨m, hkm, hm, hr, hb⟩ := dropWhile_drop_eq_cons h
    exact ⟨m + 1, by omega, by simpa using hm, by simpa using hr,
      fun i hi him => by
        obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        simpa using hb i (by omega) (by omega)⟩

/-- The head of a nonempty `dropWhile` fails the predicate. -/
private theorem dropWhile_eq_cons_head {α} {p : α → Bool} :
    ∀ {l : List α} {x : α} {r : List α}, l.dropWhile p = x :: r → p x = false
  | [], _, _, h => by simp at h
  | a :: l, x, r, h => by
    rw [List.dropWhile_cons] at h
    by_cases ha : p a
    · simp only [ha, ite_true] at h
      exact dropWhile_eq_cons_head h
    · simp only [ha, ite_false, Bool.false_eq_true] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      simpa using ha

/-- **`codeAt` at the start address**: the directive list past its leading
labels. Any executable. -/
theorem codeAt_start (e : Kraken.Executable Directive) :
    e.codeAt e.1 = e.2.dropWhile (fun c => c.1.isLabel) := by
  obtain ⟨a, ds⟩ := e
  unfold codeAt directivesFromAddress
  simp only
  rw [withAddresses_dropWhile_start, withAddresses_map_snd]

/-- **`codeAt` at the address of index `n`**: the directive list from `n` on,
past labels. -/
theorem codeAt_addrOf_drop (e : Kraken.Executable Directive) [ValidLayout e] {n : Nat} (hn : n ≤ e.2.length) :
    e.codeAt (e.addrOf n) = (e.2.drop n).dropWhile (fun c => c.1.isLabel) := by
  obtain ⟨j, hjn, hcut, hlab⟩ := exists_cut e hn
  unfold codeAt
  rw [hcut]
  refine dropWhile_drop_of_all hjn hn fun i hi hin => ?_
  obtain ⟨l, z, h⟩ := hlab i hi hin
  exact ⟨_, h, rfl⟩

/-- **A cell of `codeAt` is a cell of the directive list at its address**:
index `m` holds it, `pc` is the address of `m`, and the rest of `codeAt` is
the list from `m + 1` on. -/
theorem codeAt_pos (e : Kraken.Executable Directive) [ValidLayout e] {pc : Int64} {d : Directive} {z : Nat}
    {rest : List (Directive × Nat)} (h : e.codeAt pc = (d, z) :: rest) :
    ∃ m, m < e.2.length ∧ e.addrOf m = pc ∧ e.2[m]? = some (d, z) ∧ rest = e.2.drop (m + 1) := by
  have hne : e.directivesFromAddress pc ≠ [] := by
    intro h0
    unfold codeAt at h
    rw [h0] at h
    simp at h
  obtain ⟨k, -, hk, hdfa⟩ := exists_pos_of_directivesFromAddress e hne
  unfold codeAt at h
  rw [hdfa] at h
  obtain ⟨m, hkm, hm, hr, hlab⟩ := dropWhile_drop_eq_cons h
  have hlt : m < e.2.length := by
    rcases Nat.lt_or_ge m e.2.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hm; cases hm
  exact ⟨m, hlt, by rw [addrOf_eq_of_labels e hkm hlab, hk], hm, hr⟩

/-- **The successor of a cell**: `codeAt` behind the cell `(d, z)` at `pc`,
i.e. at `pc + z`, is the rest past labels. -/
theorem codeAt_succ (e : Kraken.Executable Directive) [ValidLayout e] {pc : Int64} {d : Directive} {z : Nat}
    {rest : List (Directive × Nat)} (h : e.codeAt pc = (d, z) :: rest) :
    e.codeAt (pc + .ofNat z) = rest.dropWhile (fun c => c.1.isLabel) := by
  obtain ⟨m, hm, rfl, hd, rfl⟩ := codeAt_pos e h
  rw [← addrOf_succ e hd, codeAt_addrOf_drop e (by omega)]

/-- **`codeAt` at a label**: the directive list behind the label's first
occurrence, past labels. -/
theorem codeAt_label (e : Kraken.Executable Directive) [hv : ValidLayout e] {l : Label} {n z : Nat}
    (hn : e.2[n]? = some (.label l, z)) (hfirst : ∀ dz ∈ e.2.take n, dz.1 ≠ Directive.label l) :
    e.codeAt ((_root_.Executable.labels e).label l) = (e.2.drop (n + 1)).dropWhile (fun c => c.1.isLabel) := by
  have hz := hv.label_size n l z hn
  subst hz
  have hlt : n < e.2.length := by
    rcases Nat.lt_or_ge n e.2.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at hn; cases hn
  rw [label_addrOf e l n hn hfirst, codeAt_addrOf_drop e (by omega), List.drop_eq_getElem_cons hlt,
    List.dropWhile_cons]
  have : e.2[n] = (.label l, 0) := by rw [List.getElem?_eq_getElem hlt] at hn; exact Option.some.inj hn
  simp [this, Directive.isLabel]

/-- **A label-free segment**: if `codeAt` at `pc` begins with the cells `cs`,
none a label, then cell `j` of `cs` is at `pc` plus the sizes of the cells
before it, with the rest of `cs` and then `rest` behind it. -/
theorem codeAt_segment (e : Kraken.Executable Directive) [ValidLayout e] {pc : Int64}
    {cs rest : List (Directive × Nat)} (h : e.codeAt pc = cs ++ rest)
    (hcs : ∀ c ∈ cs, c.1.isLabel = false) :
    ∀ j, j < cs.length → e.codeAt (pc + .ofNat ((cs.take j).map (·.2)).sum) = cs.drop j ++ rest
  | 0, _ => by
    rw [List.take_zero, List.map_nil, List.sum_nil, show Int64.ofNat 0 = 0 from rfl, Int64.add_zero,
      List.drop_zero, h]
  | j + 1, hj => by
    have ih := codeAt_segment e h hcs j (by omega)
    rw [List.drop_eq_getElem_cons (by omega), List.cons_append] at ih
    have hs := codeAt_succ e ih
    simp only [List.get_eq_getElem] at hs
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, List.map_append,
      List.sum_append, List.map_singleton, List.sum_singleton, ofNat_add', ← Int64.add_assoc, hs,
      List.drop_eq_getElem_cons (by omega), List.cons_append, List.dropWhile_cons,
      hcs _ (List.getElem_mem (by omega))]
    simp

private theorem sum_take_succ_le (l : List (Directive × Nat)) {m : Nat} {c : Directive × Nat}
    (hc : l[m]? = some c) : ((l.take m).map (·.2)).sum + c.2 ≤ (l.map (·.2)).sum := by
  conv => rhs; rw [← List.take_append_drop (m + 1) l]
  rw [List.take_add_one, hc]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton]
  omega

/-- **A cell is short of the end of the text**: its address is not the start
plus the total size. -/
theorem codeAt_ne_end (e : Kraken.Executable Directive) [hv : ValidLayout e] {pc : Int64} {d : Directive}
    {z : Nat} {rest : List (Directive × Nat)} (h : e.codeAt pc = (d, z) :: rest) :
    pc ≠ e.1 + .ofNat (e.2.map (·.2)).sum := by
  obtain ⟨m, -, rfl, hm, -⟩ := codeAt_pos e h
  have hnl : ∀ l, d ≠ Directive.label l := by
    intro l hl
    subst hl
    unfold codeAt at h
    have := dropWhile_eq_cons_head h
    simp [Directive.isLabel] at this
  have hz : 0 < z := hv.instr_size m d z hm hnl
  have hle := sum_take_succ_le e.2 hm
  have hw := hv.no_wrap
  intro heq
  have h4 := congrArg Int64.toBitVec heq
  simp only [addrOf, sizeBefore, Int64.toBitVec_add, Int64.toBitVec_ofNat'] at h4
  have h5 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp h4)
  simp only [BitVec.toNat_ofNat] at h5
  simp only at hle
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h5
  omega

end Kraken.Executable
