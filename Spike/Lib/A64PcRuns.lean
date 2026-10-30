/-
**Pcs in runs of instructions after labels** (`WCompat.pass`, AArch64): a set of pcs named by labels of a program and
instruction counts after them, and the decided check of whether a pc
`label l + 4k` of the program is in it.

The worker's target store point (`WCompat.pass`) is a set of pcs: the
instructions after the worker's release store. Each node of the worker's
segments knows its pc as a label of the listing plus a count of
instructions; whether that pc is in the set is decided on the listing
alone (`inRuns`), by the instructions' indices in it: in a valid layout,
distinct instructions have distinct addresses (`addrOf_inj`).

- `PcIn runs s`: the pc of `s` is `label l + 4j` with `(l, lo, hi) ∈ runs`
  and `lo ≤ j < hi`, in `s`'s executable.
- `runsOk prog runs`: every run's label is in `prog`, every bound within the
  run of instructions after it (`run`).
- `inRuns prog runs l k`: the instruction `k` after `l` is one of the runs'
  (by index).
- `label_add_eq`: `label l + 4k` is the address of the cell `k + 1` after
  the label's.
- `addrOf_inj`: distinct instruction cells have distinct addresses.
- `pcIn_iff`: at `label l + 4k` (`k` within `l`'s run), `PcIn runs` is
  `inRuns`.
-/
import Scc.Cert.Rt.LayoutA64

namespace Spike.Lib.A64.PcRuns

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (Lays isIns labelIdx run labelIdx_spec getElem?_fst mem_takeWhile)

/-- **The pc of `s` is in one of the runs**: `label l + 4j` of `s`'s
executable for a run `(l, lo, hi)` and `lo ≤ j < hi`. -/
def PcIn (runs : List (Label × Nat × Nat)) (s : State) : Prop :=
  ∃ q ∈ runs, ∃ j, q.2.1 ≤ j ∧ j < q.2.2 ∧
    s.st.2 = (_root_.Executable.labels s.exe).label q.1 + Int64.ofNat (4 * j)

/-- The index in `prog` of the instruction `k` after `label l`. -/
def runIdx (prog : List Directive) (l : Label) (k : Nat) : Option Nat := (labelIdx prog l).map (· + 1 + k)

/-- **The runs are in `prog`**: each label is, each count within the run of
instructions after it. -/
def runsOk (prog : List Directive) (runs : List (Label × Nat × Nat)) : Bool :=
  runs.all fun q => (labelIdx prog q.1).isSome && decide (q.2.2 ≤ (run prog q.1).length)

/-- **The instruction `k` after `label l` is one of the runs'** (by index). -/
def inRuns (prog : List Directive) (runs : List (Label × Nat × Nat)) (l : Label) (k : Nat) : Bool :=
  runs.any fun q => (List.range q.2.2).any fun j => decide (q.2.1 ≤ j) && runIdx prog q.1 j == runIdx prog l k

/-! ## Addresses of the instructions of a run -/

section Addr

variable {exe : _root_.Executable} [hv : Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}

/-- The instruction `k` of the run after `label l` is the directive `i + 1 + k`
of `prog` (`i` the label's index), an instruction. -/
theorem run_getElem? {l : Label} {i k : Nat} (hi : labelIdx prog l = some i) (hk : k < (run prog l).length) :
    ∃ d, prog[i + 1 + k]? = some d ∧ isIns d = true := by
  have hr : run prog l = (prog.drop (i + 1)).takeWhile isIns := by simp [run, hi]
  rw [hr] at hk
  obtain ⟨t, ht⟩ := List.takeWhile_prefix (p := isIns) (l := prog.drop (i + 1))
  refine ⟨((prog.drop (i + 1)).takeWhile isIns)[k], ?_, mem_takeWhile (List.getElem_mem hk)⟩
  rw [← List.getElem?_drop]
  conv => lhs; rw [← ht]
  rw [List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

/-- The address after a cell of no bytes, `n` instructions on. -/
theorem addrOf_run {l : Label} {i : Nat} (hp : Lays exe prog kp) (hi : labelIdx prog l = some i) :
    ∀ m, m ≤ (run prog l).length →
      Kraken.Executable.addrOf exe (kp + (i + 1 + m)) = Kraken.Executable.addrOf exe (kp + i) + Int64.ofNat (4 * m)
  | 0, _ => by
    obtain ⟨hpi, -⟩ := labelIdx_spec hi
    obtain ⟨z, hz⟩ := getElem?_fst hp hpi
    have hz0 := hv.label_size _ l z hz
    subst hz0
    rw [show kp + (i + 1 + 0) = kp + i + 1 by omega, Kraken.Executable.addrOf_succ exe hz]
  | m + 1, hm => by
    obtain ⟨d, hd, hdi⟩ := run_getElem? hi (k := m) (by omega)
    obtain ⟨z, hz⟩ := getElem?_fst hp hd
    cases d with
    | instr ins =>
      have hz4 := hv.instr_size _ ins z hz
      subst hz4
      rw [show kp + (i + 1 + (m + 1)) = kp + (i + 1 + m) + 1 by omega, Kraken.Executable.addrOf_succ exe hz,
        addrOf_run hp hi m (by omega), Int64.add_assoc, ← Int64.ofNat_add,
        show 4 * (m + 1) = 4 * m + 4 by omega]
    | _ => simp [isIns] at hdi

/-- **`label l + 4k` is the address of the cell `k + 1` after the label's.** -/
theorem label_add_eq {l : Label} {i k : Nat} (hp : Lays exe prog kp) (hi : labelIdx prog l = some i)
    (hk : k ≤ (run prog l).length) :
    (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = Kraken.Executable.addrOf exe (kp + (i + 1 + k)) := by
  obtain ⟨hpi, hfi⟩ := labelIdx_spec hi
  obtain ⟨z, hz⟩ := getElem?_fst hp hpi
  have hz0 := hv.label_size _ l z hz
  subst hz0
  rw [Kraken.Executable.label_addrOf exe l _ hz (hp.first hpi hfi), addrOf_run hp hi k hk]

omit hv in
/-- A cell's bytes: the bytes before the cells after it are at least its
own after those before it. -/
theorem sizeBefore_lt {a b : Nat} {d : Directive} {z : Nat} (hab : a < b) (hd : exe.2[a]? = some (d, z)) :
    Kraken.Executable.sizeBefore exe a + z ≤ Kraken.Executable.sizeBefore exe b := by
  unfold Kraken.Executable.sizeBefore
  rw [show b = (a + 1) + (b - (a + 1)) by omega, List.take_add, List.map_append, List.sum_append,
    List.take_add_one, hd]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil]
  omega

/-- **Distinct instruction cells have distinct addresses.** -/
theorem addrOf_inj {a b : Nat} {ia ib : Instr} {za zb : Nat} (ha : exe.2[a]? = some (.instr ia, za))
    (hb : exe.2[b]? = some (.instr ib, zb)) (h : Kraken.Executable.addrOf exe a = Kraken.Executable.addrOf exe b) :
    a = b := by
  have hs := Kraken.Executable.sizeBefore_eq_of_addrOf_eq exe h
  have hza := hv.instr_size _ ia za ha
  have hzb := hv.instr_size _ ib zb hb
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have := sizeBefore_lt hab ha; omega
  · exact hab
  · have := sizeBefore_lt hab hb; omega

omit hv in
/-- The cell of the instruction `k` after `label l` is an instruction. -/
theorem run_cell {l : Label} {i k : Nat} (hp : Lays exe prog kp) (hi : labelIdx prog l = some i)
    (hk : k < (run prog l).length) : ∃ ins z, exe.2[kp + (i + 1 + k)]? = some (.instr ins, z) := by
  obtain ⟨d, hd, hdi⟩ := run_getElem? hi hk
  obtain ⟨z, hz⟩ := getElem?_fst hp hd
  cases d with
  | instr ins => exact ⟨ins, z, hz⟩
  | _ => simp [isIns] at hdi

/-- **At `label l + 4k` (`k` within `l`'s run), `PcIn runs` is `inRuns`**:
decided on `prog` alone. -/
theorem pcIn_iff (hp : Lays exe prog kp) {runs : List (Label × Nat × Nat)} (hok : runsOk prog runs = true)
    {s : State} (he : s.exe = exe) {l : Label} {k : Nat} (hl : (labelIdx prog l).isSome)
    (hk : k < (run prog l).length)
    (hpc : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) :
    PcIn runs s ↔ inRuns prog runs l k = true := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hl
  rw [label_add_eq hp hi (Nat.le_of_lt hk)] at hpc
  obtain ⟨ins, z, hc⟩ := run_cell hp hi hk
  simp only [runsOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  simp only [inRuns, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, runIdx, hi]
  unfold PcIn
  rw [he]
  constructor
  · rintro ⟨q, hq, j, hlo, hj, he'⟩
    obtain ⟨hql, hqn⟩ := hok q hq
    obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp hql
    rw [label_add_eq hp hi' (by omega), hpc] at he'
    obtain ⟨ins', z', hc'⟩ := run_cell hp hi' (k := j) (by omega)
    have := addrOf_inj hc hc' he'
    exact ⟨q, hq, j, hj, hlo, by rw [hi']; simp only [Option.map_some, Option.some.injEq]; omega⟩
  · rintro ⟨q, hq, j, hj, hlo, hij⟩
    obtain ⟨hql, hqn⟩ := hok q hq
    obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp hql
    rw [hi'] at hij
    simp only [Option.map_some, Option.some.injEq] at hij
    refine ⟨q, hq, j, hlo, hj, ?_⟩
    rw [hpc, label_add_eq hp hi' (by omega)]
    congr 2
    omega

end Addr

end Spike.Lib.A64.PcRuns
