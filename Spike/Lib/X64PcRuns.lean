/-
**Pcs in byte ranges after labels on x86-64** (the x64 twin of
`Spike/Lib/A64PcRuns.lean`, `WCompat.pass`): a set of pcs named by labels of
a list of code cells and byte offsets after them, and the decided check of
whether a pc `label l + b` of the cells is in it.

The worker's target store point (`WCompat.pass`) is a set of pcs: the
instructions after the worker's release store. Each node of the worker's
segments knows its pc as a label of the listing plus a byte offset; whether
that pc is in the set is decided on the listing alone (`inRuns`), by the
bytes' positions in it: the cells' bytes fit the address space
(`ValidLayout.no_wrap`), so distinct positions have distinct addresses.

- `labelPos cells l`: the bytes of the cells before the first `label l`;
  `cellsSize cells`: all their bytes.
- `PcIn runs s`: the pc of `s` is `label l + b` with `(l, lo, hi) ∈ runs`
  and `lo ≤ b < hi`, in `s`'s executable.
- `runsOk cells runs`: every run's label is in `cells`, every bound within
  the cells' bytes.
- `inRuns cells runs l b`: the byte `b` after `l` is one of the runs' (by
  position).
- `label_eq`: `label l` is the cells' base plus `labelPos`; `pcIn_iff`: at
  `label l + b` (within the cells' bytes), `PcIn runs` is `inRuns`.

**Unlike AArch64** (forced by the x64 shape): instructions have varying
sizes, so a run is a range of bytes after its label (AArch64: a range of
instruction counts, the pc `label l + 4j`), and positions are compared as
byte counts (AArch64: cell indices, `addrOf_inj`). A range may span labels;
each byte of the run's range is a pc of the set.
-/
import Scc.Cert.Rt.LaysX64

namespace Spike.Lib.X64.PcRuns

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays labelIdx labelIdx_spec)

/-- The bytes of the cells before the first `label l`. -/
def labelPos (cells : List (Directive × Nat)) (l : Label) : Option Nat :=
  (labelIdx cells l).map fun i => ((cells.take i).map (·.2)).sum

/-- All the cells' bytes. -/
def cellsSize (cells : List (Directive × Nat)) : Nat := (cells.map (·.2)).sum

/-- **The pc of `s` is in one of the runs**: `label l + b` of `s`'s
executable for a run `(l, lo, hi)` and `lo ≤ b < hi`. -/
def PcIn (runs : List (Label × Nat × Nat)) (s : State) : Prop :=
  ∃ q ∈ runs, ∃ b, q.2.1 ≤ b ∧ b < q.2.2 ∧
    s.st.2 = (_root_.Executable.labels s.exe).label q.1 + Int64.ofNat b

/-- The position `p + b` is in the run `q` (at `labelPos … q.1 = pq`). -/
def posIn (pq : Option Nat) (q : Label × Nat × Nat) (x : Nat) : Bool :=
  match pq with
  | some p' => decide (p' + q.2.1 ≤ x) && decide (x < p' + q.2.2)
  | none => false

/-- **The runs are in `cells`**: each label is, each bound within the cells'
bytes. -/
def runsOk (cells : List (Directive × Nat)) (runs : List (Label × Nat × Nat)) : Bool :=
  runs.all fun q => match labelPos cells q.1 with
    | some p => decide (p + q.2.2 ≤ cellsSize cells)
    | none => false

/-- **The byte `b` after `label l` is one of the runs'** (by position). -/
def inRuns (cells : List (Directive × Nat)) (runs : List (Label × Nat × Nat)) (l : Label) (b : Nat) : Bool :=
  match labelPos cells l with
  | some p => runs.any fun q => posIn (labelPos cells q.1) q (p + b)
  | none => false

/-! ## Addresses of the bytes after a label -/

section Addr

variable {exe : _root_.Executable} [hv : Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}

/-- The cells' bytes, after the first `kp` cells', fit the address space. -/
theorem lays_size (hp : Lays exe cells kp) : Executable.sizeBefore exe kp + cellsSize cells < 2 ^ 64 := by
  have hw := hv.no_wrap
  obtain ⟨pre, ext, he, hk, -⟩ := hp
  unfold Executable.sizeBefore cellsSize
  rw [he] at hw ⊢
  subst hk
  simp only [List.append_assoc, List.take_left, List.map_append, List.sum_append] at hw ⊢
  omega

/-- **`label l` is the cells' base plus the bytes before it.** -/
theorem label_eq (hp : Lays exe cells kp) {l : Label} {p : Nat} (hl : labelPos cells l = some p) :
    (_root_.Executable.labels exe).label l = exe.1 + Int64.ofNat (Executable.sizeBefore exe kp + p) := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨⟨z, hz⟩, hf⟩ := labelIdx_spec hi
  have hz' := hp.getElem? hz
  have hz0 := hv.label_size _ l z hz'
  subst hz0
  have hil : i ≤ cells.length := by
    rcases Nat.lt_or_ge i cells.length with hc | hc
    · exact Nat.le_of_lt hc
    · rw [List.getElem?_eq_none hc] at hz; cases hz
  rw [Executable.label_addrOf exe l _ hz' (hp.first hz hf)]
  unfold Executable.addrOf Executable.sizeBefore
  rw [hp.take_add hil, List.map_append, List.sum_append]

omit hv in
/-- `c + Int64.ofNat ·` is injective below `2 ^ 64`. -/
theorem ofNat_inj {c : Int64} {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : c + Int64.ofNat a = c + Int64.ofNat b) : a = b := by
  have h4 := congrArg Int64.toBitVec h
  simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat'] at h4
  have h1 := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp h4)
  simp only [BitVec.toNat_ofNat] at h1
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1

/-- **At `label l + b` (within the cells' bytes), `PcIn runs` is
`inRuns`**: decided on `cells` alone. -/
theorem pcIn_iff (hp : Lays exe cells kp) {runs : List (Label × Nat × Nat)} (hok : runsOk cells runs = true)
    {s : State} (he : s.exe = exe) {l : Label} {p b : Nat} (hl : labelPos cells l = some p)
    (hb : p + b < cellsSize cells)
    (hpc : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat b) :
    PcIn runs s ↔ inRuns cells runs l b = true := by
  have hS := lays_size hp
  rw [label_eq hp hl, Int64.add_assoc, ← Int64.ofNat_add] at hpc
  simp only [runsOk, List.all_eq_true] at hok
  simp only [inRuns, hl, List.any_eq_true]
  unfold PcIn
  rw [he]
  constructor
  · rintro ⟨q, hq, b', hlo, hhi, he'⟩
    have hq' := hok q hq
    split at hq'
    next p' hp' =>
      simp only [decide_eq_true_eq] at hq'
      rw [label_eq hp hp', Int64.add_assoc, ← Int64.ofNat_add, hpc] at he'
      have := ofNat_inj (by omega) (by omega) he'
      refine ⟨q, hq, ?_⟩
      simp only [posIn, hp', Bool.and_eq_true, decide_eq_true_eq]
      omega
    next => cases hq'
  · rintro ⟨q, hq, hin⟩
    unfold posIn at hin
    split at hin
    next p' hp' =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
      refine ⟨q, hq, p + b - p', by omega, by omega, ?_⟩
      rw [hpc, label_eq hp hp', Int64.add_assoc, ← Int64.ofNat_add]
      congr 2
      omega
    next => cases hin

end Addr

end Spike.Lib.X64.PcRuns
