/-
**wake.w on AArch64: the layout facts of `wc_waitLoop`**,
decided on the program the canonical loader reads from the certificate's
listing (`wakeProg`: `scc_arm_text%` of `SccCertificate.asm`,
`Spike/Test/Cert/A64WakeCert.lean`; the parse is the
trust boundary, checked by `#guard`, as in the generated `*Code.lean`
files). There the function's label prefix is `.L20_wc_waitLoop`.

A label of the program text is at the text's base plus the sizes of the
cells before its first occurrence, in any executable whose cells start
with the program's (`lab_of_idx`): the canonical loader's thread is one
when no data symbol is below the code
(`Scc.Cert.Rt.A64.threadAt_exe_of_above`). So the differences between the
labels `Spike.Lib.A64.WaitLoop.seg_waitLoopP` takes as hypotheses
(`hentry`, `hcheck`, `hsp3`, `hpentry`) are decided on the program alone
(`labOff`, by `decide +kernel`), whatever the base and the cells after the
text.
-/
import Spike.Lib.A64Ret0Mem
import Spike.Test.Cert.A64WakeCert

namespace Spike.Lib.A64.WakeLabels

open Kraken Kraken.Promising.AArch64
open Spike.Lib.A64.Flow.Ret0.Mem (labelIdx labelIdx_spec)

/-- The program's cells (`Directive.fakeSize`: instructions 4 bytes, labels 0). -/
def cellsOf (prog : Program) : List (Directive × Nat) := prog.map fun d => (d, d.fakeSize)

/-- **The byte offset of label `l`** in the program text: the sizes of the
cells before its first occurrence. -/
def labOff (prog : Program) (l : Label) : Option Nat :=
  (labelIdx (cellsOf prog) l).map fun n => (((cellsOf prog).take n).map (·.2)).sum

theorem labelIdx_append : ∀ {xs ys : List (Directive × Nat)} {l : Label} {n : Nat},
    labelIdx xs l = some n → labelIdx (xs ++ ys) l = some n
  | [], _, _, _, h => by simp [labelIdx] at h
  | c :: cs, ys, l, n, h => by
    unfold labelIdx at h ⊢
    simp only [List.cons_append]
    split
    · split at h
      · exact h
      · contradiction
    · split at h
      · contradiction
      · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [labelIdx_append hm]; rfl

/-- **A label of the program text** in an executable whose cells start with
the program's. -/
theorem lab_of_off {prog : Program} {base : Int64} {rest : List (Directive × Nat)} {l : Label} {k : Nat}
    (h : labOff prog l = some k) :
    (_root_.Executable.labels (base, cellsOf prog ++ rest)).label l = base + Int64.ofNat k := by
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
  have hn' := labelIdx_append (ys := rest) hn
  obtain ⟨⟨z, hz⟩, hfirst⟩ := labelIdx_spec hn'
  have hlt : n < (cellsOf prog).length := by
    obtain ⟨⟨z', hz'⟩, -⟩ := labelIdx_spec hn
    exact (List.getElem?_eq_some_iff.mp hz').1
  have hz0 : z = 0 := by
    obtain ⟨⟨z', hz'⟩, -⟩ := labelIdx_spec hn
    rw [List.getElem?_append_left hlt, hz'] at hz
    cases hz
    simp only [cellsOf, List.getElem?_map, Option.map_eq_some_iff] at hz'
    obtain ⟨d, -, hd⟩ := hz'
    cases hd; rfl
  subst hz0
  rw [Kraken.Executable.label_addrOf _ l n hz hfirst]
  simp only [Kraken.Executable.addrOf, Kraken.Executable.sizeBefore]
  rw [List.take_append_of_le_length (by simpa using Nat.le_of_lt hlt)]

theorem lab_of_off_add {prog : Program} {base : Int64} {rest : List (Directive × Nat)} {l l' : Label} {k d : Nat}
    (h : labOff prog l = some k) (h' : labOff prog l' = some (k + d)) :
    (_root_.Executable.labels (base, cellsOf prog ++ rest)).label l' =
      (_root_.Executable.labels (base, cellsOf prog ++ rest)).label l + Int64.ofNat d := by
  rw [lab_of_off h, lab_of_off h', Int64.ofNat_add, Int64.add_assoc]

/-! ## wake.w's certificate -/

/-- The program the canonical loader reads from wake.w's listing. -/
def wakeProg : Program := scc_arm_text% SccCertificate.asm

/-- The data sections the canonical loader reads from it. -/
def wakeSecs : Scc.Sem.DataSecs := scc_data_secs% SccCertificate.asm

#guard Scc.Cert.Link.A64.parsesTo SccCertificate.asm wakeProg wakeSecs

/-- `wc_waitLoop`'s label prefix in wake.w's certificate. -/
abbrev pfx : String := ".L20_wc_waitLoop"

theorem off_entry : labOff wakeProg (pfx ++ ".0_entry") =
    (labOff wakeProg "wc_waitLoop").map (· + 40) := by decide +kernel
theorem off_check : labOff wakeProg (pfx ++ ".stack_check") =
    (labOff wakeProg "wc_waitLoop").map (· + 0) := by decide +kernel
theorem off_sp3 : labOff wakeProg (pfx ++ ".sp3") =
    (labOff wakeProg (pfx ++ ".2_else2")).map (· + 4) := by decide +kernel
theorem off_pentry : labOff wakeProg ".L10_scc_rt_park.0_entry" =
    (labOff wakeProg "scc_rt_park").map (· + 16) := by decide +kernel
theorem off_some : (labOff wakeProg "wc_waitLoop").isSome ∧
    (labOff wakeProg (pfx ++ ".2_else2")).isSome ∧
    (labOff wakeProg "scc_rt_park").isSome := by decide +kernel

theorem rel_of {l l' : Label} {d : Nat} (h : labOff wakeProg l' = (labOff wakeProg l).map (· + d))
    (hs : (labOff wakeProg l).isSome) {base : Int64} {rest : List (Directive × Nat)} :
    (_root_.Executable.labels (base, cellsOf wakeProg ++ rest)).label l' =
      (_root_.Executable.labels (base, cellsOf wakeProg ++ rest)).label l + Int64.ofNat d := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
  rw [hk] at h
  exact lab_of_off_add hk h

/-- **The canonical loader's thread** has the program's cells first when no
data symbol is below the code. -/
theorem threadAt_cells {E : Scc.Sem.Entry} {base : Nat} {syms : List (String × Nat)} (h : ∀ p ∈ syms, base ≤ p.2) :
    (Scc.Sem.A64.threadAt E base wakeProg syms).exe.2 =
      cellsOf wakeProg ++ (Scc.Sem.A64.threadAt E base wakeProg syms).exe.2.drop wakeProg.length := by
  rw [Scc.Cert.Rt.A64.threadAt_exe_of_above h]
  simp only [cellsOf, List.drop_left' (List.length_map _)]

variable {exe : _root_.Executable} (hexe : exe.2 = cellsOf wakeProg ++ exe.2.drop wakeProg.length)
include hexe

private theorem exe_eq : exe = (exe.1, cellsOf wakeProg ++ exe.2.drop wakeProg.length) :=
  Prod.ext rfl hexe

/-- `hentry` of `seg_waitLoopP` at wake's prefix. -/
theorem hentry : (_root_.Executable.labels exe).label (pfx ++ ".0_entry") =
    (_root_.Executable.labels exe).label "wc_waitLoop" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 := by
  rw [exe_eq hexe, rel_of off_entry off_some.1]
  simp only [Int64.add_assoc]; rfl

/-- `hcheck` of `seg_waitLoopP` at wake's prefix. -/
theorem hcheck : (_root_.Executable.labels exe).label (pfx ++ ".stack_check") =
    (_root_.Executable.labels exe).label "wc_waitLoop" := by
  rw [exe_eq hexe, rel_of off_check off_some.1]
  simp

/-- `hsp3` of `seg_waitLoopP` at wake's prefix. -/
theorem hsp3 : (_root_.Executable.labels exe).label (pfx ++ ".sp3") =
    (_root_.Executable.labels exe).label (pfx ++ ".2_else2") + 4 := by
  rw [exe_eq hexe, rel_of off_sp3 off_some.2.1]
  rfl

/-- `hpentry` of `seg_waitLoopP` (`scc_rt_park`'s prologue falls through). -/
theorem hpentry : (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
    (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4 := by
  rw [exe_eq hexe, rel_of off_pentry off_some.2.2]
  simp only [Int64.add_assoc]; rfl

end Spike.Lib.A64.WakeLabels
