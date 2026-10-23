import Scc.Cert.Rt.CodeX64
import Spike.Lib.X64Print

/-!
# `scc_rt_print` in an emitted x64 program

The x64 twin of `Scc/Cert/Rt/A64Print.lean`.
`Spike.Lib.X64.Print.seg_print` proves `scc_rt_print` one segment from its
entry to its return or its abort, from hypotheses on the layout: each block
at its node's pc (`Code`) and the prologue's fall-through to `.entry`
(`hentry`). `printIn cells` checks them on the code cells: every block of
the function is the run of cells at its label and byte offset
(`blockAtB`), and `.entry` is 16 bytes behind `scc_rt_print`
(`labelGapB`). `seg_print_of` is `seg_print` in any valid layout of code
cells with `printIn cells = true`, decided once per program by
`decide +kernel`. The write system call stays a given node (`hsys`).
-/

namespace Scc.Cert.Rt.X64.Print

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Print

/-- `a + off` with the offset as `Int64.ofNat`, as the nodes write it. -/
theorem off_eq (a : Int64) (n : Nat) : a + Int64.ofNat n = a + OfNat.ofNat n := rfl

theorem off0 (a : Int64) : a + Int64.ofNat 0 = a := by
  rw [show Int64.ofNat 0 = 0 by decide, Int64.add_zero]

/-- **The code of `scc_rt_print` in `cells`**: its blocks at their labels
and offsets (the `write` system call 20 bytes after `.write` among them),
and the prologue's fall-through. -/
def printIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells "scc_rt_print" 0 x0 &&
  blockAtB cells ".Lscc_rt_print.entry" 0 x1 &&
  blockAtB cells ".Lscc_rt_print.loop" 0 x2 &&
  blockAtB cells ".Lscc_rt_print.loop" 20 x3 &&
  blockAtB cells ".Lscc_rt_print.write" 0 x4 &&
  blockAtB cells ".Lscc_rt_print.write" 20 [(.instr (.regular .W64 .W64 .syscall), 2)] &&
  blockAtB cells ".Lscc_rt_print.write" 22 x5 &&
  blockAtB cells ".Lscc_rt_print.write" 42 x6 &&
  blockAtB cells ".Lscc_rt_print.chk2" 0 x7 &&
  blockAtB cells ".Lscc_rt_print.chk2" 16 x8 &&
  blockAtB cells ".Lscc_rt_print.chk3" 0 x9 &&
  blockAtB cells ".Lscc_rt_print.chk3" 16 x10 &&
  blockAtB cells ".Lscc_rt_print.adv" 0 x11 &&
  blockAtB cells ".Lscc_rt_print.fail" 0 x12 &&
  blockAtB cells ".Lscc_rt_print.done" 0 x13 &&
  labelGapB cells "scc_rt_print" ".Lscc_rt_print.entry" 16

set_option linter.unusedSimpArgs false in
/-- **`scc_rt_print` is one segment** in any valid layout `exe` of code
cells `cells` with `printIn cells = true`, given its write system call. -/
theorem seg_print_of {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl} {rbp0 ra : BitVec 64}
    {cells : List (Directive × Nat)} [Kraken.Executable.ValidLayout exe] (hp : Lays exe cells)
    (hend : endPc = endOf exe cells) (hprog : printIn cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 rbp0 ra .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 rbp0 ra .n5))) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 rbp0 ra .e))
      (fun s c => ∃ x, At exe endPc R (DFrame R m0) (E (_root_.Executable.labels exe).label c0 rbp0 ra x) s c) := by
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, hgap⟩ := hprog
  refine seg_print hR hlo hhi ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [label_labelGapB hp hgap]; rfl) hsys
  · exact code_field hp hend h0 (off0 _)
  · exact code_field hp hend h1 (off0 _)
  · exact code_field hp hend h2 (off0 _)
  · exact code_field hp hend h3 rfl
  · exact code_field hp hend h4 (off0 _)
  · exact code_field hp hend h5 rfl
  · exact code_field hp hend h6 rfl
  · exact code_field hp hend h7 (off0 _)
  · exact code_field hp hend h8 rfl
  · exact code_field hp hend h9 (off0 _)
  · exact code_field hp hend h10 rfl
  · exact code_field hp hend h11 (off0 _)
  · exact code_field hp hend h12 (off0 _)
  · exact code_field hp hend h13 (off0 _)
  · exact code_field hp hend hs rfl

end Scc.Cert.Rt.X64.Print
