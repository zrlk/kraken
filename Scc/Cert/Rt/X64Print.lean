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

The theorems stated over the segment predicate (`Spike.Lib.Seg`, `MemSide`)
are in `Spike/Lib/Rt/Seg/X64Print.lean` (same namespace and names).
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

end Scc.Cert.Rt.X64.Print
