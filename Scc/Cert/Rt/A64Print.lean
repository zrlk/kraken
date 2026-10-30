import Scc.Cert.Rt.LayoutA64
import Spike.Lib.A64Print

/-!
# `scc_rt_print` in an emitted AArch64 program

`printIn prog` checks `scc_rt_print`'s code on a directive list: every
block of the function is the run of instructions at its label and offset
(`blockAt`), and `.0_entry` is six instructions behind `scc_rt_print`
(`labelGap`), decided once per program by `decide +kernel`. On AArch64
every program's write block `.2_write` is led by the barrier `dmb ish`
(`Print.bF`, `Runtime.printF`), the rest of the block one instruction on.
`code_field` gives a block's code from `blockAt` in every state of a valid
layout, for the segment proofs.

The labels are scc's (`.L9_scc_rt_print.*`: the runtime's functions come
first in every program, in a fixed order).
-/

namespace Scc.Cert.Rt.A64.Print

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow
  Spike.Lib.A64.Print

/-- **The code of `scc_rt_print` in `prog`**: its blocks at their labels
and offsets (`.2_write` led by the barrier `bF`, `dmb ish`, the `write`
system call 5 instructions after `.2_write` among them), and the prologue's
fall-through. -/
def printIn (prog : List Directive) : Bool :=
  blockAt prog "scc_rt_print" 0 b0 &&
  blockAt prog ".L9_scc_rt_print.0_entry" 0 b1 &&
  blockAt prog ".L9_scc_rt_print.1_loop" 0 b2 &&
  blockAt prog ".L9_scc_rt_print.1_loop" 4 b3 &&
  blockAt prog ".L9_scc_rt_print.2_write" 0 bF &&
  blockAt prog ".L9_scc_rt_print.2_write" 1 b4 &&
  blockAt prog ".L9_scc_rt_print.2_write" 5 [svcDir] &&
  blockAt prog ".L9_scc_rt_print.2_write" 6 b5 &&
  blockAt prog ".L9_scc_rt_print.2_write" 13 b6 &&
  blockAt prog ".L9_scc_rt_print.2_write" 14 b7 &&
  blockAt prog ".L9_scc_rt_print.3_chk2" 0 b8 &&
  blockAt prog ".L9_scc_rt_print.3_chk2" 6 b9 &&
  blockAt prog ".L9_scc_rt_print.3_chk2" 7 b10 &&
  blockAt prog ".L9_scc_rt_print.4_chk3" 0 b11 &&
  blockAt prog ".L9_scc_rt_print.4_chk3" 4 b12 &&
  blockAt prog ".L9_scc_rt_print.5_adv" 0 b13 &&
  blockAt prog ".L9_scc_rt_print.6_fail" 0 b14 &&
  blockAt prog ".L9_scc_rt_print.7_done" 0 b16 &&
  labelGap prog "scc_rt_print" ".L9_scc_rt_print.0_entry" 6

/-- A code segment at an equal pc. -/
theorem CodeAt.pc_eq {st : State} {p q : Int64} {b : List Directive} (h : CodeAt st p b) (e : p = q) :
    CodeAt st q b := e ▸ h

/-- `a + 4 + … + 4` (`k` times) is `a + 4k`. -/
theorem add4 (a : Int64) (k : Nat) : a + Int64.ofNat (4 * (k + 1)) = a + Int64.ofNat (4 * k) + 4 := by
  rw [Int64.add_assoc, show 4 * (k + 1) = 4 * k + 4 by omega, Int64.ofNat_add]; rfl

theorem add0 (a : Int64) : a + Int64.ofNat (4 * 0) = a := by
  rw [show Int64.ofNat (4 * 0) = 0 by decide, Int64.add_zero]

/-- A field of `Code` from `blockAt`: the block's code at `label + 4k`, in
every state of the executable. -/
theorem code_field {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) {endPc : Int64} (hend : endPc = endOf exe prog kp)
    {l : Label} {k : Nat} {b : List Directive} (h : blockAt prog l k b = true) {q : Int64}
    (e : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = q) :
    ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s q b :=
  fun _ hs hn => CodeAt.pc_eq (codeAt_blockAt hp hs (hn.trans hend) h) e

end Scc.Cert.Rt.A64.Print
