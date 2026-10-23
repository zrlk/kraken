/-
**`hab_of`'s premises at `ret0.w`'s `main`** (`Spike/Lib/LowerA64/AbortCall.lean`):
`main`'s `.abort_overflow` block is `Abort.Local.lb` in `ret0`'s program
(`hblk`), passes its phase check at the hand tables (`hphA`), and the
program has the abort code (`hprog`); the block has no `ret`. A pc table
excluding the block's call, or a phase table moving its call target, fails
the check; `lb` is not at another label. `rsOf_cell` at `main`'s context:
every register's cell is below the saved pair.
-/
import Spike.Lib.LowerA64.AbortCall
import Spike.Test.A64StubW
import Spike.Test.LowerA64Ret0Oracle

namespace Spike.Test.LowerA64AbortCall

open Spike.Lib.LowerA64
open Spike.Test.LowerInv (mainCtx)
open Spike.Lib.A64Consumer (blkPh noRetBlk)
open Spike.Lib.A64.Flow.Ret0.Inst (okPc ph)
open Spike.Lib.A64.StubW.Test (labR)
open SccCode (ret0Prog)

/-- **`hblk` at `ret0`**: `main`'s abort block is the checked `ovfBlk` (`= lb`). -/
theorem ret0_hblk : Scc.Cert.Rt.A64.blockAt ret0Prog (mainCtx.local "abort_overflow") 0
    ovfBlk = true := by
  rw [Spike.Test.LowerA64Ret0Oracle.mainCtx_abort]; decide +kernel

/-- **`hphA` at `ret0`**, on the hand tables. -/
theorem ret0_hphA : blkPh okPc ph (fun _ => false) labR (labR ".L18_wc_main.abort_overflow" + Int64.ofNat (4 * 0)) 0
    Spike.Lib.A64.Abort.Local.lb = true := by decide +kernel

/-- **`hprog` at `ret0`.** -/
theorem ret0_hprog : Scc.Cert.Rt.A64.Abort.abortIn ret0Prog = true := by decide +kernel

/-- The block has no `ret` (`lb_noRet`). -/
example : noRetBlk Spike.Lib.A64.Abort.Local.lb = true := lb_noRet

/-- No pc allowed: the check fails. -/
example : blkPh (fun _ => false) ph (fun _ => false) labR (labR ".L18_wc_main.abort_overflow" + Int64.ofNat (4 * 0)) 0
    Spike.Lib.A64.Abort.Local.lb = false := by decide +kernel

/-- A phase table putting `scc_rt_abort` in another phase than the block: the check fails. -/
example : blkPh okPc (fun pc => if pc = (labR "scc_rt_abort").toBitVec.toNat then ph pc + 1 else ph pc)
    (fun _ => false) labR (labR ".L18_wc_main.abort_overflow" + Int64.ofNat (4 * 0)) 0
    Spike.Lib.A64.Abort.Local.lb = false := by decide +kernel

/-- `lb` is not `main`'s check label's block. -/
example : Scc.Cert.Rt.A64.blockAt ret0Prog ".L18_wc_main.stack_check" 0 Spike.Lib.A64.Abort.Local.lb = false := by
  decide +kernel

/-- **`rsOf_cell` at `main`'s context** (frame 32): a cell is at most at `-24`. -/
example {r : Scc.IR.Reg} {k : Int} (h : rsOf mainCtx r = some k) : -32 ≤ k ∧ k ≤ -24 := by
  have hf : Scc.Lower.InvA64.FrameOk mainCtx := by unfold Scc.Lower.InvA64.FrameOk; decide +kernel
  have hfr : mainCtx.frame = 32 := by decide +kernel
  have := rsOf_cell hf h
  omega

end Spike.Test.LowerA64AbortCall
