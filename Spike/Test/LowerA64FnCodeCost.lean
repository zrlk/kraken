import Spike.Lib.LowerA64.Checks
import Spike.Test.LowerInv
import Spike.Lib.A64Ret0Code
import Spike.Lib.A64Hello1Code

/-!
# `fnCodeOk` at `ret0.w`

The placement check of the lowered `Accepted0` functions
(`Spike/Lib/LowerA64/Checks.lean`), its contexts recomputed from the lowered
IR, decided by the kernel on `ret0Prog` (its `main`), and rejected on a
listing without that function (`hello1Prog`: its `.L18_wc_main` labels are
not there) or with its local overflow block wrong or missing.

Cost (AArch64, this file): peak RssAnon about 2.1 GB, most of it the
kernel's run of the lowering itself (`ret0IR` is `lowerAll` of the source);
from a written-out IR literal the decision alone peaks at about 0.4 GB.
-/

namespace Spike.Test.LowerA64FnCodeCost

open Spike.Lib.LowerA64 Spike.Test.LowerInv

#guard fnCodeOk SccCode.ret0Prog ret0IR
#guard !fnCodeOk SccCode.hello1Prog ret0IR

/-- A spawned thread body returning `Unit` (`threadcap`'s `wc_worker`):
`func0`-shaped but no single result, so not checked. -/
def unitWorker : Scc.IR.Func :=
  { name := "wc_worker", params := [], checkStack := true, blocks := [{ label := "entry", insts := [], term := .ret [] }] }

#guard fnCodeOk SccCode.ret0Prog { ret0IR with funcs := ret0IR.funcs ++ [unitWorker] }

theorem ret0_fnCodeOk : fnCodeOk SccCode.ret0Prog ret0IR = true := by decide +kernel

/-! The local overflow block (`ovfBlk` at `abort_overflow`) is checked: a
listing with a wrong abort code, a wrong callee or without the block's
label fails. -/

/-- The index of `main`'s `.L18_wc_main.abort_overflow` label in `ret0Prog`. -/
def ovfIdx : Nat := 1319

#guard SccCode.ret0Prog[ovfIdx]? == some (.label ".L18_wc_main.abort_overflow")
#guard (SccCode.ret0Prog.drop (ovfIdx + 1)).take 2 == ovfBlk

/-- `movz x0, #2` for the abort's code. -/
def badImm : List _root_.Directive := SccCode.ret0Prog.set (ovfIdx + 1)
  (.instr { operation_size := .W64, operation := .MOVZ (Scc.Emit.A64.xz .X0) (Scc.Emit.A64.i64 2) .LSL0 })

/-- `bl scc_rt_abort_heap` for the call. -/
def badCallee : List _root_.Directive := SccCode.ret0Prog.set (ovfIdx + 2)
  (.instr { operation_size := .W64, operation := .BL (.label "scc_rt_abort_heap") })

/-- The block's label gone. -/
def noBlock : List _root_.Directive := SccCode.ret0Prog.eraseIdx ovfIdx

#guard !fnCodeOk badImm ret0IR
#guard !fnCodeOk badCallee ret0IR
#guard !fnCodeOk noBlock ret0IR

end Spike.Test.LowerA64FnCodeCost
