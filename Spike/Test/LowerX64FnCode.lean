import Spike.Lib.LowerX64.Checks
import Spike.Test.LowerInvX64
import Spike.Lib.X64Ret0Code
import Spike.Lib.X64Hello1Code

/-!
# `fnCodeOk` at `ret0.w` (x86-64)

The twin of `Spike/Test/LowerA64FnCodeCost.lean`: the placement check of
the lowered `Accepted0` functions (`Spike/Lib/LowerX64/Checks.lean`), their
frames recomputed from the lowered IR (`frOf`) and the prologue's cell
sizes read off the listing (`proInS`), decided by the kernel on
`ret0Cells` (its `main`), and rejected on a listing without that function
(`hello1Cells`: its `wc_main` is another body) or with its local overflow
block wrong or missing.
-/

namespace Spike.Test.LowerX64FnCode

open Spike.Lib.LowerX64 Spike.Test.LowerInvX64

-- The frame `fnCodeOk` recomputes for `main` is the emitter's (`mainFr`),
-- and the sizes it reads are the listing's.
#guard (frOf ret0IR mainF).slots == mainFr.slots && (frOf ret0IR mainF).size == mainFr.size &&
  (frOf ret0IR mainF).maps == mainFr.maps && (frOf ret0IR mainF).fn == "wc_main"
#guard sizesAt SccCode.ret0Cells ".Lwc_main.chk" 0 5 == [5, 9, 3, 2, 4]
#guard proInS SccCode.ret0Cells (frOf ret0IR mainF) "wc_main" ".Lwc_main.entry"

#guard fnCodeOk SccCode.ret0Cells ret0IR
#guard !fnCodeOk SccCode.hello1Cells ret0IR

theorem ret0_fnCodeOk : fnCodeOk SccCode.ret0Cells ret0IR = true := by decide +kernel

theorem ret0_fnCodeOk_hello1 : fnCodeOk SccCode.hello1Cells ret0IR = false := by decide +kernel

/-! The local overflow block (`ovfBlk` at `ovfL`) is checked: a listing
with a wrong abort code, a wrong callee or without the block's label fails. -/

/-- The index of `main`'s `.Lwc_main.ovf` label in `ret0Cells`. -/
def ovfIdx : Nat := 1199

#guard SccCode.ret0Cells[ovfIdx]? == some (.label ".Lwc_main.ovf", 0)
#guard (SccCode.ret0Cells.drop (ovfIdx + 1)).take 2 == ovfBlk

/-- `movl $2, %edi` for the abort's code (the same size). -/
def badImm : List (_root_.Directive × Nat) := SccCode.ret0Cells.set (ovfIdx + 1)
  (Scc.Emit.X64.i32 (.mov (Scc.Emit.X64.xr .rdi) (Scc.Emit.X64.oi 2)), 5)

/-- `call scc_rt_abort_heap` for the call (the same size). -/
def badCallee : List (_root_.Directive × Nat) := SccCode.ret0Cells.set (ovfIdx + 2)
  (Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel "scc_rt_abort_heap")), 5)

/-- The block's label gone. -/
def noBlock : List (_root_.Directive × Nat) := SccCode.ret0Cells.eraseIdx ovfIdx

#guard !fnCodeOk badImm ret0IR
#guard !fnCodeOk badCallee ret0IR
#guard !fnCodeOk noBlock ret0IR

end Spike.Test.LowerX64FnCode
