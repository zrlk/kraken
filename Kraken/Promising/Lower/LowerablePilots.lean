/-
**Every AArch64 pilot program is
WeakCore-lowerable.**

`Program.WCLowerable` (`Lower/Lowerable.lean`), proved by `decide` of `pilot`
(the first lowering pilot), `pilot2` (the stack-frame pilot), `progE`/`progD` (the MS queue pilot), `allocP` (the allocation pilot),
and the fragment demos `callsDemo` (Calls) and `loopDemo` (LoopCalls). With
`Program.WCLowerable.lse2Free` each gives the LSE2 route's `hfree`.
-/
import Kraken.Promising.Lower.Lowerable
import Kraken.Promising.Lower.PilotProg
import Kraken.Promising.Lower.Pilot2Prog
import Kraken.Promising.Lower.MsqPilotProg
import Kraken.Promising.Lower.AllocProg
import Kraken.Promising.Lower.FragSpecLoopCallsDemo

/-! ## Every AArch64 pilot program is lowerable -/

/-- The first lowering pilot. -/
theorem Kraken.Promising.Lower.Pilot.pilot_wcLowerable : Program.WCLowerable Kraken.Promising.Lower.Pilot.pilot := by
  decide

/-- The stack-frame pilot. -/
theorem Kraken.Promising.Lower.Pilot2.pilot2_wcLowerable :
    Program.WCLowerable Kraken.Promising.Lower.Pilot2.pilot2 := by
  decide

/-- The MS queue pilot, the enqueuer. -/
theorem Kraken.Promising.Lower.MsqPilot.progE_wcLowerable :
    Program.WCLowerable Kraken.Promising.Lower.MsqPilot.progE := by
  decide

/-- The MS queue pilot, the dequeuer. -/
theorem Kraken.Promising.Lower.MsqPilot.progD_wcLowerable :
    Program.WCLowerable Kraken.Promising.Lower.MsqPilot.progD := by
  decide

/-- The allocation pilot. -/
theorem Kraken.Promising.Lower.Alloc.allocP_wcLowerable :
    Program.WCLowerable Kraken.Promising.Lower.Alloc.allocP := by
  decide

/-- The Calls fragment demo (direct, tail, indirect and nested calls of `push`). -/
theorem Kraken.Promising.Lower.Calls.callsDemo_wcLowerable :
    Program.WCLowerable Kraken.Promising.Lower.Calls.callsDemo := by
  decide

/-- The LoopCalls fragment demo (`pop` called in a loop). -/
theorem Kraken.Promising.Lower.LoopCalls.loopDemo_wcLowerable :
    Program.WCLowerable Kraken.Promising.Lower.LoopCalls.loopDemo := by
  decide
