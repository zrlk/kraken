import Spike.Lib.LowerA64.CtxC

/-!
# The contexts of an `Accepted1` program's functions (AArch64)

`Spike/Lib/LowerA64/CtxC.lean` and `Spike/Lib/A64FramesPlacedI.lean`: the axioms
of the pieces.
-/

namespace Spike.Test.LowerA64CtxC

/-- info: 'Spike.Lib.A64ConsumerS.FramesPlacedInI.nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.FramesPlacedInI.nil

/-- info: 'Spike.Lib.A64ConsumerS.FramesPlacedInI.toFramesPlaced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.FramesPlacedInI.toFramesPlaced

/-- info: 'Spike.Lib.A64ConsumerS.FramesPlacedInI.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.FramesPlacedInI.mono

/-- info: 'Spike.Lib.A64ConsumerS.FramesPlacedInI.of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.FramesPlacedInI.of_eq

/-- info: 'Spike.Lib.A64ConsumerS.FramesPlacedInI.of_cKept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.FramesPlacedInI.of_cKept

/-- info: 'Spike.Lib.A64ConsumerS.FramesPlacedInI.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.FramesPlacedInI.push

/-- info: 'Spike.Lib.A64ConsumerS.framesPlaced_callTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.framesPlaced_callTo

/-- info: 'Spike.Lib.A64ConsumerS.slotPlacedI_of_srep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.slotPlacedI_of_srep

/-- info: 'Spike.Lib.LowerA64.calleeR_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.calleeR_base

/-- info: 'Spike.Lib.LowerA64.CtxB.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.CtxB.call

/-- info: 'Spike.Lib.LowerA64.CalleeF.inF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.CalleeF.inF

/-- info: 'Spike.Lib.LowerA64.CalleeF.callerCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.CalleeF.callerCells

/-- info: 'Spike.Lib.LowerA64.lookupS_filter_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.lookupS_filter_ne

/-- info: 'Spike.Lib.LowerA64.lookupS_filter_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.lookupS_filter_eq

/-- info: 'Spike.Lib.LowerA64.FramesPlacedInI.cons1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.FramesPlacedInI.cons1

/-- info: 'Spike.Lib.LowerA64.frame_outA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.frame_outA

/-- info: 'Spike.Lib.LowerA64.framesPlaced_calleeF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.framesPlaced_calleeF

/-- info: 'Spike.Lib.LowerA64.envSmall_calleeF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.envSmall_calleeF

/-- info: 'Spike.Lib.LowerA64.CtxB.callF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.CtxB.callF

/-- info: 'Spike.Lib.LowerA64.rsOf_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.rsOf_param

/-- info: 'Spike.Lib.LowerA64.ArgV.envNum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.ArgV.envNum

/-- info: 'Spike.Lib.LowerA64.nj_callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.nj_callee

/-- info: 'Spike.Lib.LowerA64.CxOkC.hab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.CxOkC.hab

end Spike.Test.LowerA64CtxC
