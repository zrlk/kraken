import Spike.Lib.LowerX64.CtxC

/-!
# The contexts of an `Accepted1` program's functions (x86-64)

`Spike/Lib/LowerX64/CtxC.lean`: the regions' bases and a call keeping the
context, the frames placed at a call; the axioms of the pieces.
-/

namespace Spike.Test.LowerX64CtxC

/-- info: 'Spike.Lib.LowerX64.rbR_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.rbR_base

/-- info: 'Spike.Lib.LowerX64.calleeR_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.calleeR_base

/-- info: 'Spike.Lib.LowerX64.CtxB.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.CtxB.call

/-- info: 'Spike.Lib.LowerX64.lookupS_filter_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.lookupS_filter_ne

/-- info: 'Spike.Lib.LowerX64.lookupS_filter_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.lookupS_filter_eq

/-- info: 'Spike.Lib.LowerX64.FramesPlacedInI.cons1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.FramesPlacedInI.cons1

/-- info: 'Spike.Lib.LowerX64.framesPlaced_calleeF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.framesPlaced_calleeF

/-- info: 'Spike.Lib.LowerX64.envSmall_calleeF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.envSmall_calleeF

/-- info: 'Spike.Lib.LowerX64.CtxB.callF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.CtxB.callF

/-- info: 'Spike.Lib.LowerX64.rsOf_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.rsOf_param

/-- info: 'Spike.Lib.LowerX64.nj_callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.nj_callee

/-- info: 'Spike.Lib.LowerX64.CxOkC.hab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.CxOkC.hab

end Spike.Test.LowerX64CtxC
