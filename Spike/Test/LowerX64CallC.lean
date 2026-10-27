import Spike.Lib.LowerX64.CallC

/-!
# A plain call (x86-64)

`Spike/Lib/LowerX64/CallC.lean`: a plain call's obligation `CallC` from its
code, its blocks inside the frame's fragment and the callee's segment
(`callC_of`), with its walk's pieces and the shared pieces of
`Spike/Lib/LowerX64/CallNodes.lean`; the axioms of the pieces.
-/

namespace Spike.Test.LowerX64CallC

/-- info: 'Spike.Lib.LowerX64.callC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.callC_of

/-- info: 'Spike.Lib.LowerX64.calleeP_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.calleeP_seg

/-- info: 'Spike.Lib.LowerX64.retP_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.retP_seg

/-- info: 'Spike.Lib.LowerX64.argP_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.argP_seg

/-- info: 'Spike.Lib.LowerX64.codeC_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.codeC_call

/-- info: 'Spike.Lib.LowerX64.callq_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.callq_seg

/-- info: 'Spike.Lib.LowerX64.CalleeF.framesKept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.CalleeF.framesKept

end Spike.Test.LowerX64CallC
