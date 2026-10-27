import Spike.Lib.LowerX64.CallBlkW

/-!
# A call's blocks inside the body's fragment at depth (x86-64)

`Spike/Lib/LowerX64/CallBlkW.lean`: a covered `ret`-free block of the code,
a call's `callq`, and the callee's entry at its prologue head inside
`BodyWS0`, with the blocks' coverage; the axioms of the pieces.
-/

namespace Spike.Test.LowerX64CallBlkW

/-- info: 'Spike.Lib.LowerX64.okBlk_argLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.okBlk_argLoad

/-- info: 'Spike.Lib.LowerX64.noRet_argLoad' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.noRet_argLoad

/-- info: 'Spike.Lib.LowerX64.okBlk_xHead_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.okBlk_xHead_call

/-- info: 'Spike.Lib.LowerX64.blkW_bodySC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.blkW_bodySC

/-- info: 'Spike.Lib.LowerX64.blkW_callq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.blkW_callq

/-- info: 'Spike.Lib.LowerX64.nodeW_calleeEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.nodeW_calleeEntry

end Spike.Test.LowerX64CallBlkW
