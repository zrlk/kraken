import Spike.Lib.LowerA64.CallBlkW

/-!
# A call's blocks inside the body's fragment at depth (AArch64)

`Spike/Lib/LowerA64/CallBlkW.lean`: a covered `ret`-free block of the code,
a call's `bl`, and the callee's entry at its prologue head inside
`BodyWS0`, with the blocks' coverage; the axioms of the pieces.
-/

namespace Spike.Test.LowerA64CallBlkW

/-- info: 'Spike.Lib.LowerA64.okBlk_kind1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.okBlk_kind1

/-- info: 'Spike.Lib.LowerA64.okBlk_argLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.okBlk_argLoad

/-- info: 'Spike.Lib.LowerA64.okBlk_resStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.okBlk_resStore

/-- info: 'Spike.Lib.LowerA64.noRet_movzD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.noRet_movzD

/-- info: 'Spike.Lib.LowerA64.noRet_movkD' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.noRet_movkD

/-- info: 'Spike.Lib.LowerA64.noRetBlk_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.noRetBlk_cons

/-- info: 'Spike.Lib.LowerA64.noRet_movDs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.noRet_movDs

/-- info: 'Spike.Lib.LowerA64.noRet_argLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.noRet_argLoad

/-- info: 'Spike.Lib.LowerA64.noRet_resStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.noRet_resStore

/-- info: 'Spike.Lib.LowerA64.noRet_bl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.noRet_bl

/-- info: 'Spike.Lib.LowerA64.okBlk_chkHead_at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.okBlk_chkHead_at

/-- info: 'Spike.Lib.LowerA64.BlkW.bodyS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.BlkW.bodyS

/-- info: 'Spike.Lib.LowerA64.blkW_bodySC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.blkW_bodySC

/-- info: 'Spike.Lib.LowerA64.blkW_bl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.blkW_bl

/-- info: 'Spike.Lib.LowerA64.nodeW_calleeEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.nodeW_calleeEntry

/-- info: 'Spike.Lib.LowerA64.nodeW_calleeEntry_ofCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.nodeW_calleeEntry_ofCode

end Spike.Test.LowerA64CallBlkW
