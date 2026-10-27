import Spike.Lib.LowerA64.MainC

/-!
# The aborts at their contexts held back never end (AArch64)

`Spike/Lib/LowerA64/MainC.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64MainC

/-- info: 'Spike.Lib.LowerA64.hasAddChk_func1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.hasAddChk_func1

/-- info: 'Spike.Lib.LowerA64.abC_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.abC_lag

/-- info: 'Spike.Lib.LowerA64.CodeFactsS.ovfFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.CodeFactsS.ovfFacts

/-- info: 'Spike.Lib.LowerA64.g16_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.g16_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.mainCtxB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainCtxB

/-- info: 'Spike.Lib.LowerA64.argTy_main' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.argTy_main

/-- info: 'Spike.Lib.LowerA64.spillsOk_of_paramSpill' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.spillsOk_of_paramSpill

/-- info: 'Spike.Lib.LowerA64.mainPre_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainPre_of

/-- info: 'Spike.Lib.LowerA64.uPostS_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.uPostS_ret

/--
info: 'Spike.Lib.LowerA64.lowerNoneS_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.lowerNoneS_ofPlaceOK

end Spike.Test.LowerA64MainC
