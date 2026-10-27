import Spike.Lib.LowerA64.CorrectC

/-!
# The compiler theorem for an `Accepted1` program at `CfgNeedOkA` (AArch64)

`Spike/Lib/LowerA64/CorrectC.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64CorrectC

/-- info: 'Spike.Lib.LowerA64.lowerAll?_ok_of_placeOKC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.lowerAll?_ok_of_placeOKC

/-- info: 'Spike.Lib.LowerA64.mainFunc_of_accepted1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainFunc_of_accepted1

/-- info: 'Spike.Lib.LowerA64.userMainSW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.userMainSW_of

/-- info: 'Spike.Lib.LowerA64.userMainSW_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.userMainSW_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.a64_lower_correctEC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.a64_lower_correctEC

/-- info: 'Spike.Lib.LowerA64.a64_scc_correctE_closedAtC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.a64_scc_correctE_closedAtC

/-- info: 'Spike.Lib.LowerA64.a64_scc_correctE_text_closedAtC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.a64_scc_correctE_text_closedAtC

end Spike.Test.LowerA64CorrectC
