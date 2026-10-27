import Spike.Lib.LowerX64.CorrectC

/-!
# The compiler theorem for an `Accepted1` program at `CfgNeedOk` (x86-64)

`Spike/Lib/LowerX64/CorrectC.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerX64CorrectC

/-- info: 'Spike.Lib.LowerX64.lowerAll?_ok_of_placeOKC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.lowerAll?_ok_of_placeOKC

/-- info: 'Spike.Lib.LowerX64.mainFunc_of_accepted1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainFunc_of_accepted1

/-- info: 'Spike.Lib.LowerX64.x64_lower_correctEC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x64_lower_correctEC

/-- info: 'Spike.Lib.LowerX64.x64_scc_correctE_closedAtC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x64_scc_correctE_closedAtC

/-- info: 'Spike.Lib.LowerX64.x64_scc_correctE_text_closedAtC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x64_scc_correctE_text_closedAtC

end Spike.Test.LowerX64CorrectC
