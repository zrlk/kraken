import Spike.Lib.LowerA64.StartSegSG

/-!
# `_start`'s segment inside `SFactsS` (AArch64)

`Spike/Lib/LowerA64/StartSegSG.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64StartSegSG

/-- info: 'Spike.Lib.LowerA64.startW_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.startW_wmono

/-- info: 'Spike.Lib.LowerA64.sp0W_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.sp0W_wmono

/-- info: 'Spike.Lib.LowerA64.sp2W_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.sp2W_wmono

/-- info: 'Spike.Lib.LowerA64.proW_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.proW_wmono

/-- info: 'Spike.Lib.LowerA64.exitW_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.exitW_wmono

/-- info: 'Spike.Lib.LowerA64.mainUW_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainUW_wmono

/-- info: 'Spike.Lib.LowerA64.segWS_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.segWS_wmono

/-- info: 'Spike.Lib.LowerA64.a64_start_segWSG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.a64_start_segWSG

end Spike.Test.LowerA64StartSegSG
