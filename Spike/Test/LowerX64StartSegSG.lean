import Spike.Lib.LowerX64.StartSegSG

/-!
# `_start`'s segment inside `SFactsS` (x86-64)

`Spike/Lib/LowerX64/StartSegSG.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerX64StartSegSG

/-- info: 'Spike.Lib.LowerX64.st0W_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.st0W_wmono

/-- info: 'Spike.Lib.LowerX64.x0W_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x0W_wmono

/-- info: 'Spike.Lib.LowerX64.mainUW_wmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainUW_wmono

/-- info: 'Spike.Lib.LowerX64.x64_start_segWSG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x64_start_segWSG
end Spike.Test.LowerX64StartSegSG
