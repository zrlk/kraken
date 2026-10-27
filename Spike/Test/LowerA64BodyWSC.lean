import Spike.Lib.LowerA64.BodyWSC

/-!
# The construct blocks with calls inside the facts at depth (AArch64)

`Spike/Lib/LowerA64/BodyWSC.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64BodyWSC

/-- info: 'Spike.Lib.LowerA64.blockAt_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.blockAt_sub

/-- info: 'Spike.Lib.LowerA64.cd1_of_subCdC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.cd1_of_subCdC

/-- info: 'Spike.Lib.LowerA64.hWbS_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.hWbS_of

/-- info: 'Spike.Lib.LowerA64.hWsS_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.hWsS_of

end Spike.Test.LowerA64BodyWSC
