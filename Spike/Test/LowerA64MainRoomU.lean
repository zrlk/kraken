import Spike.Lib.LowerA64.MainRoomU

/-!
# `main`'s frame within the limit's room (AArch64)

`Spike/Lib/LowerA64/MainRoomU.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64MainRoomU

/-- info: 'Spike.Lib.LowerA64.mainThread0_frameA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainThread0_frameA

/-- info: 'Spike.Lib.LowerA64.mainFrameU_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainFrameU_of_placeOKAt

end Spike.Test.LowerA64MainRoomU
