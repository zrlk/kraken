import Spike.Lib.LowerX64.MainRoomU

/-!
# `main`'s frame within the limit's room from the placement check (x86-64)

`Spike/Lib/LowerX64/MainRoomU.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerX64MainRoomU

/-- info: 'Spike.Lib.LowerX64.mainThread0_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainThread0_frame

/-- info: 'Spike.Lib.LowerX64.mainFrameU_of_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainFrameU_of_rows

/-- info: 'Spike.Lib.LowerX64.mainFrameU_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainFrameU_of_placeOKAt

end Spike.Test.LowerX64MainRoomU
