import Spike.Lib.LowerX64.MainD

/-!
`main`'s user depth from the placement check on x86-64
(`Spike/Lib/LowerX64/MainD.lean`): the axioms of its theorems.
-/

namespace Spike.Test.LowerX64MainD

/--
info: 'Spike.Lib.LowerX64.frame16_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.frame16_of_placeOKAt

/--
info: 'Spike.Lib.LowerX64.mainD_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainD_of_placeOKAt

end Spike.Test.LowerX64MainD
