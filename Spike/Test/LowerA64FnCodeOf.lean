import Spike.Lib.LowerA64.FnCodeOf

/-!
# The code of each function at its placement (AArch64)

`Spike/Lib/LowerA64/FnCodeOf.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64FnCodeOf

/-- info: 'Spike.Lib.LowerA64.fnCode_ofPlaceOKR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.fnCode_ofPlaceOKR

/-- info: 'Spike.Lib.LowerA64.fnCode_ofPlaceOKX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.fnCode_ofPlaceOKX

/-- info: 'Spike.Lib.LowerA64.fnCode_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.fnCode_ofPlaceOK

end Spike.Test.LowerA64FnCodeOf
