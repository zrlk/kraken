import Spike.Lib.LowerX64.FnCodeOf

/-!
# Every x86-64 code block's code facts from the placement check

`Spike/Lib/LowerX64/FnCodeOf.lean`: `FnCode` for each code block of an
`Accepted1` program passing `placeOKAt`; the axioms of the pieces.
-/

namespace Spike.Test.LowerX64FnCodeOf

open Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.fresh_env1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fresh_env1

/-- info: 'Spike.Lib.LowerX64.fnCode_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnCode_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.fnCode_ofPlaceOKX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnCode_ofPlaceOKX

/-- info: 'Spike.Lib.LowerX64.InWalkD.inWalkC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms InWalkD.inWalkC

/-- info: 'Spike.Lib.LowerX64.fnCode_ofPlaceOKR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnCode_ofPlaceOKR

end Spike.Test.LowerX64FnCodeOf
