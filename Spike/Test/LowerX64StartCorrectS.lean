import Spike.Lib.LowerX64.StartCorrectS

/-!
# The x86-64 consumer at any call depth from the user function's interface

`Spike/Lib/LowerX64/StartCorrectS.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerX64StartCorrectS

/-- info: 'Spike.Lib.LowerX64.ovfDt_noWrite1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.ovfDt_noWrite1

/-- info: 'Spike.Lib.LowerX64.hroomU_ofPlaceOK'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.hroomU_ofPlaceOK'

/-- info: 'Spike.Lib.LowerX64.x64_lower_correctES_of_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x64_lower_correctES_of_user

end Spike.Test.LowerX64StartCorrectS
