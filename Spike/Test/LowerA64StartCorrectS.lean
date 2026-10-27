import Spike.Lib.LowerA64.StartCorrectS

/-!
# The AArch64 consumer at any call depth from the user function's interface

`Spike/Lib/LowerA64/StartCorrectS.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64StartCorrectS

/-- info: 'Spike.Lib.LowerA64.ovfDt_noWrite1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.ovfDt_noWrite1

/-- info: 'Spike.Lib.LowerA64.hroomU_ofPlaceOK'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.hroomU_ofPlaceOK'

/-- info: 'Spike.Lib.LowerA64.tail_bare_of_accepted1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.tail_bare_of_accepted1

/-- info: 'Spike.Lib.LowerA64.a64_lower_correctES_of_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.a64_lower_correctES_of_user

end Spike.Test.LowerA64StartCorrectS
