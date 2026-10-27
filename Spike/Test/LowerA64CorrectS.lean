import Spike.Lib.LowerA64.CorrectS

/-!
# The AArch64 consumer at any call depth from `_start`'s segment

`Spike/Lib/LowerA64/CorrectS.lean` and `Spike/Lib/A64Accepted1SafeS.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64CorrectS

/-- info: 'Spike.Lib.A64ConsumerS.safeS_of_accepted1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.safeS_of_accepted1

/-- info: 'Spike.Lib.LowerA64.msOfS_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.msOfS_nil

/-- info: 'Spike.Lib.LowerA64.a64_lower_correctES' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.a64_lower_correctES

/-- info: 'Spike.Lib.LowerA64.a64_lower_correctES_rtF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.a64_lower_correctES_rtF

/-- info: 'Spike.Lib.LowerA64.a64_lower_correctES_wn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.a64_lower_correctES_wn

end Spike.Test.LowerA64CorrectS
