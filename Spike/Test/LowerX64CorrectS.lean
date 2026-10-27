import Spike.Lib.LowerX64.CorrectS

/-!
# The x86-64 consumer at any call depth from `_start`'s segment

`Spike/Lib/LowerX64/CorrectS.lean` and `Spike/Lib/X64Accepted1SafeS.lean`: the
axioms of the pieces.
-/

namespace Spike.Test.LowerX64CorrectS

/-- info: 'Spike.Lib.X64ConsumerS.safeS_of_accepted1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.safeS_of_accepted1

/-- info: 'Spike.Lib.LowerX64.msOfS_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.msOfS_nil

/-- info: 'Spike.Lib.LowerX64.x64_lower_correctES' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x64_lower_correctES

/-- info: 'Spike.Lib.LowerX64.x64_lower_correctES_rtF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x64_lower_correctES_rtF

/-- info: 'Spike.Lib.LowerX64.x64_lower_correctES_wn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x64_lower_correctES_wn

end Spike.Test.LowerX64CorrectS
