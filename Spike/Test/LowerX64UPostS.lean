import Spike.Lib.LowerX64.UPostS

/-!
The user function's post at depth on x86-64 (`Spike/Lib/LowerX64/UPostS.lean`):
the axioms of its theorems.
-/

namespace Spike.Test.LowerX64UPostS

/--
info: 'Spike.Lib.LowerX64.UPost.toS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.UPost.toS

/--
info: 'Spike.Lib.LowerX64.uPostS_exit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.uPostS_exit

end Spike.Test.LowerX64UPostS
