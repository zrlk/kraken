import Spike.Lib.LowerX64.Correct1

/-!
The axioms of the x86-64 compiler theorem for a main-only call-free
`Accepted1` program (`Spike/Lib/LowerX64/Correct1.lean`).
-/

namespace Spike.Lib.LowerX64.Test1

open Spike.Lib.LowerX64

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_closedAt1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_closedAt1

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_text_closedAt1

/--
info: 'Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt_of1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms x64_scc_correctE_text_closedAt_of1

end Spike.Lib.LowerX64.Test1
