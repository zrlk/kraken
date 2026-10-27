import Spike.Lib.LowerA64.Correct1

/-!
The axioms of the AArch64 compiler theorem for a main-only call-free
`Accepted1` program (`Spike/Lib/LowerA64/Correct1.lean`).
-/

namespace Spike.Lib.LowerA64.Test1

open Spike.Lib.LowerA64

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_closedAt1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE_closedAt1

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE_text_closedAt1

/--
info: 'Spike.Lib.LowerA64.a64_scc_correctE_text_closedAt_of1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms a64_scc_correctE_text_closedAt_of1

end Spike.Lib.LowerA64.Test1
