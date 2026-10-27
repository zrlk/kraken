import Spike.Lib.LowerX64.ProgC

/-!
# Every x86-64 function with calls is one segment

`Spike/Lib/LowerX64/ProgC.lean`: the induction over the program's
declarations with the call brackets a premise, and `scc_rt_main`'s user
function at depth from its exits; the axioms of the pieces.
-/

namespace Spike.Test.LowerX64ProgC

open Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.fnSpecC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnSpecC_of

/-- info: 'Spike.Lib.LowerX64.fnSpecC_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnSpecC_all

/-- info: 'Spike.Lib.LowerX64.userCallWS_of_exitC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms userCallWS_of_exitC

/-- info: 'Spike.Lib.LowerX64.hps_of_spills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hps_of_spills

/-- info: 'Spike.Lib.LowerX64.fnSpecC_allI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.fnSpecC_allI

/-- info: 'Spike.Lib.LowerX64.FnCode.monoT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.FnCode.monoT

end Spike.Test.LowerX64ProgC
