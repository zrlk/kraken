import Spike.Lib.LowerA64.UserLag

/-!
# `scc_rt_main`'s user function at depth, held back at its ghost (AArch64)

`Spike/Lib/LowerA64/UserLag.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerA64UserLag

/-- info: 'Spike.Lib.A64ConsumerS.SFactsS.dt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64ConsumerS.SFactsS.dt_mono

/-- info: 'Spike.Lib.LowerA64.userCallWS_of_exitCL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.userCallWS_of_exitCL

end Spike.Test.LowerA64UserLag
