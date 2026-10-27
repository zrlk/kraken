import Spike.Lib.LowerX64.UserLag

/-!
# `scc_rt_main`'s user function at depth, held back at its ghost (x86-64)

`Spike/Lib/LowerX64/UserLag.lean`: the axioms of the pieces.
-/

namespace Spike.Test.LowerX64UserLag

/-- info: 'Spike.Lib.X64ConsumerS.SFactsS.dt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.SFactsS.dt_mono

/-- info: 'Spike.Lib.SegWS.mono_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.SegWS.mono_W

/-- info: 'Spike.Lib.LowerX64.userCallWS_of_exitCL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.userCallWS_of_exitCL

end Spike.Test.LowerX64UserLag
