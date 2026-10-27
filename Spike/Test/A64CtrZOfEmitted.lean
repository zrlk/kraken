import Spike.Lib.Rt.A64CtrZOfEmitted

/-!
# The counter's zeroed item of scc's output (AArch64)

`ctrZ_ofEmitted` and `ctrZ_ofPlaceOK` use no axiom beyond Lean's.
-/

namespace Spike.Test.A64CtrZOfEmitted

/-- info: 'Spike.Lib.A64.Rt.ctrZ_ofEmitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Rt.ctrZ_ofEmitted

/-- info: 'Spike.Lib.A64.Rt.ctrZ_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Rt.ctrZ_ofPlaceOK

end Spike.Test.A64CtrZOfEmitted
