import Spike.Lib.Rt.X64CtrZOfEmitted

/-!
# The counter's zeroed item of scc's output (x86-64)

`ctrZ_ofEmitted` and `ctrZ_ofPlaceOK` use no axiom beyond Lean's.
-/

namespace Spike.Test.X64CtrZOfEmitted

/-- info: 'Spike.Lib.X64.Rt.ctrZ_ofEmitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Rt.ctrZ_ofEmitted

/-- info: 'Spike.Lib.X64.Rt.ctrZ_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.X64.Rt.ctrZ_ofPlaceOK

end Spike.Test.X64CtrZOfEmitted
