import Spike.Lib.A64AbortWS

/-!
# The AArch64 overflow abort at depth, held back at depth 0

`Spike/Lib/A64AbortWS.lean`: a function's `.abort_overflow` block at
frames, the source held back at depth 0 after `SegWS.lag`; the axioms of the
pieces.
-/

namespace Spike.Test.A64AbortWS

open Spike.Lib.A64.Abort.Local

/-- info: 'Spike.Lib.A64.Abort.Local.seg_localWS_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seg_localWS_lag

/-- info: 'Spike.Lib.A64.Abort.Local.lb_take_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lb_take_slot

/-- info: 'Spike.Lib.A64.Abort.Local.StubW.mapF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StubW.mapF

end Spike.Test.A64AbortWS
