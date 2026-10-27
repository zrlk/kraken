import Spike.Lib.LowerX64.AbortCallS

/-!
# A function's overflow abort at depth, held back at depth 0 (x86-64)

`Spike/Lib/LowerX64/AbortCallS.lean` and the abort path's obligations moved
between worlds (`Spike/Lib/X64AbortWS.lean`): the axioms of the pieces.
-/

namespace Spike.Test.LowerX64AbortCallS

open Spike.Lib.LowerX64 Spike.Lib.X64.Abort.Local

/-- info: 'Spike.Lib.X64.Abort.Local.lb_take_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lb_take_slot

/-- info: 'Spike.Lib.X64.Abort.Local.StubW.mapF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StubW.mapF

/-- info: 'Spike.Lib.LowerX64.stub_sys_noK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stub_sys_noK

/-- info: 'Spike.Lib.LowerX64.hab_ofS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hab_ofS

end Spike.Test.LowerX64AbortCallS
