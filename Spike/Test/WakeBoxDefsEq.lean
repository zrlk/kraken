/-
**The ISA-free restatements in `Spike.Lib.X64WakeBoxDefs` are the A64
originals** (`A64.Flow.WakeWc.boxTerm`, `A64.Flow.WakeWc.boxPubCtl`), by
`rfl`. Imports the A64 side only (as `WakeSrcDefsEq`).
-/
import Spike.Lib.X64WakeBoxDefs
import Spike.Lib.WakePubFence

namespace Spike.Test.WakeBoxDefsEq

theorem boxTerm_eq : Spike.Lib.X64WakeBoxDefs.boxTerm = Spike.Lib.A64.Flow.WakeWc.boxTerm := rfl

theorem boxPubCtl_eq : Spike.Lib.X64WakeBoxDefs.boxPubCtl = Spike.Lib.A64.Flow.WakeWc.boxPubCtl := rfl

/-- info: 'Spike.Test.WakeBoxDefsEq.boxTerm_eq' does not depend on any axioms -/
#guard_msgs in #print axioms boxTerm_eq

/-- info: 'Spike.Test.WakeBoxDefsEq.boxPubCtl_eq' does not depend on any axioms -/
#guard_msgs in #print axioms boxPubCtl_eq

end Spike.Test.WakeBoxDefsEq
