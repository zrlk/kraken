/-
**The ISA-free restatements in `Spike.Lib.X64WakeSrcDefs` are the neutral
originals** (`WakePreA.spawnTerm`, `WakeT1.mainTidLbl`), by `rfl`. Imports
the A64 side only (as `WakeSrcPoEq`).
-/
import Spike.Lib.X64WakeSrcDefs
import Spike.Lib.WakePreA

namespace Spike.Test.WakeSrcDefsEq

theorem spawnTerm_eq : Spike.Lib.X64WakeSrcDefs.spawnTerm = Spike.Lib.WakePreA.spawnTerm := rfl

theorem mainTidLbl_eq : Spike.Lib.X64WakeSrcDefs.mainTidLbl = Spike.Lib.WakeT1.mainTidLbl := rfl

/-- info: 'Spike.Test.WakeSrcDefsEq.spawnTerm_eq' does not depend on any axioms -/
#guard_msgs in #print axioms spawnTerm_eq

/-- info: 'Spike.Test.WakeSrcDefsEq.mainTidLbl_eq' does not depend on any axioms -/
#guard_msgs in #print axioms mainTidLbl_eq

end Spike.Test.WakeSrcDefsEq
