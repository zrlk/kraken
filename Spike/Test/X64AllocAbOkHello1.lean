/-
**Oracle: `hello1.x`'s allocator passes the target check** (x86-64):
`Spike/Lib/X64AllocAbOk.lean`'s `allocAbOk` at `labT` (the hand proofs'
`blkAb` and `abPcs` decisions, `Spike/Test/X64Hello1AllocAb.lean`).
-/
import Spike.Lib.X64AllocAbOk
import Spike.Test.X64Hello1AllocAb

namespace Spike.Test.X64AllocAbOkHello1

open Spike.Lib.X64.Flow.Hello1.Inst

/-- **`hello1.x`'s allocator's targets are off the write abort's pcs.** -/
theorem hello1_allocAbOk : Spike.Lib.X64.AllocG.allocAbOk labT = true := by
  rw [Spike.Test.X64Hello1W0.labT_eq_labY]; decide +kernel

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.X64AllocAbOkHello1.hello1_allocAbOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms hello1_allocAbOk

end Spike.Test.X64AllocAbOkHello1
