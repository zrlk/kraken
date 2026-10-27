import Spike.Lib.X64AllocPh
import Spike.Test.X64Hello1RtW

/-!
# `hello1.x`'s allocator passes `allocPhOk` (x86-64)

At `hello1.x`'s sites, phases and labels (`Inst.okPc`, `Inst.ph`, `labT`),
the hand proofs' `blkPh` decisions, `Spike/Test/X64Hello1AllocW.lean`.
-/

namespace Spike.Test.X64AllocPhHello1

open Spike.Lib.X64.Flow.Hello1.Inst (okPc ph labT)

/-- **`hello1.x`'s allocator passes the phase check.** -/
theorem hello1_allocPhOk : Spike.Lib.X64.AllocG.allocPhOk okPc ph labT = true := by
  rw [Spike.Test.X64Hello1RtW.labT_eq_labX]; decide +kernel

end Spike.Test.X64AllocPhHello1
