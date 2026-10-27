import Spike.Lib.X64PrintPh
import Spike.Test.X64Hello1RtW

/-!
# `hello1.x`'s output routine passes `printPhOk` (x86-64)

At `hello1.x`'s sites, phases and labels (`Inst.okPc`, `Inst.ph`, `labT`),
as `Spike/Test/X64AllocPhHello1.lean` for the allocator.
-/

namespace Spike.Test.X64PrintPhHello1

open Spike.Lib.X64.Flow.Hello1.Inst (okPc ph labT)

/-- **`hello1.x`'s output routine passes the phase check.** -/
theorem hello1_printPhOk : Spike.Lib.X64.PrintG.printPhOk okPc ph labT = true := by
  rw [Spike.Test.X64Hello1RtW.labT_eq_labX]; decide +kernel

end Spike.Test.X64PrintPhHello1
