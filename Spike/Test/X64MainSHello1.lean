/-
**`Spike/Lib/Rt/X64MainS.lean` on `hello1.w`**: its cells pass `mainSIn`
at today's emitter's `scc_rt_main` for four setup words (`setupMC 4`), and
the marshalling block's closed form agrees with the hand block `mB1`.
-/
import Spike.Lib.Rt.X64MainS
import Spike.Lib.X64Hello1Main

namespace Spike.Test.X64MainSHello1

open Spike.Lib.X64 Spike.Lib.X64.Rt

/-- `hello1.w`'s cells pass `mainSIn` at four words. -/
theorem hello1_mainSIn : mainSIn SccCode.hello1Cells (setupMC 4) = true := by decide +kernel

/-- The parametric marshalling block at four words is the hand `.x2` block. -/
example : marshal 4 "wc_main" = Spike.Lib.X64.Flow.Hello1.mB1 := by decide

end Spike.Test.X64MainSHello1
