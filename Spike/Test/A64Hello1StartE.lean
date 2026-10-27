/-
**`hello1.w`'s start up to `scc_rt_main`'s entry** (AArch64): the runtime's
code but `scc_rt_main`'s (`RtCodeIn0`) from its setup pass at four words
(`setupMC 4`), so that `startE_segW` (`Spike/Lib/Rt/A64StartE.lean`)
applies to `hello1Prog`.
-/
import Spike.Lib.Rt.A64StartE
import Spike.Lib.Rt.A64CodeInSetup
import Spike.Lib.A64Hello1Code

namespace Spike.Lib.A64.Rt.Test

open Spike.Lib.A64.Rt

/-- `hello1.w`'s setup pass at four words passes. -/
theorem hello1_rtCodeOkS : rtCodeOkS SccCode.hello1Prog (setupMC 4) = true := by decide +kernel

/-- **`hello1.w`'s runtime code but `scc_rt_main`'s**. -/
theorem hello1_rtCodeIn0 : RtCodeIn0 SccCode.hello1Prog := rtCodeIn0_of_okS hello1_rtCodeOkS

end Spike.Lib.A64.Rt.Test
