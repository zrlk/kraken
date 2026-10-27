/-
**`hello1.w`'s start up to `scc_rt_main`'s entry** (x86-64): the runtime's
code but `scc_rt_main`'s, `scc_rt_thread_init`'s returning to `.x8`
(`RtCodeInTi … x8L`), from its setup pass at four words (`setupMC 4`), so
that `startE_segW` (`Spike/Lib/Rt/X64StartE.lean`) applies to
`hello1Cells`. The x86-64 twin of `Spike/Test/A64Hello1StartE.lean`; the
setup pass itself is `Spike.Lib.X64.Rt.Test.hello1_rtCodeOkS`
(`Spike/Test/X64RtCode.lean`).
-/
import Spike.Lib.Rt.X64StartE
import Spike.Test.X64RtCode

namespace Spike.Lib.X64.Rt.Test

open Spike.Lib.X64.Rt

/-- **`hello1.w`'s runtime code but `scc_rt_main`'s**, `scc_rt_thread_init`
returning to `.x8`. -/
theorem hello1_rtCodeInTi : RtCodeInTi SccCode.hello1Cells x8L := rtCodeInTi_of_okS hello1_rtCodeOkS

-- No axioms beyond Lean's.
/--
info: 'Spike.Lib.X64.Rt.Test.hello1_rtCodeInTi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_rtCodeInTi

/--
info: 'Spike.Lib.X64.Rt.startE_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms startE_segWS

end Spike.Lib.X64.Rt.Test
