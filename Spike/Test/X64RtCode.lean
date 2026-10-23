/-
**The x86-64 runtime's code checks in one pass on `ret0.w` and
`hello1.w`** (`Spike/Lib/Rt/X64RtCode.lean`): `rtCodeOk` holds on
`ret0Cells` at the `scc_rt_main` its placement data names (`Scc.Cert.PlaceOK.X64.mcOf`), its
checks are the hand ones, and it fails on a wrong frame and on `hello1.w`'s
`scc_rt_main`, which has a setup block.
-/
import Spike.Lib.Rt.X64RtCode
import Spike.Lib.Rt.X64MainRet0
import Spike.Test.X64Ret0PlaceOK
import Spike.Test.X64Hello1PlaceOK

namespace Spike.Lib.X64.Rt.Test

open Spike.Lib.X64.Rt Spike.Lib.X64.Flow

/-- `ret0.w`'s placement data names `bareMC`, the oracle's `ret0MC`. -/
example : Scc.Cert.PlaceOK.X64.mcOf Scc.Cert.PlaceOK.X64.Test.ret0Place.tail = some ret0MC := rfl

/-- **`ret0.w`'s runtime code in one pass.** -/
theorem ret0_rtCodeOk : rtCodeOk SccCode.ret0Cells bareMC = true := by decide +kernel

/-- Its checks are the hand ones. -/
example : RtCodeIn SccCode.ret0Cells ret0MC :=
  ⟨by decide +kernel, ret0_startIn, Ret0.ret0_startCallIn, Ret0.ret0_startCall2In, Ret0.ret0_startTailIn, ret0_mainUIn,
    Ret0.AllocTcb.ret0_allocTcbIn, Ret0.ThreadInit.ret0_threadInitIn, Ret0.StackTake.ret0_stackTakeIn⟩

example : (rtCodeIn_of_ok ret0_rtCodeOk).main = ret0_mainUIn := rfl

/-- A wrong frame fails. -/
example : rtCodeOk SccCode.ret0Cells { bareMC with Z := 48 } = false := by decide +kernel

/-- `_start`'s code is checked: `hello1.w`'s `_start` passes, and with
`andq $-16, %rsp` dropped from `ret0.w`'s cells the check fails. -/
example : Code.Start.entryIn SccCode.hello1Cells = true := by decide +kernel
example : rtCodeOk (SccCode.ret0Cells.filter (· != (andRsp (-16), 4))) bareMC = false := by decide +kernel

/-- `hello1.w`'s `scc_rt_main` has a setup block: no `MainCode`, and the bare
one fails. -/
example : Scc.Cert.PlaceOK.X64.mcOf Scc.Cert.PlaceOK.X64.Test.hello1Place.tail = none := rfl
example : rtCodeOk SccCode.hello1Cells bareMC = false := by decide +kernel

end Spike.Lib.X64.Rt.Test
