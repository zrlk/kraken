/-
**The AArch64 runtime's code checks in one pass on `ret0.w` and
`hello1.w`** (`Spike/Lib/Rt/A64RtCode.lean`): `rtCodeOk` holds on
`ret0Prog` at `bareMC`, the `scc_rt_main` of its placement data's bare tail,
its checks are the hand ones, and it fails on a wrong frame and on
`hello1.w`'s `scc_rt_main`, which has a setup block.
-/
import Spike.Lib.Rt.A64RtCode
import Spike.Lib.Rt.A64MainRet0
import Spike.Test.A64Hello1PlaceOK

namespace Spike.Lib.A64.Rt.Test

open Spike.Lib.A64.Rt Spike.Lib.A64.Flow

/-- `ret0.w`'s placement data has the bare tail; its `MainCode` is the oracle's. -/
example : Scc.Cert.PlaceOK.A64.Test.ret0Place.tail = .bare := rfl
example : ret0MC = bareMC := rfl

/-- **`ret0.w`'s runtime code in one pass.** -/
theorem ret0_rtCodeOk : rtCodeOk SccCode.ret0Prog bareMC = true := by decide +kernel

/-- Its checks are the hand ones. -/
example : RtCodeIn SccCode.ret0Prog ret0MC :=
  ⟨Ret0.ret0_entryIn, ret0_startIn, Ret0.ret0_startCallIn, Ret0.ret0_startTailIn, ret0_mainUIn,
    Ret0.AllocTcb.ret0_allocTcbIn, Ret0.ThreadInit.ret0_threadInitIn, Ret0.ret0_tiSpIn,
    Ret0.StackTake.ret0_stackTakeIn⟩

example : (rtCodeIn_of_ok ret0_rtCodeOk).main = ret0_mainUIn := rfl

/-- A wrong frame fails. -/
example : rtCodeOk SccCode.ret0Prog { bareMC with Z := 64 } = false := by decide +kernel

/-- `hello1.w`'s `scc_rt_main` has a setup block: its tail is not the bare
one, and the bare `MainCode` fails. -/
example : Scc.Cert.PlaceOK.A64.Test.hello1Place.tail = .setup := rfl
example : rtCodeOk SccCode.hello1Prog bareMC = false := by decide +kernel

end Spike.Lib.A64.Rt.Test
