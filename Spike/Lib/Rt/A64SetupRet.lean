/-
**The setup block's result registers on AArch64** for `SetupPostS`
(`Spike/Lib/SetupRet.lean`): register `i` is `x i` (`argX`).
-/
import Spike.Lib.SetupRet
import Spike.Lib.Rt.A64CodeInSetup

namespace Spike.Lib.A64.Rt

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64

/-- **The AArch64 result register reader**: register `i` is `x i`. -/
def rdA64 (i : Nat) (r : Reg64s) : BitVec 64 := (r.getXReg (argX i)).toBitVec

end Spike.Lib.A64.Rt
