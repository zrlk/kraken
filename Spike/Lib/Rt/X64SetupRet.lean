/-
**The setup block's result registers on x86-64** for `SetupPostS`
(`Spike/Lib/SetupRet.lean`): register `i` is `retXs[i]` (`%rax`, `%rdx`,
`%rcx`, `%rsi`, `%rdi`, `%r8`).
-/
import Spike.Lib.SetupRet
import Spike.Lib.Rt.X64CodeInSetup

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Kraken.X64.Parser

/-- **The x86-64 result register reader**: register `i` is `retXs[i]`. -/
def rdX64 (i : Nat) (r : Reg64s) : BitVec 64 := r.get64 (retXs.getD i .rax)

end Spike.Lib.X64.Rt
