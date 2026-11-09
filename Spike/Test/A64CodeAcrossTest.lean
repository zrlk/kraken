/-
**Code across a label on `ret0.w`'s program** (`Spike/Lib/A64CodeAcross.lean`):
`scc_rt_start`'s four instructions before `.L0_scc_rt_start.0_entry` and the
first three after it are one code segment, from the decided checks
(`blockAt`, `labelGap`); a wrong gap fails.
-/
import Spike.Lib.A64CodeAcross
import Spike.Lib.A64Ret0Code

namespace Spike.Lib.A64.CodeAcrossTest

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap)

/-- `scc_rt_start`'s instructions before its body label. -/
def a : List Directive := (SccCode.ret0Prog.drop 4).take 4
/-- The first three instructions after it. -/
def b : List Directive := (SccCode.ret0Prog.drop 9).take 3

theorem ha : blockAt SccCode.ret0Prog "scc_rt_start" 0 a = true := by decide +kernel
theorem hg : labelGap SccCode.ret0Prog "scc_rt_start" ".L0_scc_rt_start.0_entry" (0 + a.length) = true := by
  decide +kernel
theorem hb : blockAt SccCode.ret0Prog ".L0_scc_rt_start.0_entry" 0 b = true := by decide +kernel

/-- A wrong distance fails. -/
example : labelGap SccCode.ret0Prog "scc_rt_start" ".L0_scc_rt_start.0_entry" 3 = false := by decide +kernel

/-- **One segment across `.L0_scc_rt_start.0_entry`**, in any layout of `ret0.w`'s program. -/
example {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {p : Nat}
    (hp : Lays exe SccCode.ret0Prog p) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe SccCode.ret0Prog p) :
    CodeAt st ((_root_.Executable.labels exe).label "scc_rt_start" + Int64.ofNat (4 * 0)) (a ++ b) :=
  codeAt_across hp he hend ha hg hb

end Spike.Lib.A64.CodeAcrossTest
