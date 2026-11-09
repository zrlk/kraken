/-
**Code across a label on `ret0.w`'s cells** (`Spike/Lib/X64CodeAcross.lean`):
`scc_rt_start`'s three cells before `.Lscc_rt_start.entry` and the first two
after it are one code segment, from the decided checks (`blockAt`,
`labelGap`); a wrong gap fails.
-/
import Spike.Lib.X64CodeAcross
import Spike.Lib.X64Ret0Code

namespace Spike.Lib.X64.CodeAcrossTest

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAt labelGap)

/-- `scc_rt_start`'s cells before its body label. -/
def a : List (Directive × Nat) := (SccCode.ret0Cells.drop 7).take 3
/-- The first two cells after it. -/
def b : List (Directive × Nat) := (SccCode.ret0Cells.drop 11).take 2

theorem ha : blockAt SccCode.ret0Cells "scc_rt_start" 0 0 a = true := by decide +kernel
theorem hg : labelGap SccCode.ret0Cells "scc_rt_start" ".Lscc_rt_start.entry" (0 + a.length)
    (0 + (a.map (·.2)).sum) = true := by decide +kernel
theorem hb : blockAt SccCode.ret0Cells ".Lscc_rt_start.entry" 0 0 b = true := by decide +kernel

/-- The label is no instruction: `a` is three cells of eight bytes. -/
example : a.length = 3 ∧ (a.map (·.2)).sum = 8 := by decide +kernel
/-- A wrong distance fails. -/
example : labelGap SccCode.ret0Cells "scc_rt_start" ".Lscc_rt_start.entry" 3 7 = false := by decide +kernel

/-- **One segment across `.Lscc_rt_start.entry`**, in any layout of `ret0.w`'s cells. -/
example {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {p : Nat}
    (hp : Lays exe SccCode.ret0Cells p) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe SccCode.ret0Cells p) :
    CodeAt st ((_root_.Executable.labels exe).label "scc_rt_start" + Int64.ofNat 0) (a ++ b) :=
  codeAt_across hp he hend ha hg hb

end Spike.Lib.X64.CodeAcrossTest
