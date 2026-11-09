/-
**wake.w on x86-64: `wc_waitLoop`'s pcs off the exits, decided on the
listing**: `X64RunsOff`'s decision at wake's code cells
(`SccCode.wakeCells`) for `waitRuns`, the byte runs after `wc_waitLoop`'s
labels, at any executable laying them out (`Lays`). The twin of
`Spike/Lib/A64WakeMainW.lean`'s `waitRuns` with its check.

- `waitRuns`: the function's label up to `.entry` (the stack-checked
  prologue, `.chk` inside it), `.entry` (`b4`, the load, `b5`, `b6`),
  `.then1`, `.else2` (the park call), `.x16` (the tail call). The stack grow
  path (`.stk`) has no node and is not a run.
- `wait_chkA`: the check, by `decide +kernel`.
- `wake_waitRuns_offA`: `X64WakeOff.RunsOffA` at wake.
-/
import Spike.Lib.X64RunsOff
import Spike.Lib.X64WakeCode

namespace Spike.Lib.X64.WakeRunsOff

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib.X64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)

/-- **`wc_waitLoop`'s byte runs**: from each of its labels to the next. -/
def waitRuns : List (String × Nat × Nat) :=
  [("wc_waitLoop", 0, 31), (".Lwc_waitLoop.entry", 0, 29), (".Lwc_waitLoop.then1", 0, 12),
    (".Lwc_waitLoop.else2", 0, 5), (".Lwc_waitLoop.x1", 0, 10)]

/-- `wc_waitLoop`'s byte runs miss `PcOffA`'s points. -/
theorem wait_chkA : runsNeChk SccCode.wakeCells waitRuns abPtsA = true := by decide +kernel

/-- **`wc_waitLoop`'s pcs off all five abort exits and the transfer sites** at
wake. -/
theorem wake_waitRuns_offA {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat}
    (hl : Lays exe SccCode.wakeCells kp) :
    Spike.Lib.X64WakeOff.RunsOffA (_root_.Executable.labels exe).label waitRuns :=
  runsOffA_of_chk hl wait_chkA

end Spike.Lib.X64.WakeRunsOff

/-- info: 'Spike.Lib.X64.WakeRunsOff.wake_waitRuns_offA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRunsOff.wake_waitRuns_offA
