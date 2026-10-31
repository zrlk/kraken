/-
**wake.w on x86-64: main's post-spawn pcs off the exits, decided on the
listing**: `X64RunsOff`'s decision at wake's code cells
(`SccCode.wakeCells`) for the byte runs of main's parent half
(`X64WakeParent`) and of `scc_rt_main`'s `exit_group` tail
(`X64WakeMainPost`), at any executable laying them out (`Lays`). The twin
of `Spike/Lib/A64WakeMainSegW.lean`'s `parentRuns` and `exitRuns`.

- `parentRuns`: the test and the `je` after the clone (`.x21 + 48` to
  `+ 53`), `.x22`'s block and its branch (`.x22` to `+ 22`), `.spawned6`
  (13 bytes).
- `exitRuns`: `scc_rt_main`'s return point `.x2` (the tail's three
  instructions and the `syscall`, 15 bytes).
- `parent_chkA`, `exit_chkA`: the checks, by `decide +kernel`.
- `wake_parentRuns_offA`, `wake_exitRuns_offA`: `X64WakeOff.RunsOffA` at
  wake.
-/
import Spike.Lib.X64RunsOff
import Spike.Lib.X64WakeCode

namespace Spike.Lib.X64.WakeRunsOff

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib.X64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)

/-- **The parent half's byte runs**: the test and the `je` after the
clone's `syscall`, `.x22`'s block and its `jmp`, `.spawned6`. -/
def parentRuns : List (String × Nat × Nat) :=
  [(".Lwc_main.x21", 48, 53), (".Lwc_main.x22", 0, 22), (".Lwc_main.spawned6", 0, 13)]

/-- **The `exit_group` tail's byte run** at `scc_rt_main`'s return point. -/
def exitRuns : List (String × Nat × Nat) := [(".Lscc_rt_main.x2", 0, 15)]

/-- The parent half's byte runs miss `PcOffA`'s points. -/
theorem parent_chkA : runsNeChk SccCode.wakeCells parentRuns abPtsA = true := by decide +kernel

/-- The tail's byte run misses `PcOffA`'s points. -/
theorem exit_chkA : runsNeChk SccCode.wakeCells exitRuns abPtsA = true := by decide +kernel

/-- **The parent half's pcs off all five abort exits and the transfer
sites** at wake. -/
theorem wake_parentRuns_offA {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat}
    (hl : Lays exe SccCode.wakeCells kp) :
    Spike.Lib.X64WakeOff.RunsOffA (_root_.Executable.labels exe).label parentRuns :=
  runsOffA_of_chk hl parent_chkA

/-- **The `exit_group` tail's pcs off all five abort exits and the transfer
sites** at wake. -/
theorem wake_exitRuns_offA {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat}
    (hl : Lays exe SccCode.wakeCells kp) :
    Spike.Lib.X64WakeOff.RunsOffA (_root_.Executable.labels exe).label exitRuns :=
  runsOffA_of_chk hl exit_chkA

end Spike.Lib.X64.WakeRunsOff

/-- info: 'Spike.Lib.X64.WakeRunsOff.wake_parentRuns_offA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRunsOff.wake_parentRuns_offA

/-- info: 'Spike.Lib.X64.WakeRunsOff.wake_exitRuns_offA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRunsOff.wake_exitRuns_offA
