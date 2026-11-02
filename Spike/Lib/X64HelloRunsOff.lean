/-
**hello.w on x86-64: main's post-spawn pcs off the exits, decided on the listing** (the twin of
`Spike/Lib/A64HelloRunsOff.lean`): `X64RunsOff`'s decision at hello's code cells (`SccCode.helloCells`) per
sub-list of main's byte runs (one `decide +kernel` each), at any executable laying them out (`Lays`).

- `waitRunsL xl`, `flagRunsL xl`: `X64WakeRunsOff.waitRuns`'s and `X64WakeMainF.flagRuns`' byte runs with the
  tail-call label `xl` (`waitRunsL ".Lwc_waitLoop.x16"` is wake's, by `rfl`); `waitRunsH`, `flagRunsH` at
  hello's `LoopCode.waitXL` (`.x20`).
- `exitRunsH`: `scc_rt_main`'s `exit_group` tail at hello's return point `.Lscc_rt_main.x3` (15 bytes).
- `wait_chk`, `park_chk`, `exit_chk`; `wait_off`, `park_off`, `exit_off`: the checks and their `RunsOffA`.
- `flag_chk`, `hello_flag_ne`: the flag load's pc (byte `7` of `.entry`) is off `flagRunsH`.

Unlike AArch64, the runs are byte runs of the sized cells, and the labels are x86-64's (no `.Lnn_` prefix):
the wait loop's tail-call label is `.x20` at hello (wake: `.x16`), and the exit tail follows `scc_rt_main`'s
second call `.x3` (hello calls `wc_rodata` first; wake's tail is at `.x2`). As for AArch64, wake's
`parentRuns` (wake's `wc_main` shape) is not restated here.
-/
import Spike.Lib.X64RunsOff
import Spike.Lib.X64ParkW
import Spike.Lib.X64HelloLoopCode
import Spike.Lib.X64WakeRunsOffWait
import Spike.Lib.X64WakeMainF

namespace Spike.Lib.X64.HelloRunsOff

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib.X64.RunsOff (runsNeChk abPtsA runsOffA_of_chk runsNeQ_of_chk)
open Spike.Lib.X64.Flow.Park (parkRuns)
open Spike.Lib.X64.Hello.LoopCode (waitXL)

/-- **`wc_waitLoop`'s byte runs** with the tail-call label `xl`: from each of its labels to the next. -/
def waitRunsL (xl : Label) : List (String × Nat × Nat) :=
  [("wc_waitLoop", 0, 31), (".Lwc_waitLoop.entry", 0, 29), (".Lwc_waitLoop.then1", 0, 12),
    (".Lwc_waitLoop.else2", 0, 5), (xl, 0, 10)]

/-- **main's pcs at the flag load's control other than `q`** with the tail-call label `xl`: `waitRunsL xl`
without byte `7` of `.entry`, and `scc_rt_park`'s. -/
def flagRunsL (xl : Label) : List (String × Nat × Nat) :=
  [("wc_waitLoop", 0, 31), (".Lwc_waitLoop.entry", 0, 7), (".Lwc_waitLoop.entry", 8, 29),
    (".Lwc_waitLoop.else2", 0, 5), (xl, 0, 10)] ++ parkRuns

/-- At wake's label the runs are wake's. -/
example : waitRunsL ".Lwc_waitLoop.x16" = Spike.Lib.X64.WakeRunsOff.waitRuns ∧
    flagRunsL ".Lwc_waitLoop.x16" = Spike.Lib.X64WakeMainF.flagRuns := ⟨rfl, rfl⟩

/-- hello's wait-loop runs. -/
abbrev waitRunsH : List (String × Nat × Nat) := waitRunsL waitXL

/-- hello's flag runs. -/
abbrev flagRunsH : List (String × Nat × Nat) := flagRunsL waitXL

/-- **The `exit_group` tail's byte run** at `scc_rt_main`'s return point from `wc_main`. -/
def exitRunsH : List (String × Nat × Nat) := [(".Lscc_rt_main.x3", 0, 15)]

/-- `wc_waitLoop`'s runs are off the exits. -/
theorem wait_chk : runsNeChk SccCode.helloCells waitRunsH abPtsA = true := by decide +kernel

/-- `scc_rt_park`'s runs are off the exits. -/
theorem park_chk : runsNeChk SccCode.helloCells parkRuns abPtsA = true := by decide +kernel

/-- The `exit_group` tail's run is off the exits. -/
theorem exit_chk : runsNeChk SccCode.helloCells exitRunsH abPtsA = true := by decide +kernel

/-- A run over an abort exit is refused (the check is not vacuous). -/
example : runsNeChk SccCode.helloCells [("scc_rt_abort_heap", 0, 61)] abPtsA = false := by decide +kernel

section Off

variable {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
include hp

/-- **`wc_waitLoop`'s pcs are off every abort exit and the transfer sites.** -/
theorem wait_off : Spike.Lib.X64WakeOff.RunsOffA (_root_.Executable.labels exe).label waitRunsH :=
  runsOffA_of_chk hp wait_chk

/-- **`scc_rt_park`'s pcs are off every abort exit and the transfer sites.** -/
theorem park_off : Spike.Lib.X64WakeOff.RunsOffA (_root_.Executable.labels exe).label parkRuns :=
  runsOffA_of_chk hp park_chk

/-- **The `exit_group` tail's pcs are off every abort exit and the transfer sites.** -/
theorem exit_off : Spike.Lib.X64WakeOff.RunsOffA (_root_.Executable.labels exe).label exitRunsH :=
  runsOffA_of_chk hp exit_chk

end Off

/-- `flagRunsH` misses the flag load's pc. -/
theorem flag_chk : runsNeChk SccCode.helloCells flagRunsH [(".Lwc_waitLoop.entry", 7)] = true := by
  decide +kernel

/-- **main's flag load's pc is off its other post-spawn pcs**, in any executable laying out `helloCells`. -/
theorem hello_flag_ne {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe SccCode.helloCells kp) :
    Spike.Lib.X64WakeOff.RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label ".Lwc_waitLoop.entry" + Int64.ofNat 7) flagRunsH :=
  runsNeQ_of_chk hp flag_chk

end Spike.Lib.X64.HelloRunsOff

/-- info: 'Spike.Lib.X64.HelloRunsOff.wait_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloRunsOff.wait_off

/-- info: 'Spike.Lib.X64.HelloRunsOff.exit_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloRunsOff.exit_off

/-- info: 'Spike.Lib.X64.HelloRunsOff.hello_flag_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloRunsOff.hello_flag_ne
