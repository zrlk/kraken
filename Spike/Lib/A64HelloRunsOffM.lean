/-
**hello.w on AArch64: main's parent and `exit_group` tail pcs off the exits, decided on the listing**: the parent's
and the exit tail's halves of `A64HelloRunsOff.lean` at hello's own runs
(`A64HelloMainSegW.parentRunsH`, `exitRunsH`), by `RunsOff.runsOffA_of_chk` decided on `SccCode.helloProg`
(one `decide +kernel` each), at any executable laying out `helloProg`.

- `parentH_chk`, `exitH_chk`: the decisions; `parentH_off`, `exitH_off`: their `RunsOffA`.
- `mainRunsH`: main's post-spawn runs at hello (the loop's at `.L21_wc_waitLoop`, the park's, `parentRunsH`,
  `exitRunsH`); `mainRunsH_off`: `RunsOffA lab mainRunsH` (the one pc obligation of hello's `MainClosedW`).

`A64HelloRunsOff.exit_off` (wake's `exitRuns`, at wake's `.sp0`) is not used by hello: its tail is `exitRunsH`.

Superseded by `A64HelloMainClosedW.mainRunsH`/`mainRunsH_off` (same runs) and
`A64HelloMainSegW.parent_off`/`exit_off`; kept building, use those.
-/
import Spike.Lib.A64HelloRunsOff
import Spike.Lib.A64HelloMainSegW

namespace Spike.Lib.A64.HelloRunsOffM

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (Lays)
open Spike.Lib.A64WakeOff (RunsOffA)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open Spike.Lib.A64.HelloLabels (pfx)
open Spike.Lib.A64HelloMainSegW (parentRunsH exitRunsH)
open SccCode (helloProg)

/-- The parent's runs (past the spawn, to its tail call) are off the exits. -/
theorem parentH_chk : runsNeChk helloProg parentRunsH abPtsA = true := by decide +kernel

/-- hello's `exit_group` tail's runs (at `.sp1`) are off the exits. -/
theorem exitH_chk : runsNeChk helloProg exitRunsH abPtsA = true := by decide +kernel

/-- **main's post-spawn pcs at hello**: the loop's, the park's, the parent's and the `exit_group` tail's runs. -/
def mainRunsH : List (String × Nat × Nat) :=
  Spike.Lib.A64WakeMainW.waitRuns pfx ++ Spike.Lib.A64.Flow.Park.parkRuns ++ parentRunsH ++ exitRunsH

/-- All of `mainRunsH` is off the exits. -/
theorem mainRunsH_chk : runsNeChk helloProg mainRunsH abPtsA = true := by decide +kernel

section Off

variable {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe helloProg kp)
include hp

/-- **The parent's pcs are off every abort exit and the transfer sites.** -/
theorem parentH_off : RunsOffA (_root_.Executable.labels exe).label parentRunsH :=
  runsOffA_of_chk hp parentH_chk

/-- **hello's `exit_group` tail's pcs are off every abort exit and the transfer sites.** -/
theorem exitH_off : RunsOffA (_root_.Executable.labels exe).label exitRunsH :=
  runsOffA_of_chk hp exitH_chk

/-- **main's post-spawn pcs at hello are off every abort exit and the transfer sites** (`hruns` of hello's
`MainClosedW`), in any executable laying out `helloProg`. -/
theorem mainRunsH_off : RunsOffA (_root_.Executable.labels exe).label mainRunsH :=
  runsOffA_of_chk hp mainRunsH_chk

end Off

end Spike.Lib.A64.HelloRunsOffM

/-- info: 'Spike.Lib.A64.HelloRunsOffM.mainRunsH_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.HelloRunsOffM.mainRunsH_off
