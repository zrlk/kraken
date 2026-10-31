/-
**wake.w on x86-64: `scc_rt_park`'s pcs off the exits, decided on the
listing**: `X64RunsOff`'s decisions at wake's code cells
(`SccCode.wakeCells`) for `Park.parkRuns`, at any executable laying them
out (`Lays`). The first instance of `X64RunsOff`; main's other runs follow
with their twins (`X64WakeRunsOff`).

- `park_chk`, `park_chkA`: the checks, by `decide +kernel`.
- `wake_parkRuns_off`: `ParkW`'s `hW` (`X64AbOffL.RunsOff`).
- `wake_parkRuns_offA`: `X64WakeOff.RunsOffA` (all five abort exits).
-/
import Spike.Lib.X64RunsOff
import Spike.Lib.X64WakeCode
import Spike.Lib.X64ParkW

namespace Spike.Lib.X64.WakeRunsOff

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib.X64.RunsOff (runsNeChk abPts abPtsA runsOff_of_chk runsOffA_of_chk)
open Spike.Lib.X64.Flow.Park (parkRuns)

/-- `scc_rt_park`'s byte runs miss `PcOff`'s points. -/
theorem park_chk : runsNeChk SccCode.wakeCells parkRuns abPts = true := by decide +kernel

/-- `scc_rt_park`'s byte runs miss `PcOffA`'s points. -/
theorem park_chkA : runsNeChk SccCode.wakeCells parkRuns abPtsA = true := by decide +kernel

/-- A run over an abort exit is refused (the check is not vacuous). -/
example : runsNeChk SccCode.wakeCells [("scc_rt_abort_heap", 0, 61)] abPtsA = false := by decide +kernel

/-- **`ParkW`'s `hW` at wake.** -/
theorem wake_parkRuns_off {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat}
    (hl : Lays exe SccCode.wakeCells kp) : Spike.Lib.X64AbOffL.RunsOff (_root_.Executable.labels exe).label parkRuns :=
  runsOff_of_chk hl park_chk

/-- **Park's pcs off all five abort exits and the transfer sites** at wake. -/
theorem wake_parkRuns_offA {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat}
    (hl : Lays exe SccCode.wakeCells kp) :
    Spike.Lib.X64WakeOff.RunsOffA (_root_.Executable.labels exe).label parkRuns :=
  runsOffA_of_chk hl park_chkA

end Spike.Lib.X64.WakeRunsOff

/-- info: 'Spike.Lib.X64.WakeRunsOff.wake_parkRuns_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRunsOff.wake_parkRuns_off
