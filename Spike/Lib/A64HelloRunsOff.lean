/-
**hello.w on AArch64: main's post-spawn pcs off the exits, decided on the
listing** (B2): the restatement of `A64WakeRunsOff.lean` at
hello.w's listing (`SccCode.helloProg`, `Spike/Lib/A64HelloCode.lean`), by
`RunsOff.runsOffA_of_chk` decided on `helloProg` per sub-list of main's runs
(one `decide +kernel` each), at any executable laying out `helloProg`
(`Lays`). No address or index is written here.

- `wait_chk`, `park_chk`, `exit_chk`: `wc_waitLoop`'s (at hello's prefix
  `.L21_wc_waitLoop`), `scc_rt_park`'s and the `exit_group` tail's runs are
  off the exits; `wait_off`, `park_off`, `exit_off`: their `RunsOffA`.
- `flag_chk`, `hello_flag_ne`: the flag check's pc
  (`label (pfx ++ ".0_entry") + 4 + 4`) none of `A64WakeMainF.flagRuns`',
  `RunsOff.runsNe_of_chk` at the point `(pfx ++ ".0_entry", 2)`.

Deferred: wake's `parent_chk` (`A64WakeMainSegW.parentRuns`, wake's
`wc_main` shape; it fails on `helloProg`) and so `wake_mainRuns_off` (all of
`A64WakeMainClosedW.mainRuns`) to B3/B6, with hello's `wc_main` segments.
-/
import Spike.Lib.A64RunsOff
import Spike.Lib.A64WakeMainSegW
import Spike.Lib.A64WakeMainF
import Spike.Lib.A64HelloLabels

namespace Spike.Lib.A64.HelloRunsOff

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (Lays)
open Spike.Lib.A64WakeOff (RunsOffA)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk runsNe_of_chk)
open Spike.Lib.A64.HelloLabels (pfx)
open SccCode (helloProg)

/-- `wc_waitLoop`'s runs are off the exits. -/
theorem wait_chk : runsNeChk helloProg (Spike.Lib.A64WakeMainW.waitRuns pfx) abPtsA = true := by
  decide +kernel

/-- `scc_rt_park`'s runs are off the exits. -/
theorem park_chk : runsNeChk helloProg Spike.Lib.A64.Flow.Park.parkRuns abPtsA = true := by decide +kernel

/-- The `exit_group` tail's runs are off the exits. -/
theorem exit_chk : runsNeChk helloProg Spike.Lib.A64WakeMainSegW.exitRuns abPtsA = true := by decide +kernel

section Off

variable {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe helloProg kp)
include hp

/-- **`wc_waitLoop`'s pcs are off every abort exit and the transfer sites**,
in any executable laying out `helloProg`. -/
theorem wait_off : RunsOffA (_root_.Executable.labels exe).label (Spike.Lib.A64WakeMainW.waitRuns pfx) :=
  runsOffA_of_chk hp wait_chk

/-- **`scc_rt_park`'s pcs are off every abort exit and the transfer sites.** -/
theorem park_off : RunsOffA (_root_.Executable.labels exe).label Spike.Lib.A64.Flow.Park.parkRuns :=
  runsOffA_of_chk hp park_chk

/-- **The `exit_group` tail's pcs are off every abort exit and the transfer
sites.** -/
theorem exit_off : RunsOffA (_root_.Executable.labels exe).label Spike.Lib.A64WakeMainSegW.exitRuns :=
  runsOffA_of_chk hp exit_chk

end Off

/-- The flag check's pc is none of `flagRuns`'. -/
theorem flag_chk :
    runsNeChk helloProg (Spike.Lib.A64WakeMainF.flagRuns pfx) [(pfx ++ ".0_entry", 2)] = true := by
  decide +kernel

/-- **main's flag check's pc is off its other post-spawn pcs** (wake's
`main_closed_wakeW`'s `hflag`), in any executable laying out `helloProg`. -/
theorem hello_flag_ne {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe helloProg kp) :
    Spike.Lib.A64WakeOff.RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label (pfx ++ ".0_entry") + 4 + 4)
      (Spike.Lib.A64WakeMainF.flagRuns pfx) := by
  intro r hr j hlo hhi
  have h := runsNe_of_chk hp flag_chk r hr j hlo hhi _ (List.mem_singleton_self _)
  rwa [Int64.add_assoc, show (4 : Int64) + 4 = Int64.ofNat (4 * 2) by decide]

end Spike.Lib.A64.HelloRunsOff

/-- info: 'Spike.Lib.A64.HelloRunsOff.wait_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.HelloRunsOff.wait_off

/-- info: 'Spike.Lib.A64.HelloRunsOff.hello_flag_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.HelloRunsOff.hello_flag_ne
