/-
**wake.w on AArch64: main's post-spawn pcs off the exits, decided on the
listing** (the listing facts at the instance): `hruns` of
`A64WakeMainClosedW.main_closed_wakeW`, `RunsOffA lab mainRuns`, at any
executable laying out `wakeProg` (`Lays`), by `RunsOff.runsOffA_of_chk`
decided on `wakeProg` per sub-list of `mainRuns` (one `decide +kernel` each).
No address or index is written here: a new certificate only re-runs the
checks. The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

- `runsOffA_append`: `RunsOffA` of an append.
- `wait_chk`, `park_chk`, `parent_chk`, `exit_chk`: the four sub-lists'
  checks.
- `wake_mainRuns_off`: `RunsOffA (exe.labels).label mainRuns`.
- `flag_chk`, `wake_flag_ne`: `main_closed_wakeW`'s `hflag`, the flag check's
  pc (`label (pfx ++ ".0_entry") + 4 + 4`) none of `A64WakeMainF.flagRuns`',
  `RunsOff.runsNe_of_chk` at the point `(pfx ++ ".0_entry", 2)`.
-/
import Spike.Lib.A64RunsOff
import Spike.Lib.A64WakeMainClosedW
import Spike.Lib.A64WakeMainF

namespace Spike.Lib.A64.WakeRunsOff

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (Lays)
open Spike.Lib.A64WakeOff (RunsOffA)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk runsNe_of_chk)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-- `RunsOffA` of an append. -/
theorem runsOffA_append {lab : String → Int64} {a b : List (String × Nat × Nat)} (ha : RunsOffA lab a)
    (hb : RunsOffA lab b) : RunsOffA lab (a ++ b) := fun q hq =>
  (List.mem_append.mp hq).elim (ha q) (hb q)

/-- `wc_waitLoop`'s runs are off the exits. -/
theorem wait_chk : runsNeChk wakeProg (Spike.Lib.A64WakeMainW.waitRuns WakeLabels.pfx) abPtsA = true := by
  decide +kernel

/-- `scc_rt_park`'s runs are off the exits. -/
theorem park_chk : runsNeChk wakeProg Spike.Lib.A64.Flow.Park.parkRuns abPtsA = true := by decide +kernel

/-- The parent's runs are off the exits. -/
theorem parent_chk : runsNeChk wakeProg Spike.Lib.A64WakeMainSegW.parentRuns abPtsA = true := by
  decide +kernel

/-- The `exit_group` tail's runs are off the exits. -/
theorem exit_chk : runsNeChk wakeProg Spike.Lib.A64WakeMainSegW.exitRuns abPtsA = true := by decide +kernel

/-- **main's post-spawn pcs are off every abort exit and the transfer
sites** (`main_closed_wakeW`'s `hruns`), in any executable laying out
`wakeProg`. -/
theorem wake_mainRuns_off {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeProg kp) :
    RunsOffA (_root_.Executable.labels exe).label Spike.Lib.A64WakeMainClosedW.mainRuns :=
  runsOffA_append (runsOffA_append (runsOffA_append (runsOffA_of_chk hp wait_chk) (runsOffA_of_chk hp park_chk))
    (runsOffA_of_chk hp parent_chk)) (runsOffA_of_chk hp exit_chk)

/-- info: 'Spike.Lib.A64.WakeRunsOff.wake_mainRuns_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_mainRuns_off

/-- The flag check's pc is none of `flagRuns`'. -/
theorem flag_chk :
    runsNeChk wakeProg (Spike.Lib.A64WakeMainF.flagRuns WakeLabels.pfx) [(WakeLabels.pfx ++ ".0_entry", 2)] = true := by
  decide +kernel

/-- **main's flag check's pc is off its other post-spawn pcs**
(`main_closed_wakeW`'s `hflag`), in any executable laying out `wakeProg`. -/
theorem wake_flag_ne {exe : _root_.Executable} [Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeProg kp) :
    Spike.Lib.A64WakeOff.RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label (WakeLabels.pfx ++ ".0_entry") + 4 + 4)
      (Spike.Lib.A64WakeMainF.flagRuns WakeLabels.pfx) := by
  intro r hr j hlo hhi
  have h := runsNe_of_chk hp flag_chk r hr j hlo hhi _ (List.mem_singleton_self _)
  rwa [Int64.add_assoc, show (4 : Int64) + 4 = Int64.ofNat (4 * 2) by decide]

/-- info: 'Spike.Lib.A64.WakeRunsOff.wake_flag_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_flag_ne

end Spike.Lib.A64.WakeRunsOff
