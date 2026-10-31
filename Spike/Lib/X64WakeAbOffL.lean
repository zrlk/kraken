/-
**Off wake's exit calls and transfer sites, decided by label** (x86-64; twin
of `Spike/Lib/A64WakeAbOffL.lean`): the pc test `Spike.Lib.X64AbOffL.PcOff`
(the `writeErr`/`threads` abort exits and the take/release sites), stated
unfolded, at a pc `label l + k0 + k` of wake.w's cells
(`SccCode.wakeCells`), decided on the cells (`abChk`, through
`X64RunsOff.runsOff_of_chk`).

- `abChk l k0 len`: none of the bytes `k0 .. k0 + len` after `l` is one of
  the four labels (`runsNeChk` of the one byte run `(l, k0, k0 + len)`
  against `RunsOff.abPts`).
- `abOff_at`: at such a pc the pc is none of the four labels.

**Unlike AArch64**: runs are **byte** ranges (`X64AbOffLDef`), so `abChk`
counts bytes and a pc is `label l + ofNat k0 + ofNat k` (A64: instruction
indices, `label l + 4k0 + 4k`); the decision is `X64RunsOff.runsNeChk` (A64:
`PcRuns.inRuns` per instruction, `abRuns`/`wake_abRunsOk` have no
counterpart: the points are `RunsOff.abPts`); `abOff_at` takes no
`s.exe = exe` (the pc test reads only `s.st.2`). The `wc_waitLoop` limit
load half (`wait_tlsChk`, `wait_tlsCode`, `seg_waitTlsW`, `seg_waitTlsLim`)
has no x86-64 counterpart: `X64WaitLoop.seg_waitLoop` takes the limit
word's facts directly (`hlim`), its `%fs:8` load being a prologue node, with
no `htls` segment premise.
-/
import Spike.Lib.X64RunsOff
import Spike.Lib.X64WakeCode

namespace Spike.Lib.X64.Flow.Worker.Wake.AbOffAt

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib.X64.RunsOff (runsNeChk abPts runsOff_of_chk)
open SccCode (wakeCells)

/-- **None of the bytes `k0 .. k0 + len` after `l` is an exit call or a
transfer site**, decided on wake's cells. -/
def abChk (l : Label) (k0 len : Nat) : Bool :=
  runsNeChk wakeCells [(l, k0, k0 + len)] abPts

/-- `wc_waitLoop`'s whole prologue and loop (its first 60 bytes) is off them. -/
example : abChk "wc_waitLoop" 0 60 = true := by decide +kernel

/-- A run over the take site is refused (the check is not vacuous). -/
example : abChk "scc_rt_take_site" 0 1 = false := by decide +kernel

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe wakeCells kp)
include hp

/-- **Off the exit calls at a decided pc** (`AbOffL`, unfolded): the byte
`k0 + k` after `l`, `k < len`, with `abChk l k0 len`. -/
theorem abOff_at {l : Label} {k0 len : Nat} (hchk : abChk l k0 len = true) {s : State} {k : Nat}
    (hk : k < len)
    (hs : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat k0 + Int64.ofNat k) :
    s.st.2 ≠ (_root_.Executable.labels exe).label "scc_rt_abort_write_exit" ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label "scc_rt_abort_threads_exit" ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label "scc_rt_take_site" ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label "scc_rt_release_site" := by
  rw [hs]
  exact Spike.Lib.X64AbOffL.pcOff_add (runsOff_of_chk hp hchk) List.mem_cons_self (Nat.le_refl k0)
    (by omega) rfl

end Inst

end Spike.Lib.X64.Flow.Worker.Wake.AbOffAt

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.AbOffAt.abOff_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Wake.AbOffAt.abOff_at
