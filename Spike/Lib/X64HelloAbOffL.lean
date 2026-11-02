/-
**Off hello's exit calls and transfer sites, decided by label** (x86-64; the
twin of `Spike/Lib/A64HelloAbOffL.lean`, the restatement of
`Spike/Lib/X64WakeAbOffL.lean` at hello.w's cells `SccCode.helloCells`,
`Spike/Lib/X64HelloCode.lean`): the pc test `Spike.Lib.X64AbOffL.PcOff` (the
`writeErr`/`threads` abort exits and the take/release sites), stated
unfolded, at a pc `label l + k0 + k` of hello's cells, decided on the cells
(`abChk`, through `X64RunsOff.runsOff_of_chk`).

- `abChk l k0 len`: none of the bytes `k0 .. k0 + len` after `l` is one of
  the four labels (`runsNeChk` of the one byte run `(l, k0, k0 + len)`
  against `RunsOff.abPts`).
- `abOff_at`: at such a pc the pc is none of the four labels.

**Deviation from the A64 file.** As in `X64WakeAbOffL`: runs are byte
ranges, so `abChk` counts bytes and a pc is `label l + ofNat k0 + ofNat k`
(A64: instruction indices; `abRuns`/`hello_abRunsOk` have no counterpart, the
points are `RunsOff.abPts`). The `wc_waitLoop` limit load half
(`wait_tlsChk`, `wait_tlsCode`, `seg_waitTlsW`, `seg_waitTlsLim`) has no
x86-64 counterpart: `X64WaitLoop.seg_waitLoop` takes the limit word's facts
directly (`hlim`), its `%fs:8` load being a prologue node, so main's
consumers (`A64HelloMainSF`'s uses of `wait_tlsCode`) follow
`X64WakeMainF`, which has none.
-/
import Spike.Lib.X64RunsOff
import Spike.Lib.X64HelloCode

namespace Spike.Lib.X64.Flow.Worker.Hello.AbOffAt

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib.X64.RunsOff (runsNeChk abPts runsOff_of_chk)
open SccCode (helloCells)

/-- **None of the bytes `k0 .. k0 + len` after `l` is an exit call or a
transfer site**, decided on hello's cells. -/
def abChk (l : Label) (k0 len : Nat) : Bool :=
  runsNeChk helloCells [(l, k0, k0 + len)] abPts

/-- `wc_waitLoop`'s whole prologue and loop (its first 60 bytes) is off them. -/
example : abChk "wc_waitLoop" 0 60 = true := by decide +kernel

/-- A run over the take site is refused (the check is not vacuous). -/
example : abChk "scc_rt_take_site" 0 1 = false := by decide +kernel

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
  (hp : Lays exe helloCells kp)
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

end Spike.Lib.X64.Flow.Worker.Hello.AbOffAt

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbOffAt.abOff_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbOffAt.abOff_at
