/-
**Part 1: the SWP spinlock released by a
release-only swap — the program and its static checks** (on `EnvGC`,
`EnvG/RmwGhost.lean`).

The worker of `spinlock_swpl2.kl`/`spinlock_swpl3.kl`: `spinlock_swp2.kl`'s
worker (`swpa` acquire writing `1`, `ldr` test-and-test-and-set spin, plain
increment of the counter) with the release `stlr wzr, [x0]` replaced by the
release-only swap `swpl wzr, w2, [x0]` (writes `0`, the old value goes to
`w2`). `swpl` and not `swpal`: a lock release needs only release ordering; the
acquire half of `swpal` would make the swap claim (on `EnvGC`, an
acquire-release RMW always claims) the update slots of the lock message it
reads, adding an unknown resource to the thread after its release, for
nothing. The old value goes to `w2` (not `wzr`) so that the swap is a
returning RMW (`rmwLive`).

Static hypotheses of `ThreadRuleRX.ofSafelyEnvGRC` and
`noFaultRule_ofSafelyEnvGRC_struct`:
- `swplWorker_rmwLive`: `e.rmwLive` (both swaps return into `w2`);
- `swplWorker_phase1R`: `Phase1TreeR` (single-access trees; the release swap
  is a release-kind RMW that never fails), by `dirs_phase1R`;
- `swplWorker_noFault`: `DirsNoFault`, by `dirs_no_fault'`.

Phase-1 limits: single-access trees, read-side acquire only (the `swpa`
acquire is an RMW claim); the release is an RMW, which phase 1 covers only on
the claim-conditional environments (`EnvGC`/`EnvGTC`).
-/
import Kraken.Promising.SLR.EnvG.SafelyBridge
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.Promising.SLR.EnvG.A64LinkR
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.EnvG.SwplLock

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The SWP spinlock worker with a `swpl` release** of
`spinlock_swpl2.kl`/`spinlock_swpl3.kl` (verbatim `code` block: 11
instructions and 5 labels, 16 directives; the end of the text is `addrOf 16`). -/
def swplWorker : Program := parseAArch64("
worker:
    mov w3, #1
try:
    swpa w3, w2, [x0]
    cbz w2, cs
spin:
    ldr w2, [x0]
    cbnz w2, spin
    b try
cs:
    ldr w5, [x1]
    add w5, w5, #1
    str w5, [x1]
    swpl wzr, w2, [x0]
    b done
done:
")

/-- info: 16 -/
#guard_msgs in
#eval swplWorker.length

variable [layout : _root_.Layout]

theorem swplWorker_rmwLive : (layout swplWorker).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem swplWorker_phase1R [Executable.ValidLayout (layout swplWorker)] : Phase1TreeR Arch.armv8 (layout swplWorker) :=
  phase1TreeR_of_dirs (by dirs_phase1R swplWorker)

/-- A worker thread at its start, with lock address `l` and counter address
`c` (as `CasSmoke.StartState`). -/
structure StartState (l c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout swplWorker
  decls : s.decls = {}
  endPc : s.endPc = (layout swplWorker).addrOf swplWorker.length
  pc : s.st.2 = (layout swplWorker).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = l
  x1 : s.st.1.regs.X1.toBitVec = c
  dl : Mem.loadInt s.st.1.dmem l 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

theorem swplWorker_noFault : DirsNoFault (layout swplWorker) := by dirs_no_fault' swplWorker

end Kraken.Promising.SLR.EnvG.SwplLock
