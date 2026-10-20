/-
**Part 1: the SWP spinlock of
`spinlock_swp2.kl`/`spinlock_swp3.kl` on `EnvGC` — the program and its static
checks.**

The worker is the existing `InvEnv.swpWorker` (`swpa` acquire writing `1`, `ldr`
test-and-test-and-set spin, plain increment of the counter, `stlr wzr`
release), whose public theorem `SwpPublic.swp_counter_public` is on the
pre-EnvG cell route. This proof puts it on the claim-conditional environment
`EnvGC` of the `swpl` lock (`EnvG/SwplLock*.lean`): the two programs differ
only in the release (`stlr wzr, [x0]` here, `swpl wzr, w2, [x0]` there), and a
release store is inside phase 1 (releases are stores). The acquire is the
`swpa`'s claim (as for `swpl`), the release the CAS lock's `stlr`.

Static hypotheses of `ThreadRuleRX.ofSafelyEnvGRC` and
`noFaultRule_ofSafelyEnvGRC_struct`:
- `swpWorker_rmwLive`: `e.rmwLive` (the `swpa` returns into `w2`);
- `swpWorker_phase1R`: `Phase1TreeR` (single-access trees; no release-kind
  RMW), by `dirs_phase1R`;
- `swpWorker_noFault`: `DirsNoFault`, by `dirs_no_fault'`.

Phase-1 limits: single-access trees, read-side acquire only (the `swpa`
acquire is an RMW claim), releases are stores.
-/
import Kraken.Promising.SLR.EnvG.SafelyBridge
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.Promising.SLR.EnvG.A64LinkR
import Kraken.AArch64.Examples.InvEnv

namespace Kraken.Promising.SLR.EnvG.SwpEnvG

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Examples.InvEnv (swpWorker)

/-- info: 16 -/
#guard_msgs in
#eval swpWorker.length

variable [layout : _root_.Layout]

theorem swpWorker_rmwLive : (layout swpWorker).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem swpWorker_phase1R [Executable.ValidLayout (layout swpWorker)] : Phase1TreeR Arch.armv8 (layout swpWorker) :=
  phase1TreeR_of_dirs (by dirs_phase1R swpWorker)

theorem swpWorker_noFault : DirsNoFault (layout swpWorker) := by dirs_no_fault' swpWorker

end Kraken.Promising.SLR.EnvG.SwpEnvG
