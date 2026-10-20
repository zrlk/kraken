/-
Part 7: **the two threads of `treiber_pp.kl` and their
static checks** (on `EnvGC`, the `FC` link `ThreadRuleRXF.ofSafelyEnvGFC`).

`treiberPusher` and `treiberPopper` are the `pusher` and `popper` blocks of
`Kraken/Examples/LockFree/AArch64/treiber_pp.kl` (lower-case syntax, the
`.kl`'s shared `code` block split per thread; the pusher's `pdone: NOP` is
the end of its text, the popper's `qdone:` the end of its). Static hypotheses
of `ThreadRuleRXF.ofSafelyEnvGFC` / `noFaultRuleF_ofSafelyEnvGFC_struct`:
- `*_rmwLive`: the `casal`s return into `x3`;
- `*_phase1F`: `Phase1TreeF` by `dirs_phase1F` (single-access trees; the
  `casal`s are release-kind RMWs that may fail);
- `*_noFault`: `DirsNoFault` by `dirs_no_fault'`.
-/
import Kraken.Promising.SLR.EnvG.A64RmwFailGhost
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.EnvG.Treiber

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The pusher** of `treiber_pp.kl` (`x0 = top`, `x1 = n1`, `w9 = 1`): write
the data word, link the node to the current `top`, publish it by `casal`,
retry on failure. -/
def treiberPusher : Program := parseAArch64("
pusher:
    str w9, [x1]
push:
    ldar x2, [x0]
    str x2, [x1, #8]
    mov x3, x2
    casal x3, x1, [x0]
    cmp x3, x2
    b.ne push
    b pdone
pdone:
")

/-- **The popper** of `treiber_pp.kl` (`x0 = top`): read `top` until
non-empty, read the link, swing `top` by `casal`, retry on failure; then the
node in `x10`, its data word in `w11`. -/
def treiberPopper : Program := parseAArch64("
popper:
    ldar x2, [x0]
    cbz x2, popper
    ldr x4, [x2, #8]
    mov x3, x2
    casal x3, x4, [x0]
    cmp x3, x2
    b.ne popper
    mov x10, x2
    ldr w11, [x2]
    b qdone
qdone:
")

/-- info: 11 -/
#guard_msgs in
#eval treiberPusher.length

/-- info: 12 -/
#guard_msgs in
#eval treiberPopper.length

variable [layout : _root_.Layout]

theorem treiberPusher_rmwLive : (layout treiberPusher).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem treiberPopper_rmwLive : (layout treiberPopper).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem treiberPusher_phase1F [Executable.ValidLayout (layout treiberPusher)] :
    Phase1TreeF (layout treiberPusher) :=
  phase1TreeF_of_dirs (by dirs_phase1F treiberPusher)

theorem treiberPopper_phase1F [Executable.ValidLayout (layout treiberPopper)] :
    Phase1TreeF (layout treiberPopper) :=
  phase1TreeF_of_dirs (by dirs_phase1F treiberPopper)

theorem treiberPusher_noFault : DirsNoFault (layout treiberPusher) := by dirs_no_fault' treiberPusher

theorem treiberPopper_noFault : DirsNoFault (layout treiberPopper) := by dirs_no_fault' treiberPopper

end Kraken.Promising.SLR.EnvG.Treiber
