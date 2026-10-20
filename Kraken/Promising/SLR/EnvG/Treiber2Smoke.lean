/-
Part 5: **the worker of `treiber2_nodes.kl` and its
static checks** (on `EnvGCAdj`, the link `ThreadRuleRXF.ofSafelyEnvGFCAdj`).

`treiber2Worker` is the `worker` block of
`Kraken/Examples/LockFree/AArch64/treiber2_nodes.kl` (lower-case syntax; the
`worker:` label dropped, the text starts at `push:`; `done:` is the end of
the text). Both threads run it, thread `i` with `x0 = top`, `x1 = n(i+1)`.
Static hypotheses of the link:
- `treiber2Worker_rmwLive`: the `casal`s return into `x3`;
- `treiber2Worker_phase1F`: `Phase1TreeF` by `dirs_phase1F`;
- `treiber2Worker_noFault`: `DirsNoFault` by `dirs_no_fault'`.
-/
import Kraken.Promising.SLR.EnvG.A64RmwFailGhost
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The worker** of `treiber2_nodes.kl` (`x0 = top`, `x1` the node): push
the node (link it to the current `top`, publish it by `casal`, retry on
failure), then pop once (read `top`; empty: done; else read the link, swing
`top` by `casal`, retry on failure; the node in `x10`). -/
def treiber2Worker : Program := parseAArch64("
push:
    ldar x2, [x0]
    str x2, [x1, #8]
    mov x3, x2
    casal x3, x1, [x0]
    cmp x3, x2
    b.ne push
pop:
    ldar x2, [x0]
    cbz x2, done
    ldr x4, [x2, #8]
    mov x3, x2
    casal x3, x4, [x0]
    cmp x3, x2
    b.ne pop
    mov x10, x2
    b done
done:
")

/-- info: 18 -/
#guard_msgs in
#eval treiber2Worker.length

variable [layout : _root_.Layout]

theorem treiber2Worker_rmwLive : (layout treiber2Worker).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem treiber2Worker_phase1F [Executable.ValidLayout (layout treiber2Worker)] :
    Phase1TreeF (layout treiber2Worker) :=
  phase1TreeF_of_dirs (by dirs_phase1F treiber2Worker)

theorem treiber2Worker_noFault : DirsNoFault (layout treiber2Worker) := by dirs_no_fault' treiber2Worker

end Kraken.Promising.SLR.EnvG.Treiber2
