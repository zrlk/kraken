/-
Part 4: **the threads of `msqueue3.kl` and their
static checks** (on `EnvGCAdj`).

`P0` runs the `enq` block, which is msqueue2's `enq2Prog`. `P1` runs the
`deq1` block, which is msqueue1's `deqProg`. `P2` runs the `deq2` block,
`deqBProg` below: `deqProg` with the labels `deq2a`, `deq2a_ne`, `ddone2`
(the `deq2:` label dropped; `ddone2:` is the end of the text), with
`x0 = head`, `x1 = tail`. Static hypotheses of the link: `deqBProg_rmwLive`,
`deqBProg_phase1F`, `deqBProg_noFault`.
-/
import Kraken.Promising.SLR.EnvG.MsQueueSmoke

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The second dequeuer** of `msqueue3.kl` (`x0 = head`, `x1 = tail`):
`deqProg` with its labels renamed; the data in `w10`. -/
def deqBProg : Program := parseAArch64("
deq2a:
    ldar x3, [x0]
    ldar x4, [x1]
    add x8, x3, #8
    ldar x5, [x8]
    cmp x3, x4
    b.ne deq2a_ne
    cbz x5, deq2a
    mov x6, x3
    casal x6, x5, [x1]
    b deq2a
deq2a_ne:
    cbz x5, deq2a
    ldr w7, [x5]
    mov x6, x3
    casal x6, x5, [x0]
    cmp x6, x3
    b.ne deq2a
    mov w10, w7
    b ddone2
ddone2:
")

/-- info: 21 -/
#guard_msgs in
#eval deqBProg.length

variable [layout : _root_.Layout]

theorem deqBProg_rmwLive : (layout deqBProg).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem deqBProg_phase1F [Executable.ValidLayout (layout deqBProg)] :
    Phase1TreeF (layout deqBProg) :=
  phase1TreeF_of_dirs (by dirs_phase1F deqBProg)

theorem deqBProg_noFault : DirsNoFault (layout deqBProg) := by dirs_no_fault' deqBProg

end Kraken.Promising.SLR.EnvG.MsQueue
