/-
Msqueue2 part 3: **the two threads of `msqueue2.kl`
and their static checks** (on `EnvGCAdj`).

`enq2Prog` is the `enq` block of `Kraken/Examples/LockFree/AArch64/msqueue2.kl`
(lower-case syntax; the `enq:` label dropped, the text starts at `enq1:`;
`pdone:` is the end of the text), run by `P0` with `x1 = tail`, `x12 = n1`,
`x13 = n2`. `deq2Prog` is the `deq1` block (the `deq1:` label dropped;
`ddone1:` is the end of the text), run by `P1` with `x0 = head`,
`x1 = tail`. Static hypotheses of the link: `*_rmwLive`, `*_phase1F`,
`*_noFault`.
-/
import Kraken.Promising.SLR.EnvG.MsQueueSmoke

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The enqueuer** of `msqueue2.kl`: msqueue1's enqueue of `n1` (`x12`),
then the same of `n2` (`x13`, data `2`). -/
def enq2Prog : Program := parseAArch64("
enq1:
    mov x2, x12
    mov w9, #1
    str w9, [x2]
enq1_loop:
    ldar x3, [x1]
    add x8, x3, #8
    ldar x4, [x8]
    cbnz x4, enq1_fix
    mov x5, #0
    casal x5, x2, [x8]
    cbnz x5, enq1_loop
    mov x5, x3
    casal x5, x2, [x1]
    b enq1_end
enq1_fix:
    mov x5, x3
    casal x5, x4, [x1]
    b enq1_loop
enq1_end:
enq2:
    mov x2, x13
    mov w9, #2
    str w9, [x2]
enq2_loop:
    ldar x3, [x1]
    add x8, x3, #8
    ldar x4, [x8]
    cbnz x4, enq2_fix
    mov x5, #0
    casal x5, x2, [x8]
    cbnz x5, enq2_loop
    mov x5, x3
    casal x5, x2, [x1]
    b enq2_end
enq2_fix:
    mov x5, x3
    casal x5, x4, [x1]
    b enq2_loop
enq2_end:
    b pdone
pdone:
")

/-- info: 42 -/
#guard_msgs in
#eval enq2Prog.length

/-- **The dequeuer** of `msqueue2.kl`: msqueue1's dequeue into `w10`, then
the same into `w11`. -/
def deq2Prog : Program := parseAArch64("
deq1a:
    ldar x3, [x0]
    ldar x4, [x1]
    add x8, x3, #8
    ldar x5, [x8]
    cmp x3, x4
    b.ne deq1a_ne
    cbz x5, deq1a
    mov x6, x3
    casal x6, x5, [x1]
    b deq1a
deq1a_ne:
    cbz x5, deq1a
    ldr w7, [x5]
    mov x6, x3
    casal x6, x5, [x0]
    cmp x6, x3
    b.ne deq1a
    mov w10, w7
deq1b:
    ldar x3, [x0]
    ldar x4, [x1]
    add x8, x3, #8
    ldar x5, [x8]
    cmp x3, x4
    b.ne deq1b_ne
    cbz x5, deq1b
    mov x6, x3
    casal x6, x5, [x1]
    b deq1b
deq1b_ne:
    cbz x5, deq1b
    ldr w7, [x5]
    mov x6, x3
    casal x6, x5, [x0]
    cmp x6, x3
    b.ne deq1b
    mov w11, w7
    b ddone1
ddone1:
")

/-- info: 40 -/
#guard_msgs in
#eval deq2Prog.length

variable [layout : _root_.Layout]

theorem enq2Prog_rmwLive : (layout enq2Prog).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem enq2Prog_phase1F [Executable.ValidLayout (layout enq2Prog)] : Phase1TreeF (layout enq2Prog) :=
  phase1TreeF_of_dirs (by dirs_phase1F enq2Prog)

theorem enq2Prog_noFault : DirsNoFault (layout enq2Prog) := by dirs_no_fault' enq2Prog

theorem deq2Prog_rmwLive : (layout deq2Prog).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem deq2Prog_phase1F [Executable.ValidLayout (layout deq2Prog)] : Phase1TreeF (layout deq2Prog) :=
  phase1TreeF_of_dirs (by dirs_phase1F deq2Prog)

theorem deq2Prog_noFault : DirsNoFault (layout deq2Prog) := by dirs_no_fault' deq2Prog

end Kraken.Promising.SLR.EnvG.MsQueue
