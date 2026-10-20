/-
Part 3: **the two threads of `msqueue1.kl` and their
static checks** (on `EnvGCAdj`, the link `ThreadRuleRXF.ofSafelyEnvGFCAdj`).

`enqProg` is the `enq` block of `Kraken/Examples/LockFree/AArch64/msqueue1.kl`
(lower-case syntax; the `enq:` label dropped, the text starts at `enq1:`;
`pdone:` is the end of the text), run by `P0` with `x1 = tail`, `x12 = n1`. `deqProg` is the
`deq1` block (the `deq1:` label dropped; `ddone1:` is the end of the text),
run by `P1` with `x0 = head`, `x1 = tail`. Static hypotheses of the link:
`*_rmwLive` (every `casal` returns into a register), `*_phase1F`
(`Phase1TreeF` by `dirs_phase1F`), `*_noFault` (`DirsNoFault`).
-/
import Kraken.Promising.SLR.EnvG.A64RmwFailGhost
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The enqueuer** of `msqueue1.kl` (`x1 = tail`, `x12 = n1`): write the
data `1` to `[n1]`, then loop: read `tail` and `tail.next`; a non-zero
`next` is helped (swing `tail` to it, retry); else link the node by
`casal [tail+8]: 0 → n1` (retry on failure) and swing `tail` to it. -/
def enqProg : Program := parseAArch64("
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
    b pdone
pdone:
")

/-- info: 22 -/
#guard_msgs in
#eval enqProg.length

/-- **The dequeuer** of `msqueue1.kl` (`x0 = head`, `x1 = tail`): read
`head`, `tail`, `head.next`; `head = tail`: empty (retry) or help swing
`tail`; else read the data of `next` and swing `head` to `next` (retry on
failure); the data in `w10`. -/
def deqProg : Program := parseAArch64("
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
    b ddone1
ddone1:
")

/-- info: 21 -/
#guard_msgs in
#eval deqProg.length

variable [layout : _root_.Layout]

theorem enqProg_rmwLive : (layout enqProg).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem enqProg_phase1F [Executable.ValidLayout (layout enqProg)] :
    Phase1TreeF (layout enqProg) :=
  phase1TreeF_of_dirs (by dirs_phase1F enqProg)

theorem enqProg_noFault : DirsNoFault (layout enqProg) := by dirs_no_fault' enqProg

theorem deqProg_rmwLive : (layout deqProg).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem deqProg_phase1F [Executable.ValidLayout (layout deqProg)] :
    Phase1TreeF (layout deqProg) :=
  phase1TreeF_of_dirs (by dirs_phase1F deqProg)

theorem deqProg_noFault : DirsNoFault (layout deqProg) := by dirs_no_fault' deqProg

end Kraken.Promising.SLR.EnvG.MsQueue
