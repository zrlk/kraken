/-
**The AArch64 CAS spinlock on `EnvG`, the program and its static checks**
The worker of `spinlock_cas2.kl` (`casa` acquire, expected
`0` / new `1`; `ldr` test-and-test-and-set spin; plain increment of the
counter; `stlr wzr` release) as `casTtasWorker`, and the per-thread static
hypotheses of `ThreadRuleRX.ofSafelyEnvG` and of
`noFaultRule_ofSafelyEnvG_struct`:

- `casTtasWorker_rmwLive`: `e.rmwLive` (the `casa` returns into `w2`);
- `casTtasWorker_phase1`: `Phase1Tree` (every cell a deterministic single
  access; `casa` is an acquire RMW, not release-kind), by `dirs_phase1`;
- `casTtasWorker_noFault`: `DirsNoFault`, by `dirs_no_fault'`.

The worker is inside phase 1: single-access trees, read-side acquire only
(the `casa` acquire is an RMW claim, which the RMW rules support), and the
release is a store.
-/
import Kraken.Promising.SLR.EnvG.SafelyBridge
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The CAS spinlock worker** of `spinlock_cas2.kl`/`spinlock_cas3.kl`
(verbatim `code` block: 12 instructions and 5 labels, 17 directives;
the end of the text is `addrOf 17`). -/
def casTtasWorker : Program := parseAArch64("
worker:
    mov w3, #1
try:
    mov w2, #0
    casa w2, w3, [x0]
    cbz w2, cs
spin:
    ldr w2, [x0]
    cbnz w2, spin
    b try
cs:
    ldr w5, [x1]
    add w5, w5, #1
    str w5, [x1]
    stlr wzr, [x0]
    b done
done:
")

/-- info: 17 -/
#guard_msgs in
#eval casTtasWorker.length

theorem casTtasWorker_rmwLive' : casTtasWorker.rmwLive = true := by decide

variable [layout : _root_.Layout]

theorem casTtasWorker_rmwLive : (layout casTtasWorker).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem casTtasWorker_phase1 [Executable.ValidLayout (layout casTtasWorker)] :
    Phase1Tree Arch.armv8 (layout casTtasWorker) :=
  phase1Tree_of_dirs (by dirs_phase1 casTtasWorker; all_goals decide)

/-- A worker thread at its start, with lock address `l` and counter address
`c` (as `SwpPublic.StartState`): it runs the laid-out `casTtasWorker` from
its first directive to the end of the text, without declarations, with
`X0 = l`, `X1 = c`, and neither word in its private data memory. -/
structure StartState (l c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout casTtasWorker
  decls : s.decls = {}
  endPc : s.endPc = (layout casTtasWorker).addrOf casTtasWorker.length
  pc : s.st.2 = (layout casTtasWorker).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = l
  x1 : s.st.1.regs.X1.toBitVec = c
  dl : Mem.loadInt s.st.1.dmem l 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

theorem casTtasWorker_noFault : DirsNoFault (layout casTtasWorker) := by dirs_no_fault' casTtasWorker

end Kraken.Promising.SLR.EnvG.CasSmoke
