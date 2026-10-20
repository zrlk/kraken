/-
**Part 3: the ticket lock worker and its
static checks** (on `EnvGTD`, `EnvG/TicketEnv.lean`).

The worker of `ticketlock2.kl` (Promising-ARM PLDI'19 §7 "TL"): take a
ticket with `LDADDA` on `next`, spin with `LDAR` on `owner` until it equals
the ticket, increment the counter (plain), release with `STLR` of
`ticket + 1` to `owner`.

Static hypotheses of `ThreadRuleRXGSXE.ofSafelyEnvGTD` and
`noFaultRule_ofSafelyEnvGTD_struct`:
- `tkWorker_rmwLive`: `e.rmwLive` (the `ldadda` returns into `w3`);
- `tkWorker_phase1`: `Phase1Tree` (single-access trees), by `dirs_phase1`;
- `tkWorker_noFault`: `DirsNoFault`, by `dirs_no_fault'`.
-/
import Kraken.Promising.SLR.EnvG.SafelyBridge
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.Promising.SLR.EnvG.TicketA64Link
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The ticket lock worker** of `ticketlock2.kl` (verbatim `code` block:
11 instructions and 3 labels, 14 directives; the end of the text is
`addrOf 14`). -/
def tkWorker : Program := parseAArch64("
worker:
  MOV W6,#1
  LDADDA W6,W3,[X0]
spin:
  LDAR W4,[X1]
  CMP W4,W3
  B.NE spin
  LDR W5,[X2]
  ADD W5,W5,#1
  STR W5,[X2]
  ADD W4,W3,#1
  STLR W4,[X1]
  B done
done:
")

/-- info: 14 -/
#guard_msgs in
#eval tkWorker.length

variable [layout : _root_.Layout]

theorem tkWorker_rmwLive : (layout tkWorker).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem tkWorker_phase1 [Executable.ValidLayout (layout tkWorker)] : Phase1Tree Arch.armv8 (layout tkWorker) :=
  phase1Tree_of_dirs (by dirs_phase1 tkWorker; all_goals decide)

theorem tkWorker_noFault : DirsNoFault (layout tkWorker) := by dirs_no_fault' tkWorker

/-- A worker thread at its start, with `next`, `owner` and counter addresses
`x`, `o`, `c` (as `SwplLock.StartState`). -/
structure StartState (x o c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout tkWorker
  decls : s.decls = {}
  endPc : s.endPc = (layout tkWorker).addrOf tkWorker.length
  pc : s.st.2 = (layout tkWorker).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = x
  x1 : s.st.1.regs.X1.toBitVec = o
  x2 : s.st.1.regs.X2.toBitVec = c
  dx : Mem.loadInt s.st.1.dmem x 4 = none
  dO : Mem.loadInt s.st.1.dmem o 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkWorker_phase1
