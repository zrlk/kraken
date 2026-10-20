/-
**Stage 4 (repeated acquisition): the repeated-acquire ticket lock and
its liveness statements** (A64, `ldadda`; `ticketlock_loop2.kl`,
`ticketlock_loop3.kl`).

Every lock liveness theorem before this one is *one-shot*: each thread
acquires once (`Ticket.TkDone`: past the spin loop). `tkLoopWorker` runs the
worker of `ticketlock2.kl` for `k` rounds; the round counter is `X7`
(remaining rounds), tested at the loop head with `CBZ`, so `k = 0` runs no
round. The start states (`TkLoopStart k N x o c`) are those of
`Ticket.TkStart` with `X7 = k` in every worker and `N * k + 1 < 2 ^ 32`
(the tickets `0 … N * k - 1` never wrap).

The *round* of a worker is `k - X7` (rounds completed, counted at the
`SUB`). Proposed predicates:

- `TkLoopWaiting k r`: in the spin loop of round `r` (positions 6–8 with
  `X7 + r = k`);
- `TkLoopDone k r`: has acquired in round `r`: in round `r` past its spin
  loop (positions 9–14), or in a later round (`X7 + r < k`, which includes
  position 15 after the `SUB`, every later round, and the end);
- `TkLoopFinished`: at the end of the text (all rounds completed).

Statements, all on the **semantic machine** (`TraceSem`, `CertOkN`), under
`WeakFairSem ∧ MemFair`, for every `fuel`:

- `TicketLoopStarveSem fuel` (proved): starvation-freedom **per round**:
  every thread waiting in round `r` eventually acquires in round `r`;
- `TicketLoopFinishSem fuel` (proved): every thread eventually completes
  all `k` rounds;
- `TicketLoopTermSem fuel` (proved): every trace reaches a final
  configuration (`Term.TermFromSem`);
- `TicketLoopLiveSem fuel` (proved): the conjunction of the first two.

The one-shot proof (`LiveTicketSem`) does not carry over to `k ≥ 2`: a
waiting thread may need fresh writes to certify, and a thread can be disabled
forever (KNOWN_GAPS, "Liveness: repeated acquisition (LOOP)"). The proofs
(`LiveTicketLoopSem.lean`, at every valid layout: `ticket_loop_*_sem`) argue
instead that someone must step, using the trace invariant with promises
(`LiveTicketLoopInvP.lean`) and F3 for the holder of the final `owner` value.

**The promise-free fragment** (proved: `LiveTicketLoopPF.lean`): the same
statements on semantic traces with no promise step (`PromiseFreeSem`),
`TicketLoopStarvePFSem`, `TicketLoopFinishPFSem`, `TicketLoopLivePFSem`.
-/
import Kraken.Promising.LiveTerm
import Kraken.Promising.LiveTicketInv
import Kraken.AArch64.Parser

namespace Kraken.Promising.Live.TicketLoop

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.TicketInv (wn L4)

/-- **The repeated-acquire ticket lock worker** of `ticketlock_loop2.kl`
(verbatim `code` block: 14 instructions and 3 labels, 17 directives; the end
of the text is `addrOf 17`).

```
 0 worker:                  9   LDR W5,[X2]
 1   MOV W6,#1             10   ADD W5,W5,#1
 2 round:                  11   STR W5,[X2]
 3   CBZ W7,done           12   ADD W4,W3,#1
 4   LDADDA W6,W3,[X0]     13   STLR W4,[X1]
 5 spin:                   14   SUB W7,W7,#1
 6   LDAR W4,[X1]          15   B round
 7   CMP W4,W3             16 done:
 8   B.NE spin
```
-/
def tkLoopWorker : Program := parseAArch64("
worker:
  MOV W6,#1
round:
  CBZ W7,done
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
  SUB W7,W7,#1
  B round
done:
")

/-- info: 17 -/
#guard_msgs in
#eval tkLoopWorker.length

variable [layout : _root_.Layout]

set_option hygiene false in
local notation "pcA" => (layout tkLoopWorker).addrOf

/-- A worker at its start, with `next`, `owner` and counter addresses `x`,
`o`, `c` and `k` rounds to run (`X7`). -/
structure LoopStartState (k : Nat) (x o c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout tkLoopWorker
  decls : s.decls = {}
  endPc : s.endPc = pcA tkLoopWorker.length
  pc : s.st.2 = pcA 0
  x0 : s.st.1.regs.X0.toBitVec = x
  x1 : s.st.1.regs.X1.toBitVec = o
  x2 : s.st.1.regs.X2.toBitVec = c
  x7 : wn s.st.1.regs.X7 = k
  dx : Mem.loadInt s.st.1.dmem x 4 = none
  dO : Mem.loadInt s.st.1.dmem o 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

/-- **The start configurations**: `N` workers running `k` rounds, pairwise
disjoint 4-byte words `x` (`next`), `o` (`owner`), `c` (counter),
`N * k + 1 < 2 ^ 32`, the three words at `0`. -/
structure TkLoopStart (k N : Nat) (x o c : BitVec 64) (states : List isa.State)
    (initMem : List (Loc × Val)) : Prop where
  hxo : Decls.overlaps x 4 o 4 = false
  hxc : Decls.overlaps x 4 c 4 = false
  hoc : Decls.overlaps o 4 c 4 = false
  hNk32 : N * k + 1 < 2 ^ 32
  hst : ∀ s ∈ states, LoopStartState k x o c s
  hN : states.length = N
  hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0
  hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0
  hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0

/-- The spin loop's addresses: `LDAR`, `CMP`, `B.NE` (directives 6–8; the
label `spin`, directive 5, is at the address of directive 6). -/
def tkLoopSpinPcs : List Int64 := [6, 7, 8].map (layout tkLoopWorker).addrOf

/-- The critical section and release of a round, before the `SUB`
(directives 9–14). -/
def tkLoopCsPcs : List Int64 := [9, 10, 11, 12, 13, 14].map (layout tkLoopWorker).addrOf

/-- Thread `tid` waits in round `r`: it spins (holding its round-`r` ticket)
and has completed `r` of its `k` rounds. -/
def TkLoopWaiting (k r tid : Nat) (c : Config isa) : Prop :=
  ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ tkLoopSpinPcs ∧ wn t.st.st.1.regs.X7 + r = k

/-- Thread `tid` has acquired the lock in round `r`: it is in round `r` past
its spin loop, or in a later round (or finished). -/
def TkLoopDone (k r tid : Nat) (c : Config isa) : Prop :=
  ∃ t, c.threads[tid]? = some t ∧
    ((t.st.st.2 ∈ tkLoopCsPcs ∧ wn t.st.st.1.regs.X7 + r = k) ∨ wn t.st.st.1.regs.X7 + r < k)

/-- Thread `tid` exists. -/
def TkLoopPresent (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t

/-- Thread `tid` has completed all its rounds: it is at the end of the text. -/
def TkLoopFinished (tid : Nat) (c : Config isa) : Prop :=
  ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 = pcA tkLoopWorker.length

/-- The hypothesis of the statements: semantic weak fairness and memory
fairness. -/
def LoopFair (fuel : Nat) (cfg : Nat → Config isa) : Prop :=
  WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg

/-- **Starvation-freedom per round** (semantic machine; proved at valid layouts by
`TicketLoopSem.ticket_loop_starve_sem`): from every start
configuration, on every semantic trace under weak and memory fairness, every
thread waiting in round `r` eventually acquires in round `r`. -/
def TicketLoopStarveSem (fuel : Nat) : Prop :=
  ∀ k N x o c states initMem, TkLoopStart k N x o c states initMem → ∀ r,
    LiveFromSem Arch.armv8 fuel (Config.init states initMem) (LoopFair fuel) (TkLoopWaiting k r) (TkLoopDone k r)

/-- **Every thread completes all `k` rounds** (semantic machine, weak and
memory fairness; proved at valid layouts by
`TicketLoopSem.ticket_loop_finish_sem`). -/
def TicketLoopFinishSem (fuel : Nat) : Prop :=
  ∀ k N x o c states initMem, TkLoopStart k N x o c states initMem →
    LiveFromSem Arch.armv8 fuel (Config.init states initMem) (LoopFair fuel) TkLoopPresent TkLoopFinished

/-- **Termination** (semantic machine, weak and memory fairness; proved at
valid layouts by `TicketLoopSem.ticket_loop_term_sem`):
every trace reaches a final configuration. -/
def TicketLoopTermSem (fuel : Nat) : Prop :=
  ∀ k N x o c states initMem, TkLoopStart k N x o c states initMem →
    Term.TermFromSem Arch.armv8 fuel (Config.init states initMem) (LoopFair fuel)

/-- **The repeated-acquire ticket-lock liveness statement** (semantic machine;
proved at valid layouts by `TicketLoopSem.ticket_loop_live_sem`, and at
`TicketLoopPF.tkLoopLayout` by `TicketLoopSem.ticket_loop_live_sem_concrete`): starvation-freedom per round, and every thread completes all its
rounds. -/
def TicketLoopLiveSem (fuel : Nat) : Prop :=
  TicketLoopStarveSem fuel ∧ TicketLoopFinishSem fuel

/-! ## The promise-free fragment -/

/-- **No promise step** along a sequence of configurations of the semantic
machine (`PromSem`; the semantic counterpart of `PromiseFree`). -/
def PromiseFreeSem {I : ISA} (A : Arch) (fuel : Nat) (cfg : Nat → Config I) : Prop :=
  ∀ i tid, ¬ PromSem A fuel tid (cfg i) (cfg (i + 1))

/-- The hypothesis of the promise-free statements: `LoopFair` and no promise
step. -/
def LoopFairPF (fuel : Nat) (cfg : Nat → Config isa) : Prop :=
  LoopFair fuel cfg ∧ PromiseFreeSem Arch.armv8 fuel cfg

/-- **Starvation-freedom per round, promise-free fragment** (semantic machine,
traces with no promise step, weak and memory fairness). Proved at valid
layouts: `TicketLoopPF.ticket_loop_starve_pf`. -/
def TicketLoopStarvePFSem (fuel : Nat) : Prop :=
  ∀ k N x o c states initMem, TkLoopStart k N x o c states initMem → ∀ r,
    LiveFromSem Arch.armv8 fuel (Config.init states initMem) (LoopFairPF fuel) (TkLoopWaiting k r)
      (TkLoopDone k r)

/-- **Every thread completes all `k` rounds, promise-free fragment**
(semantic machine). Proved at valid layouts:
`TicketLoopPF.ticket_loop_finish_pf`. -/
def TicketLoopFinishPFSem (fuel : Nat) : Prop :=
  ∀ k N x o c states initMem, TkLoopStart k N x o c states initMem →
    LiveFromSem Arch.armv8 fuel (Config.init states initMem) (LoopFairPF fuel) TkLoopPresent TkLoopFinished

/-- **The repeated-acquire liveness statement, promise-free fragment**
(semantic machine). Proved at valid layouts: `TicketLoopPF.ticket_loop_live_pf`. -/
def TicketLoopLivePFSem (fuel : Nat) : Prop :=
  TicketLoopStarvePFSem fuel ∧ TicketLoopFinishPFSem fuel

end Kraken.Promising.Live.TicketLoop
