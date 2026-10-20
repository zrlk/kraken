/-
**Stage 3 liveness: the ticket lock's liveness
statements** for the A64 `ldadda` ticket lock worker `tkWorker`
(`ticketlock2.kl`; the program of `TicketLock.ticket_counter_envG`).

Same start states as `ticket_counter_envG` (`TkStart`: `N` workers at
`StartState x o c`, pairwise disjoint 4-byte words, `N + 1 < 2 ^ 32`, the
three words at `0`). A thread is *waiting* (`TkWaiting`) when it holds its
ticket and spins (`LDAR`/`CMP`/`B.NE`), and *done* (`TkDone`) once it is
past the spin loop (in or after its critical section).

- `TicketLive`: **the official Stage 3 statement**:
  on every stuttering trace from a start configuration that is weakly fair
  (`WeakFair`, promise steps count as steps) and memory-fair (`MemFair`),
  every waiting thread is eventually done. **Open** (with promises) for
  `fuel ≥ 1`. Proved at `fuel = 0`: `TicketZero.ticket_live_zero`
  (`LiveTicketZero.lean`). The machine's `certify` is incomplete (its visited
  set ignores the remaining fuel), so for `fuel ≥ 1` this statement may be
  false. The same statement with semantic certification (`CertOkN`),
  `TicketSem.TicketLiveSem`, is proved for every fuel under
  `[ValidLayout]`: `TicketSem.ticket_live_sem` (`LiveTicketSem.lean`).
  Weak fairness alone is refuted by `TicketCexG.ticketLiveWF_false`.
- `TicketLivePF`: the promise-free fragment (traces with no promise step).
  **Proved at valid layouts**: `Live.TicketPF.ticket_live_pf`
  (`[ValidLayout (layout tkWorker)]`, `LiveTicketPF.lean`; the promise-free liveness proofs). At an
  invalid layout it is false (see that module's docstring and KNOWN_GAPS).
  `ticketLivePF_of_live`.
- `TicketLiveWF`: weak fairness alone, the statement first proposed for
  Stage 3. **False in substance**: on `ticketlock2.kl`'s runner
  configuration (`N = 2`, typed declarations) a weakly fair, promise-free
  trace starves a thread (`TicketCex.ticket_not_live_weakFair`,
  `LiveTicketCex.lean`); the literal refutation at a `decls = {}`
  `StartState` configuration is not yet formalised.
-/
import Kraken.Promising.SLR.EnvG.TicketLockSmoke
import Kraken.Promising.LiveRank

namespace Kraken.Promising.Live.Ticket

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker StartState)

variable [layout : _root_.Layout]

/-- The spin loop's addresses: `LDAR`, `CMP`, `B.NE` (directives 4–6; the
label `spin`, directive 3, is at the address of directive 4). -/
def tkSpinPcs : List Int64 := [4, 5, 6].map (layout tkWorker).addrOf

/-- The addresses before the critical section (directives 0–6). -/
def tkPrePcs : List Int64 := (List.range 7).map (layout tkWorker).addrOf

/-- Thread `tid` holds its ticket and spins. -/
def TkWaiting (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ tkSpinPcs

/-- Thread `tid` is past its spin loop: in or after its critical section. -/
def TkDone (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ tkPrePcs

/-- **The start configurations of `ticket_counter_envG`**: `N` workers,
pairwise disjoint 4-byte words `x` (`next`), `o` (`owner`), `c` (counter),
`N + 1 < 2 ^ 32`, the three words at `0`. -/
structure TkStart (N : Nat) (x o c : BitVec 64) (states : List isa.State) (initMem : List (Loc × Val)) :
    Prop where
  hxo : Decls.overlaps x 4 o 4 = false
  hxc : Decls.overlaps x 4 c 4 = false
  hoc : Decls.overlaps o 4 c 4 = false
  hN32 : N + 1 < 2 ^ 32
  hst : ∀ s ∈ states, StartState x o c s
  hN : states.length = N
  hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0
  hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0
  hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0

/-- Ticket-lock liveness under the trace hypothesis `Fair`: from every start
configuration, on every stuttering trace satisfying `Fair`, every waiting
thread is eventually done. -/
def TicketLiveUnder (fuel : Nat) (Fair : (Nat → Config isa) → Prop) : Prop :=
  ∀ N x o c states initMem, TkStart N x o c states initMem →
    LiveFrom Arch.armv8 fuel (Config.init states initMem) Fair TkWaiting TkDone

/-- **The official Stage 3 statement for the ticket lock** (open): weak
scheduler fairness and memory fairness. -/
def TicketLive (fuel : Nat) : Prop :=
  TicketLiveUnder fuel fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg

/-- **The promise-free fragment**: `TicketLive` on traces with no promise
step. Proved at valid layouts: `Live.TicketPF.ticket_live_pf`. -/
def TicketLivePF (fuel : Nat) : Prop :=
  TicketLiveUnder fuel fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg

/-- **Weak scheduler fairness alone**: false (`TicketCex.ticket_not_live_weakFair`;
literally `¬ TicketLiveWF` at a `decls = {}` start: `ticketLiveWF_false`,
`LiveTicketCexG.lean`). -/
def TicketLiveWF (fuel : Nat) : Prop :=
  TicketLiveUnder fuel fun cfg => WeakFair Arch.armv8 fuel cfg

/-- A stronger hypothesis gives a weaker statement. -/
theorem TicketLiveUnder.mono {fuel : Nat} {F F' : (Nat → Config isa) → Prop} (h : TicketLiveUnder fuel F)
    (hF : ∀ cfg, F' cfg → F cfg) : TicketLiveUnder fuel F' :=
  fun N x o c states initMem hs tr h0 hf => h N x o c states initMem hs tr h0 (hF _ hf)

theorem ticketLivePF_of_live {fuel : Nat} (h : TicketLive fuel) : TicketLivePF fuel :=
  h.mono fun _ hf => ⟨hf.1, hf.2.1⟩

theorem ticketLive_of_wf {fuel : Nat} (h : TicketLiveWF fuel) : TicketLive fuel :=
  h.mono fun _ hf => hf.1

end Kraken.Promising.Live.Ticket
