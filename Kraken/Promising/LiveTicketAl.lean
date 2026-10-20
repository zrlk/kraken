/-
**Stage 3: the liveness statements for the AArch64
`ldaddal` ticket lock worker `tkWorkerAl`** (`ticketlock_al2/3.kl`; the
program of `TicketLock.ticket_al_counter_envG`, `EnvG/TicketAlPublic.lean`).

`tkWorkerAl` is `tkWorker` (`ticketlock2.kl`) with exactly one cell changed:
the ticket is taken by `LDADDAL` (acquire-release RMW) instead of `LDADDA`.
The statements are those of `LiveTicket.lean` at `tkWorkerAl`, with the same
shapes and fairness:

- `TkStartAl`: the start configurations of `ticket_al_counter_envG` (`N`
  workers at `StartStateAl x o c`, pairwise disjoint 4-byte words,
  `N + 1 < 2 ^ 32`, the three words at `0`). `TkWaitingAl`: the thread holds
  its ticket and spins (positions 4–6, `LDAR`/`CMP`/`B.NE`); `TkDoneAl`: it
  is past the spin loop.
- `TicketAlLive` (executable machine `succs`/`TraceS`, `WeakFair ∧
  MemFair`): the official form. **Open** for `fuel ≥ 1`, for the same reason
  as `Ticket.TicketLive` (`certify` is incomplete; see `LiveSem.lean`). The
  same statement on the semantic machine (`CertOkN`/`TraceSem`, `WeakFairSem
  ∧ MemFair`), `TicketAlSem.TicketAlLiveSem`, is proved for every fuel under
  `[ValidLayout]`: `TicketAlSem.ticket_al_live_sem` (`LiveTicketAlSem.lean`).
- `TicketAlLivePF` (executable machine, `WeakFair ∧ MemFair ∧ PromiseFree`):
  **proved at valid layouts**, `TicketAlPF.ticket_al_live_pf`
  (`LiveTicketAlPF.lean`).
- `TicketAlLiveWF` (executable machine, weak fairness alone): **false**,
  `TicketAlCexG.ticketAlLiveWF_false` (`LiveTicketAlCexG.lean`).

The proofs are the `ldadda` ones re-elaborated at `tkWorkerAl`
(`#ticket_al_clone`, `LiveTicketAlClone.lean`): every step lemma of the
`ldadda` chain is generic in the RMW's kind (`spec_rmw`, `spec_rmw_p`,
`replay_rmw`, `en_rmw`, `spec_rmw_len`), so the release half of `LDADDAL`
changes nothing in them.
-/
import Kraken.Promising.SLR.EnvG.TicketAlSmoke
import Kraken.Promising.LiveRank

namespace Kraken.Promising.Live.TicketAl

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorkerAl StartStateAl)

variable [layout : _root_.Layout]

/-- The spin loop's addresses: `LDAR`, `CMP`, `B.NE` (directives 4–6; the
label `spin`, directive 3, is at the address of directive 4). -/
def tkSpinPcs : List Int64 := [4, 5, 6].map (layout tkWorkerAl).addrOf

/-- The addresses before the critical section (directives 0–6). -/
def tkPrePcs : List Int64 := (List.range 7).map (layout tkWorkerAl).addrOf

/-- Thread `tid` holds its ticket and spins. -/
def TkWaitingAl (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ tkSpinPcs

/-- Thread `tid` is past its spin loop: in or after its critical section. -/
def TkDoneAl (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ tkPrePcs

/-- **The start configurations of `ticket_al_counter_envG`**: `N` workers
`tkWorkerAl`, pairwise disjoint 4-byte words `x` (`next`), `o` (`owner`),
`c` (counter), `N + 1 < 2 ^ 32`, the three words at `0`. -/
structure TkStartAl (N : Nat) (x o c : BitVec 64) (states : List isa.State) (initMem : List (Loc × Val)) :
    Prop where
  hxo : Decls.overlaps x 4 o 4 = false
  hxc : Decls.overlaps x 4 c 4 = false
  hoc : Decls.overlaps o 4 c 4 = false
  hN32 : N + 1 < 2 ^ 32
  hst : ∀ s ∈ states, StartStateAl x o c s
  hN : states.length = N
  hX0 : (Config.init states initMem).mem.initVal ⟨x, 4⟩ = 0
  hO0 : (Config.init states initMem).mem.initVal ⟨o, 4⟩ = 0
  hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0

/-- `ldaddal` ticket-lock liveness under the trace hypothesis `Fair`
(executable machine, `TraceS`): from every start configuration, on every
stuttering trace satisfying `Fair`, every waiting thread is eventually done. -/
def TicketAlLiveUnder (fuel : Nat) (Fair : (Nat → Config isa) → Prop) : Prop :=
  ∀ N x o c states initMem, TkStartAl N x o c states initMem →
    LiveFrom Arch.armv8 fuel (Config.init states initMem) Fair TkWaitingAl TkDoneAl

/-- **The official Stage 3 statement for the `ldaddal` ticket lock** (open;
executable machine): weak scheduler fairness and memory fairness. -/
def TicketAlLive (fuel : Nat) : Prop :=
  TicketAlLiveUnder fuel fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg

/-- **The promise-free fragment** (executable machine): `TicketAlLive` on
traces with no promise step. Proved at valid layouts:
`TicketAlPF.ticket_al_live_pf`. -/
def TicketAlLivePF (fuel : Nat) : Prop :=
  TicketAlLiveUnder fuel fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg

/-- **Weak scheduler fairness alone** (executable machine): false,
`TicketAlCexG.ticketAlLiveWF_false`. -/
def TicketAlLiveWF (fuel : Nat) : Prop :=
  TicketAlLiveUnder fuel fun cfg => WeakFair Arch.armv8 fuel cfg

/-- A stronger hypothesis gives a weaker statement. -/
theorem TicketAlLiveUnder.mono {fuel : Nat} {F F' : (Nat → Config isa) → Prop} (h : TicketAlLiveUnder fuel F)
    (hF : ∀ cfg, F' cfg → F cfg) : TicketAlLiveUnder fuel F' :=
  fun N x o c states initMem hs tr h0 hf => h N x o c states initMem hs tr h0 (hF _ hf)

theorem ticketAlLivePF_of_live {fuel : Nat} (h : TicketAlLive fuel) : TicketAlLivePF fuel :=
  h.mono fun _ hf => ⟨hf.1, hf.2.1⟩

theorem ticketAlLive_of_wf {fuel : Nat} (h : TicketAlLiveWF fuel) : TicketAlLive fuel :=
  h.mono fun _ hf => hf.1

end Kraken.Promising.Live.TicketAl
