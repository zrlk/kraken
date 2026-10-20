/-
**Stage 3: x64 ticket-lock liveness with promises,
on the machine with semantic certification** (statements).

`TicketX64.TicketX64Live fuel` (`LiveX64Ticket.lean`) is stated over the
existing machine `succs`, which admits a step of a thread with promises only
when the executable search `certify` finds a certification within `fuel`
instructions. `certify.go`'s visited set ignores the remaining fuel, so the
search is incomplete and `succs` is not monotone in fuel (KNOWN_GAPS); the
existing `TicketX64Live fuel` is a statement about that search and stays open,
as the AArch64 `Ticket.TicketLive` does.

`TicketX64LiveSem fuel` is the same statement (same start configurations
`TkStartX`, same `TkWaitingX`/`TkDoneX`) over the machine of `LiveSem.lean`,
where certification is semantic (`CertOkN`: the thread can empty its promise
set alone within `fuel` instructions), under the semantic weak fairness
`WeakFairSem` and memory fairness `MemFair` (on x86 a modelling assumption:
store buffers drain in finite time; see `LiveTrace.lean`). It is a new,
distinct statement; nothing existing is changed. The x64 counterpart of
`TicketSem.TicketLiveSem`.
-/
import Kraken.Promising.LiveX64Ticket
import Kraken.Promising.LiveSem

namespace Kraken.Promising.Live.X64Sem

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.TicketX64 (TkStartX TkWaitingX TkDoneX)

variable [layout : _root_.Layout]

/-- **x64 ticket-lock (`ticketlock3.kl`) liveness on the machine with
semantic certification** (Stage 3, with promises): from every start
configuration, on every semantic `Arch.tso` trace (`TraceSem`) under semantic
weak fairness and memory fairness, every waiting thread is eventually done.

This is *not* the existing `TicketX64.TicketX64Live fuel`: that one is stated
over `succs`, whose certification search `certify` is incomplete, so it may
be false. Here a promise or an instruction step needs the thread to be
*certifiable within `fuel`* (`CertOkN`), the intended notion. -/
def TicketX64LiveSem (fuel : Nat) : Prop :=
  ∀ N states initMem, TkStartX N states initMem →
    LiveFromSem Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) TkWaitingX TkDoneX

end Kraken.Promising.Live.X64Sem
