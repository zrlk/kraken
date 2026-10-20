/-
**Stage 3: spinlock deadlock-freedom statements
on the machine with semantic certification** (`LiveSem.lean`).

`Spin.CasSpinLive fuel` (`LiveSpin.lean`) is stated over the existing machine
`succs`, whose certification search `certify` is incomplete (`certify.go`'s
visited set ignores the remaining fuel; KNOWN_GAPS), exactly as
`Ticket.TicketLive`. It stays open. `CasSpinLiveSem fuel` is the same
statement (same start configurations `Spin.CasStart`, same `CasWaiting` /
`CasDone`) over `TraceSem`, under the semantic weak fairness `WeakFairSem`
and memory fairness `MemFair`: a promise or an instruction step needs the
thread to be *certifiable within `fuel`* (`CertOkN`). It is a new, distinct
statement; nothing existing is changed.

- `ProgressFromSem`: deadlock-freedom over `TraceSem` (the `Spin.ProgressFrom`
  shape); it is defined in `LiveSem.lean` beside `LiveFromSem`.
- `CasSpinLiveSem`: CAS-spinlock deadlock-freedom with promises.
- `CasSpinLiveOneShotSem`: per-thread liveness of the one-shot CAS workers
  (not starvation-freedom of the lock, which is false for test-and-set/CAS
  locks with re-acquiring clients).
-/
import Kraken.Promising.LiveSem
import Kraken.Promising.LiveSpin

namespace Kraken.Promising.Live.SpinSem

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem

-- `ProgressFromSem` is in `LiveSem.lean` (same full name).

variable [layout : _root_.Layout]

/-- **CAS-spinlock deadlock-freedom with promises, on the machine with
semantic certification**: from every `Spin.CasStart` configuration, on every
semantic trace under `WeakFairSem ∧ MemFair`, if a thread waits in its
try/spin loop, then some thread not yet past its release later is.

This is *not* the existing `Spin.CasSpinLive fuel`, which is stated over
`succs` (incomplete certification search) and stays open. -/
def CasSpinLiveSem (fuel : Nat) : Prop :=
  ∀ l c states initMem, Spin.CasStart l c states initMem →
    ProgressFromSem Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) Spin.CasWaiting Spin.CasDone

/-- **Per-thread liveness of the one-shot CAS workers with promises** (semantic
machine): every waiting thread is eventually past its release. A property of
these one-shot programs (each worker takes the lock once and halts), not
starvation-freedom of the lock. -/
def CasSpinLiveOneShotSem (fuel : Nat) : Prop :=
  ∀ l c states initMem, Spin.CasStart l c states initMem →
    LiveFromSem Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) Spin.CasWaiting Spin.CasDone

end Kraken.Promising.Live.SpinSem
