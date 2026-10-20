/-
**Stage 3: x64 spinlock deadlock-freedom
statements on the machine with semantic certification** (`LiveSem.lean`).

`SpinX64.CmpxSpinLive fuel` (`LiveSpinX64.lean`) and
`SpinX64Xchg.XchgSpinLive fuel` (`LiveSpinX64Xchg.lean`) are stated over the
existing machine `succs`, whose certification search `certify` is incomplete
(`certify.go`'s visited set ignores the remaining fuel; KNOWN_GAPS), exactly
as `Spin.CasSpinLive` and `TicketX64.TicketX64Live`. They stay open. The
statements here are the same (same start configurations `CmpxStart` /
`XchgStart`, same `Waiting` / `Done`) over `TraceSem Arch.tso`, under the
semantic weak fairness `WeakFairSem` and memory fairness `MemFair`: a promise
or an instruction step needs the thread to be *certifiable within `fuel`*
(`CertOkN`). They are new, distinct statements; nothing existing is changed.

- `CmpxSpinLiveSem`, `CmpxSpinLiveOneShotSem`: the `lock cmpxchg` spinlock
  (`spinlock_cmpxchg2/3.kl`).
- `XchgSpinLiveSem`, `XchgSpinLiveOneShotSem`: the `xchg`
  test-and-test-and-set spinlock (`spinlock2/3.kl`).

The one-shot forms are per-thread liveness of these one-shot workers (each
takes the lock once and halts), not starvation-freedom of the lock (false for
test-and-set/CAS locks with re-acquiring clients).

`MemFair` on x86 is a modelling assumption (store buffers drain in finite
time, as in x86-TSO); see its docstring in `LiveTrace.lean`.
-/
import Kraken.Promising.LiveSem
import Kraken.Promising.LiveSpinX64
import Kraken.Promising.LiveSpinX64Xchg

namespace Kraken.Promising.Live.SpinX64Sem

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.SpinSem (ProgressFromSem)
open Kraken.Promising.Live.SpinX64 (CmpxStart CmpxWaiting CmpxDone)
open Kraken.Promising.Live.SpinX64Xchg (XchgStart XchgWaiting XchgDone)

variable [layout : _root_.Layout]

/-- Weak and memory fairness on the semantic `Arch.tso` machine. -/
abbrev FairX (fuel : Nat) (cfg : Nat → Config isa) : Prop :=
  WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg

/-- **`lock cmpxchg` spinlock deadlock-freedom with promises, on the machine
with semantic certification**: from every `CmpxStart` configuration, on every
semantic trace under `WeakFairSem ∧ MemFair`, if a thread waits in its
acquire loop, then some thread not yet past its release later is.

This is *not* the existing `SpinX64.CmpxSpinLive fuel`, which is stated over
`succs` (incomplete certification search) and stays open. -/
def CmpxSpinLiveSem (fuel : Nat) : Prop :=
  ∀ states initMem, CmpxStart states initMem →
    ProgressFromSem Arch.tso fuel (Config.init states initMem) (FairX fuel) CmpxWaiting CmpxDone

/-- **Per-thread liveness of the one-shot `lock cmpxchg` workers with
promises** (semantic machine): every waiting thread is eventually past its
release. Not starvation-freedom of the lock. -/
def CmpxSpinLiveOneShotSem (fuel : Nat) : Prop :=
  ∀ states initMem, CmpxStart states initMem →
    LiveFromSem Arch.tso fuel (Config.init states initMem) (FairX fuel) CmpxWaiting CmpxDone

/-- **`xchg` spinlock deadlock-freedom with promises, on the machine with
semantic certification** (the `CmpxSpinLiveSem` shape at `XchgStart`). This
is *not* the existing `SpinX64Xchg.XchgSpinLive fuel`, which stays open. -/
def XchgSpinLiveSem (fuel : Nat) : Prop :=
  ∀ states initMem, XchgStart states initMem →
    ProgressFromSem Arch.tso fuel (Config.init states initMem) (FairX fuel) XchgWaiting XchgDone

/-- **Per-thread liveness of the one-shot `xchg` workers with promises**
(semantic machine). Not starvation-freedom of the lock. -/
def XchgSpinLiveOneShotSem (fuel : Nat) : Prop :=
  ∀ states initMem, XchgStart states initMem →
    LiveFromSem Arch.tso fuel (Config.init states initMem) (FairX fuel) XchgWaiting XchgDone

end Kraken.Promising.Live.SpinX64Sem
