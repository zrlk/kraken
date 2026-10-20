/-
**Stage 3: deadlock-freedom statements for the
spinlocks.**

A test-and-set spinlock is not starvation-free in general: with clients
that take the lock again and again, a fair scheduler can let one thread
win every race while another spins forever. The property for a lock in
general is **deadlock-freedom** (`ProgressFrom`): if some thread is waiting,
then eventually some thread that was not yet done is done. The "not yet"
matters: "some thread is done" alone would hold trivially once any thread
has finished.

The first family is the AArch64 CAS spinlock `casTtasWorker`
(`spinlock_cas2.kl`/`spinlock_cas3.kl`): a thread is *waiting* (`CasWaiting`)
in its try/spin loop (`MOV W2`, `CASA`, `CBZ`, `LDR`, `CBNZ`, `B try`), and
*done* (`CasDone`) past its `STLR` release.

- `CasSpinLive`: the statement under `WeakFair ∧ MemFair` (open, with
  promises).
- `CasSpinLivePF`: the promise-free fragment (traces with no promise step).
- `CasSpinLiveOneShotPF`: every waiting thread is eventually done, true for
  these one-shot workers (not starvation-freedom of the lock).
-/
import Kraken.Promising.SLR.EnvG.CasSmoke
import Kraken.Promising.LiveRank

namespace Kraken.Promising.Live.Spin

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

/-! ## The shape (ISA-neutral)

`ProgressFrom` (deadlock-freedom from `c0` under `Fair`) is in
`LiveTrace.lean`, beside `LiveFrom` (moved; same full name
`Live.Spin.ProgressFrom`). -/

/-! ## The AArch64 CAS spinlock -/

variable [layout : _root_.Layout]

/-- The try/spin loop's addresses: `MOV W2`, `CASA`, `CBZ`, `LDR`, `CBNZ`,
`B try` (directives 3–5 and 7–9; the labels `try` and `spin` are at the
addresses of directives 3 and 7). -/
def casWaitPcs : List Int64 := [3, 4, 5, 7, 8, 9].map (layout casTtasWorker).addrOf

/-- The addresses up to and including the `STLR` release (directives 0–14). -/
def casPrePcs : List Int64 := (List.range 15).map (layout casTtasWorker).addrOf

/-- Thread `tid` is in its try/spin loop. -/
def CasWaiting (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ casWaitPcs

/-- Thread `tid` is past its release. -/
def CasDone (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ casPrePcs

/-- **The start configurations of `cas_counter_envG`**: worker threads at
`CasSmoke.StartState l c` (lock `l`, counter `c`), disjoint 4-byte words, the
lock initially `0`. Any number of threads. -/
structure CasStart (l c : BitVec 64) (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  hlc : Decls.overlaps l 4 c 4 = false
  hst : ∀ s ∈ states, SLR.EnvG.CasSmoke.StartState l c s
  hL0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0

/-- CAS-spinlock deadlock-freedom under the trace hypothesis `Fair`. -/
def CasSpinLiveUnder (fuel : Nat) (Fair : (Nat → Config isa) → Prop) : Prop :=
  ∀ l c states initMem, CasStart l c states initMem →
    ProgressFrom Arch.armv8 fuel (Config.init states initMem) Fair CasWaiting CasDone

/-- **CAS-spinlock deadlock-freedom under weak and memory fairness** (open,
with promises). -/
def CasSpinLive (fuel : Nat) : Prop :=
  CasSpinLiveUnder fuel fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg

/-- **The promise-free fragment** of `CasSpinLive`. -/
def CasSpinLivePF (fuel : Nat) : Prop :=
  CasSpinLiveUnder fuel fun cfg =>
    WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg

/-- **Per-thread liveness of the one-shot CAS workers** (promise-free
fragment): every waiting thread is eventually done (the `TicketLive` shape).
This is a property of these *one-shot* programs (each worker takes the lock
once and halts), derived from deadlock-freedom: the set of finished threads
can grow only finitely often. It is **not** starvation-freedom of the lock,
which is false for test-and-set/CAS spinlocks in general (with clients that
re-acquire, a fair scheduler can let one thread lose every race forever). -/
def CasSpinLiveOneShotPF (fuel : Nat) : Prop :=
  ∀ l c states initMem, CasStart l c states initMem →
    LiveFrom Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg)
      CasWaiting CasDone

theorem CasSpinLiveUnder.mono {fuel : Nat} {F F' : (Nat → Config isa) → Prop} (h : CasSpinLiveUnder fuel F)
    (hF : ∀ cfg, F' cfg → F cfg) : CasSpinLiveUnder fuel F' :=
  fun l c states initMem hs tr h0 hf => h l c states initMem hs tr h0 (hF _ hf)

theorem casSpinLivePF_of_live {fuel : Nat} (h : CasSpinLive fuel) : CasSpinLivePF fuel :=
  h.mono fun _ hf => ⟨hf.1, hf.2.1⟩

end Kraken.Promising.Live.Spin
