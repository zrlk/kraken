/-
**Stage 3: SWP-spinlock deadlock-freedom
statements on the machine with semantic certification** (`LiveSem.lean`).

`SpinSwp.SwpSpinLive fuel` and `SpinSwp.SwplSpinLive fuel`
(`LiveSpinSwp.lean`) are stated over the existing machine `succs`, whose
certification search `certify` is incomplete (`certify.go`'s visited set
ignores the remaining fuel; KNOWN_GAPS), exactly as `Spin.CasSpinLive`. They
stay open. The statements here are the same properties (the start
configurations of the existing safety theorems, `SpinSwp.SwpWaitingG` /
`SpinSwp.SwpDoneG`) over `TraceSem`, under the semantic weak fairness
`WeakFairSem` and memory fairness `MemFair` (the shape of
`SpinSem.CasSpinLiveSem`). They are new, distinct statements; nothing existing
is changed.

- `SwpLiveSemUnderG P Start fuel`: deadlock-freedom (`SpinSem.ProgressFromSem`)
  of the workers of an SWP-spinlock program `P`;
- `SwpOneShotSemUnderG P Start fuel`: per-thread liveness of its one-shot
  workers (not starvation-freedom of the lock, which is false for
  test-and-set locks with re-acquiring clients);
- `SwpSpinLiveSem`/`SwpSpinLiveOneShotSem` (`spinlock_swp2/3`: `SWPA` lock,
  `STLR` unlock) and `SwplSpinLiveSem`/`SwplSpinLiveOneShotSem`
  (`spinlock_swpl2/3`: `SWPA` lock, `SWPL` unlock).
-/
import Kraken.Promising.LiveSpinSem
import Kraken.Promising.LiveSpinSwp

namespace Kraken.Promising.Live.SpinSemSwp

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.SpinSwp
open Kraken.Promising.Live.SpinSem (ProgressFromSem)
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.EnvG.SwplLock (swplWorker)

variable [layout : _root_.Layout]

/-- The fairness hypothesis of the semantic statements. -/
abbrev FairSem (fuel : Nat) (cfg : Nat → Config isa) : Prop :=
  WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg

/-- Deadlock-freedom of the workers of `P` from `Start` configurations, on
the semantic machine, under `WeakFairSem ∧ MemFair`. -/
def SwpLiveSemUnderG (P : Program) (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (fuel : Nat) : Prop :=
  ∀ l c states initMem, SwpStartG Start l c states initMem →
    ProgressFromSem Arch.armv8 fuel (Config.init states initMem) (FairSem fuel) (SwpWaitingG P) (SwpDoneG P)

/-- Per-thread liveness of the one-shot workers of `P` on the semantic
machine. -/
def SwpOneShotSemUnderG (P : Program) (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (fuel : Nat) : Prop :=
  ∀ l c states initMem, SwpStartG Start l c states initMem →
    LiveFromSem Arch.armv8 fuel (Config.init states initMem) (FairSem fuel) (SwpWaitingG P) (SwpDoneG P)

theorem SwpLiveSemUnderG.mono {P : Program} {S S' : BitVec 64 → BitVec 64 → isa.State → Prop} {fuel : Nat}
    (h : SwpLiveSemUnderG P S fuel) (hS : ∀ l c s, S' l c s → S l c s) : SwpLiveSemUnderG P S' fuel :=
  fun l c states initMem hs => h l c states initMem ⟨hs.hlc, fun s hm => hS l c s (hs.hst s hm), hs.hL0⟩

theorem SwpOneShotSemUnderG.mono {P : Program} {S S' : BitVec 64 → BitVec 64 → isa.State → Prop} {fuel : Nat}
    (h : SwpOneShotSemUnderG P S fuel) (hS : ∀ l c s, S' l c s → S l c s) : SwpOneShotSemUnderG P S' fuel :=
  fun l c states initMem hs => h l c states initMem ⟨hs.hlc, fun s hm => hS l c s (hs.hst s hm), hs.hL0⟩

/-! ## `spinlock_swp2/3`: `SWPA` lock, `STLR` unlock -/

/-- **SWP-spinlock deadlock-freedom with promises, on the machine with
semantic certification.** Not the existing `SpinSwp.SwpSpinLive fuel` (over
`succs`, open). -/
def SwpSpinLiveSem (fuel : Nat) : Prop := SwpLiveSemUnderG swpWorker SLR.SwpPublic.StartState fuel

/-- **Per-thread liveness of the one-shot SWP workers with promises**
(semantic machine). A property of these one-shot programs, not
starvation-freedom of the lock. -/
def SwpSpinLiveOneShotSem (fuel : Nat) : Prop := SwpOneShotSemUnderG swpWorker SLR.SwpPublic.StartState fuel

/-! ## `spinlock_swpl2/3`: `SWPA` lock, `SWPL` unlock -/

/-- **SWPL-spinlock deadlock-freedom with promises, on the machine with
semantic certification.** Not the existing `SpinSwp.SwplSpinLive fuel` (over
`succs`, open). -/
def SwplSpinLiveSem (fuel : Nat) : Prop := SwpLiveSemUnderG swplWorker SLR.EnvG.SwplLock.StartState fuel

/-- **Per-thread liveness of the one-shot SWPL workers with promises**
(semantic machine). A property of these one-shot programs, not
starvation-freedom of the lock. -/
def SwplSpinLiveOneShotSem (fuel : Nat) : Prop :=
  SwpOneShotSemUnderG swplWorker SLR.EnvG.SwplLock.StartState fuel

end Kraken.Promising.Live.SpinSemSwp
