/-
**Stage 3: deadlock-freedom statements for the
AArch64 SWP spinlocks.**

The two families share the worker shape of `LiveSpinSwpTrees.lean`
(`SWPA` acquire, `LDR` test-and-test-and-set spin):
- `swpWorker` (`spinlock_swp2.kl`/`spinlock_swp3.kl`): `STLR` release;
- `swplWorker` (`spinlock_swpl2.kl`/`spinlock_swpl3.kl`): `SWPL` release.

A thread is *waiting* (`SwpWaitingG`) in its try/spin loop (`SWPA`, `CBZ`,
`LDR`, `CBNZ`, `B try`: directives 3, 4, 6, 7, 8) and *done* (`SwpDoneG`)
past its release (not at directives 0–13). As for the CAS spinlock
(`LiveSpin.lean`), the property is **deadlock-freedom** (`ProgressFrom`),
not starvation-freedom, which is false for test-and-set locks with clients
that re-acquire.

Per family (`Swp…` for `swpWorker`, `Swpl…` for `swplWorker`), with the
start states of the existing safety theorems (`SwpPublic.StartState`,
`SwplLock.StartState`):
- `SwpSpinLive`/`SwplSpinLive`: under `WeakFair ∧ MemFair` (open, with
  promises);
- `SwpSpinLivePF`/`SwplSpinLivePF`: the promise-free fragment;
- `SwpSpinLiveOneShotPF`/`SwplSpinLiveOneShotPF`: every waiting thread is
  eventually done, true for these one-shot workers (each takes the lock once
  and halts); **not** starvation-freedom of the lock.
-/
import Kraken.Promising.LiveSpin
import Kraken.Promising.SLR.SwpPublic
import Kraken.Promising.SLR.EnvG.SwplLockSmoke

namespace Kraken.Promising.Live.SpinSwp

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Spin
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.EnvG.SwplLock (swplWorker)

variable [layout : _root_.Layout]

/-! ## The shape, for a program `P` of the SWP-spinlock form -/

/-- The try/spin loop's addresses: `SWPA`, `CBZ`, `LDR`, `CBNZ`, `B try`
(directives 3, 4, 6, 7, 8; the labels `try` and `spin` share the addresses
of directives 3 and 6). -/
def swpWaitPcs (P : Program) : List Int64 := [3, 4, 6, 7, 8].map (layout P).addrOf

/-- The addresses up to and including the release (directives 0–13). -/
def swpPrePcs (P : Program) : List Int64 := (List.range 14).map (layout P).addrOf

/-- Thread `tid` is in its try/spin loop. -/
def SwpWaitingG (P : Program) (tid : Nat) (c : Config isa) : Prop :=
  ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ swpWaitPcs P

/-- Thread `tid` is past its release. -/
def SwpDoneG (P : Program) (tid : Nat) (c : Config isa) : Prop :=
  ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ swpPrePcs P

/-- A worker of `P` at its start (the fields of `SwpPublic.StartState`). -/
structure StartG (P : Program) (l c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout P
  decls : s.decls = {}
  endPc : s.endPc = (layout P).addrOf 16
  pc : s.st.2 = (layout P).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = l
  x1 : s.st.1.regs.X1.toBitVec = c
  dl : Mem.loadInt s.st.1.dmem l 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

/-- **The start configurations**: workers satisfying `Start l c` (lock `l`,
counter `c`), disjoint 4-byte words, the lock initially `0`. Any number of
threads. -/
structure SwpStartG (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (l c : BitVec 64)
    (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  hlc : Decls.overlaps l 4 c 4 = false
  hst : ∀ s ∈ states, Start l c s
  hL0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0

/-- Deadlock-freedom of the workers of `P` from `Start` configurations under
the trace hypothesis `Fair`. -/
def SwpLiveUnderG (P : Program) (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (fuel : Nat)
    (Fair : (Nat → Config isa) → Prop) : Prop :=
  ∀ l c states initMem, SwpStartG Start l c states initMem →
    ProgressFrom Arch.armv8 fuel (Config.init states initMem) Fair (SwpWaitingG P) (SwpDoneG P)

/-- Per-thread liveness of the one-shot workers of `P` under `Fair`. -/
def SwpOneShotUnderG (P : Program) (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (fuel : Nat)
    (Fair : (Nat → Config isa) → Prop) : Prop :=
  ∀ l c states initMem, SwpStartG Start l c states initMem →
    LiveFrom Arch.armv8 fuel (Config.init states initMem) Fair (SwpWaitingG P) (SwpDoneG P)

/-- The promise-free fairness hypothesis. -/
abbrev FairPF (fuel : Nat) (cfg : Nat → Config isa) : Prop :=
  WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg ∧ PromiseFree Arch.armv8 cfg

theorem SwpLiveUnderG.mono {P : Program} {S S' : BitVec 64 → BitVec 64 → isa.State → Prop} {fuel : Nat}
    {F F' : (Nat → Config isa) → Prop} (h : SwpLiveUnderG P S fuel F) (hS : ∀ l c s, S' l c s → S l c s)
    (hF : ∀ cfg, F' cfg → F cfg) : SwpLiveUnderG P S' fuel F' :=
  fun l c states initMem hs tr h0 hf =>
    h l c states initMem ⟨hs.hlc, fun s hm => hS l c s (hs.hst s hm), hs.hL0⟩ tr h0 (hF _ hf)

theorem SwpOneShotUnderG.mono {P : Program} {S S' : BitVec 64 → BitVec 64 → isa.State → Prop} {fuel : Nat}
    {F : (Nat → Config isa) → Prop} (h : SwpOneShotUnderG P S fuel F) (hS : ∀ l c s, S' l c s → S l c s) :
    SwpOneShotUnderG P S' fuel F :=
  fun l c states initMem hs =>
    h l c states initMem ⟨hs.hlc, fun s hm => hS l c s (hs.hst s hm), hs.hL0⟩

/-! ## `spinlock_swp2/3`: `SWPA` lock, `STLR` unlock -/

/-- **SWP-spinlock deadlock-freedom under weak and memory fairness** (open,
with promises). -/
def SwpSpinLive (fuel : Nat) : Prop :=
  SwpLiveUnderG swpWorker SLR.SwpPublic.StartState fuel fun cfg =>
    WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg

/-- **The promise-free fragment** of `SwpSpinLive`. -/
def SwpSpinLivePF (fuel : Nat) : Prop := SwpLiveUnderG swpWorker SLR.SwpPublic.StartState fuel (FairPF fuel)

/-- **Per-thread liveness of the one-shot SWP workers** (promise-free
fragment): every waiting thread is eventually done. A property of these
one-shot programs, **not** starvation-freedom of the lock. -/
def SwpSpinLiveOneShotPF (fuel : Nat) : Prop :=
  SwpOneShotUnderG swpWorker SLR.SwpPublic.StartState fuel (FairPF fuel)

theorem swpSpinLivePF_of_live {fuel : Nat} (h : SwpSpinLive fuel) : SwpSpinLivePF fuel :=
  SwpLiveUnderG.mono h (fun _ _ _ h => h) fun _ hf => ⟨hf.1, hf.2.1⟩

/-! ## `spinlock_swpl2/3`: `SWPA` lock, `SWPL` unlock -/

/-- **SWPL-spinlock deadlock-freedom under weak and memory fairness** (open,
with promises). -/
def SwplSpinLive (fuel : Nat) : Prop :=
  SwpLiveUnderG swplWorker SLR.EnvG.SwplLock.StartState fuel fun cfg =>
    WeakFair Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg

/-- **The promise-free fragment** of `SwplSpinLive`. -/
def SwplSpinLivePF (fuel : Nat) : Prop :=
  SwpLiveUnderG swplWorker SLR.EnvG.SwplLock.StartState fuel (FairPF fuel)

/-- **Per-thread liveness of the one-shot SWPL workers** (promise-free
fragment). A property of these one-shot programs, **not** starvation-freedom
of the lock. -/
def SwplSpinLiveOneShotPF (fuel : Nat) : Prop :=
  SwpOneShotUnderG swplWorker SLR.EnvG.SwplLock.StartState fuel (FairPF fuel)

theorem swplSpinLivePF_of_live {fuel : Nat} (h : SwplSpinLive fuel) : SwplSpinLivePF fuel :=
  SwpLiveUnderG.mono h (fun _ _ _ h => h) fun _ hf => ⟨hf.1, hf.2.1⟩

end Kraken.Promising.Live.SpinSwp
