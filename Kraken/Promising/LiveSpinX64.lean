/-
**Stage 3: deadlock-freedom statements for the x64
spinlocks**, the x64 counterparts of `LiveSpin.lean`'s AArch64 CAS
statements, over the verbatim workers of the `.kl` files run in their images
(absolute operands `(lock)`/`(counter)`, declarations `{}`), under
`Arch.tso`.

The property is **deadlock-freedom** (`SpinX64Step.ProgressFromN`, the shape
of `Live.Spin.ProgressFrom`): if some thread is waiting, eventually some
thread that was not yet done is done. Starvation-freedom is false for
test-and-set/CAS locks in general, and is not stated.

- `lock cmpxchg` (`spinlock_cmpxchg2/3.kl`, `CmpxAbs.cmpxImageV`): a thread
  is *waiting* (`CmpxWaiting`) in its `xorl`/`movl`/`lock cmpxchg`/`jne`
  loop, *done* (`CmpxDone`) past its `movl $0,(lock)` release.
  `CmpxSpinLive` (open, with promises), `CmpxSpinLivePF` (promise-free
  fragment), `CmpxSpinLiveOneShotPF` (every waiting thread is eventually
  done: a property of these one-shot workers, not starvation-freedom).

`MemFair` on x86 is a modelling assumption (store buffers drain in finite
time, as in x86-TSO); see its docstring in `LiveTrace.lean`.
-/
import Kraken.Promising.SLR.EnvG.X64CmpxAbsPublic
import Kraken.Promising.LiveSpinX64Step
import Kraken.Promising.LiveRank

namespace Kraken.Promising.Live.SpinX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.SpinX64Step
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV symC StartStateCV)

/-! ## The x64 `lock cmpxchg` spinlock -/

section Cmpx

variable [layout : _root_.Layout]

/-- The `xorl`/`movl`/`lock cmpxchg`/`jne` loop's addresses (positions 1–4 of
`cmpxImageV`; the label `worker` is at the address of position 1). -/
def cmpxWaitPcs : List Int64 := [1, 2, 3, 4].map (layout cmpxImageV).addrOf

/-- The addresses up to and including the `movl $0,(lock)` release
(positions 0–8). -/
def cmpxPrePcs : List Int64 := (List.range 9).map (layout cmpxImageV).addrOf

/-- Thread `tid` is in its acquire loop. -/
def CmpxWaiting (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ cmpxWaitPcs

/-- Thread `tid` is past its release. -/
def CmpxDone (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ cmpxPrePcs

/-- **The start configurations of `x64_cmpx_counter_envG_verbatim`**: worker
threads at `StartStateCV` (the image, no declarations, pc at `worker`, end
at `done`, neither word in private memory; no register assumed), disjoint
4-byte words, the lock initially `0`. Any number of threads. -/
structure CmpxStart (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  hlc : Decls.overlaps (symC "lock") 4 (symC "counter") 4 = false
  hst : ∀ s ∈ states, StartStateCV s
  hL0 : (Config.init states initMem).mem.initVal ⟨symC "lock", 4⟩ = 0

/-- `lock cmpxchg` spinlock deadlock-freedom under the trace hypothesis `Fair`. -/
def CmpxSpinLiveUnder (fuel : Nat) (Fair : (Nat → Config isa) → Prop) : Prop :=
  ∀ states initMem, CmpxStart states initMem →
    ProgressFromN Arch.tso fuel (Config.init states initMem) Fair CmpxWaiting CmpxDone

/-- **`lock cmpxchg` spinlock deadlock-freedom under weak and memory
fairness** (open, with promises). -/
def CmpxSpinLive (fuel : Nat) : Prop :=
  CmpxSpinLiveUnder fuel fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg

/-- **The promise-free fragment** of `CmpxSpinLive`. -/
def CmpxSpinLivePF (fuel : Nat) : Prop :=
  CmpxSpinLiveUnder fuel fun cfg =>
    WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg

/-- **Per-thread liveness of the one-shot `lock cmpxchg` workers**
(promise-free fragment): every waiting thread is eventually done. A property
of these *one-shot* programs (each worker takes the lock once and halts),
derived from deadlock-freedom; **not** starvation-freedom of the lock. -/
def CmpxSpinLiveOneShotPF (fuel : Nat) : Prop :=
  ∀ states initMem, CmpxStart states initMem →
    LiveFrom Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      CmpxWaiting CmpxDone

theorem CmpxSpinLiveUnder.mono {fuel : Nat} {F F' : (Nat → Config isa) → Prop} (h : CmpxSpinLiveUnder fuel F)
    (hF : ∀ cfg, F' cfg → F cfg) : CmpxSpinLiveUnder fuel F' :=
  fun states initMem hs tr h0 hf => h states initMem hs tr h0 (hF _ hf)

theorem cmpxSpinLivePF_of_live {fuel : Nat} (h : CmpxSpinLive fuel) : CmpxSpinLivePF fuel :=
  h.mono fun _ hf => ⟨hf.1, hf.2.1⟩

end Cmpx

end Kraken.Promising.Live.SpinX64
