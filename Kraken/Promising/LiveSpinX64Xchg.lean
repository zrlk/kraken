/-
**Stage 3: deadlock-freedom statements for the x64
`xchg` spinlock** (`spinlock2/3.kl`, `SpinAbs.spinImageV`), the twin of
`LiveSpinX64.lean`'s `lock cmpxchg` statements, over the verbatim workers of
the `.kl` files run in their images (absolute operands `(lock)`/`(counter)`,
declarations `{}`), under `Arch.tso`.

The property is **deadlock-freedom** (`SpinX64Step.ProgressFromN`): if some
thread is waiting, eventually some thread that was not yet done is done.
Starvation-freedom is false for test-and-set locks in general, and is not
stated.

- A thread is *waiting* (`XchgWaiting`) in its test-and-test-and-set loop
  (`movl (lock),%eax`/`testl`/`jne`/`movl $1,%eax`/`xchgl`/`testl`/`jne`,
  positions 1–7 of `spinImageV`), *done* (`XchgDone`) past its
  `movl $0,(lock)` release.
- `XchgSpinLive` (open, with promises), `XchgSpinLivePF` (promise-free
  fragment), `XchgSpinLiveOneShotPF` (every waiting thread is eventually
  done: a property of these one-shot workers, not starvation-freedom).

`MemFair` on x86 is a modelling assumption (store buffers drain in finite
time, as in x86-TSO); see its docstring in `LiveTrace.lean`.
-/
import Kraken.Promising.SLR.EnvG.X64SpinAbsPublic
import Kraken.Promising.LiveSpinX64Step
import Kraken.Promising.LiveRank

namespace Kraken.Promising.Live.SpinX64Xchg

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.SpinX64Step
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV symV StartStateV)

variable [layout : _root_.Layout]

/-- The test-and-test-and-set loop's addresses (positions 1–7 of
`spinImageV`; the label `worker` is at the address of position 1). -/
def xchgWaitPcs : List Int64 := [1, 2, 3, 4, 5, 6, 7].map (layout spinImageV).addrOf

/-- The addresses up to and including the `movl $0,(lock)` release
(positions 0–11). -/
def xchgPrePcs : List Int64 := (List.range 12).map (layout spinImageV).addrOf

/-- Thread `tid` is in its acquire loop. -/
def XchgWaiting (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∈ xchgWaitPcs

/-- Thread `tid` is past its release. -/
def XchgDone (tid : Nat) (c : Config isa) : Prop := ∃ t, c.threads[tid]? = some t ∧ t.st.st.2 ∉ xchgPrePcs

/-- **The start configurations of `x64_spin_counter_envG_verbatim`**: worker
threads at `StartStateV` (the image, no declarations, pc at `worker`, end at
`done`, neither word in private memory; no register assumed), disjoint
4-byte words, the lock initially `0`. Any number of threads. -/
structure XchgStart (states : List isa.State) (initMem : List (Loc × Val)) : Prop where
  hlc : Decls.overlaps (symV "lock") 4 (symV "counter") 4 = false
  hst : ∀ s ∈ states, StartStateV s
  hL0 : (Config.init states initMem).mem.initVal ⟨symV "lock", 4⟩ = 0

/-- `xchg` spinlock deadlock-freedom under the trace hypothesis `Fair`. -/
def XchgSpinLiveUnder (fuel : Nat) (Fair : (Nat → Config isa) → Prop) : Prop :=
  ∀ states initMem, XchgStart states initMem →
    ProgressFromN Arch.tso fuel (Config.init states initMem) Fair XchgWaiting XchgDone

/-- **`xchg` spinlock deadlock-freedom under weak and memory fairness**
(open, with promises). -/
def XchgSpinLive (fuel : Nat) : Prop :=
  XchgSpinLiveUnder fuel fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg

/-- **The promise-free fragment** of `XchgSpinLive`. -/
def XchgSpinLivePF (fuel : Nat) : Prop :=
  XchgSpinLiveUnder fuel fun cfg =>
    WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg

/-- **Per-thread liveness of the one-shot `xchg` workers** (promise-free
fragment): every waiting thread is eventually done. A property of these
*one-shot* programs (each worker takes the lock once and halts), derived from
deadlock-freedom; **not** starvation-freedom of the lock. -/
def XchgSpinLiveOneShotPF (fuel : Nat) : Prop :=
  ∀ states initMem, XchgStart states initMem →
    LiveFrom Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFair Arch.tso fuel cfg ∧ MemFair Arch.tso cfg ∧ PromiseFree Arch.tso cfg)
      XchgWaiting XchgDone

theorem XchgSpinLiveUnder.mono {fuel : Nat} {F F' : (Nat → Config isa) → Prop} (h : XchgSpinLiveUnder fuel F)
    (hF : ∀ cfg, F' cfg → F cfg) : XchgSpinLiveUnder fuel F' :=
  fun states initMem hs tr h0 hf => h states initMem hs tr h0 (hF _ hf)

theorem xchgSpinLivePF_of_live {fuel : Nat} (h : XchgSpinLive fuel) : XchgSpinLivePF fuel :=
  h.mono fun _ hf => ⟨hf.1, hf.2.1⟩

end Kraken.Promising.Live.SpinX64Xchg
