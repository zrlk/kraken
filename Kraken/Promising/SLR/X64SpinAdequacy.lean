/-
The adequacy instance of the x64 spinlock (`spinWorker`, x64 `spinlock2`)
under `Arch.tso`: `counter = N` at every final
configuration, from Theorem 1′ (`Theorem1IIPure`), initial erasure and the
per-thread non-promising safety of the workers.

`Spinlock.adequacy` and `Spinlock.counter_of_theorem1Pure` (`SLR/Adequacy.lean`)
are ISA- and architecture-neutral; nothing AArch64-specific enters. The x64
instance discharges, of `Theorem1IIPure`'s hypotheses:

- the scope `Config.NTFree Arch.tso`, by `spinWorker_ntFree`
  (`SLR/X64SpinNoNT.lean`): the worker makes no non-temporal store;
- (O5) `PromisePure`, for **every** release predicate, by `promisePure_tso`
  (`SLR/TsoPromisePure.lean`): under TSO every
  plain store is a release (`tso_plainStore`) and `xchg` is `acqRel`, so
  every promise of the worker, in particular one of the counter store
  `movl %ecx,(%rsi)` or of the unlock `movl $0,(%rdi)`, is fulfilled by a
  release store: a promised release, which option (B) prepays (case (d1)).
  The counter's release predicate never has to be pure for (O5); the
  `PoolSpec` lock predicate is used unchanged.

What remains as hypotheses: Theorem 1′ itself, initial erasure (`hE`,
`hpend`), the workers' `NPSafe` (the x64 per-thread invariant and
cell proofs), and the pool specification of the lock predicate.

## Contents

- `Spinlock.spin_promisePure`: (O5) for the worker under `Arch.tso`, every
  `rel` (the x64 counterpart of AArch64's `swp_promisePure`, `SLR/SwpPure.lean`,
  without its `Bad`/reachable-state invariant: under TSO no promise of the
  worker is ever outside case (d1)).
- `Spinlock.x64_counter`: the x64 `spinlock2` instance under `Arch.tso`.
- `Spinlock.x64_counter_init`: the same with the initial state of
  `SpinInitRes.lean` (initial erasure discharged): Theorem 1′ and the
  workers' `NPSafe` remain.
-/
import Kraken.Promising.SLR.TsoPromisePure
import Kraken.Promising.SLR.X64SpinNoNT
import Kraken.Promising.SLR.SpinInitRes

namespace Kraken.Promising.SLR

namespace Spinlock

section X64

open X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- **(O5) for the x64 spinlock worker under TSO**, for every choice of
release predicates: `promisePure_tso` at `spinWorker_noNTInv`. -/
theorem spin_promisePure {fuel : Nat} {states : List X64.isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, SpinPc s) (rel : Loc → Pred) :
    PromisePure (I := X64.isa) Arch.tso fuel states initMem rel :=
  promisePure_tso spinWorker_noNTInv hs rel

/-- **The x64 spinlock counter under TSO**: `N` threads all starting in the
worker (`SpinPc`), with initial erasure and non-promisingly safe workers,
end with `counter = N` at every reachable final configuration. Theorem 1′'s
scope and (O5) are discharged (see the module docstring). -/
theorem x64_counter {fuel : Nat} (hT : Theorem1IIPure (I := X64.isa) Arch.tso fuel)
    {states : List X64.isa.State} {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, SpinPc s)
    {rF : Nat → Res} {g₀ : Ghost} {N : Nat} {Lk C : Loc} {K : Nat → Loc} {φ : Pred} {ι : PredId}
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model X64.isa) Arch.tso (fun _ r _ => Post N Lk K r) tid n m True
      (Config.init states initMem) (rF tid) g₀)
    (hN : states.length = N) (hN0 : 0 < N) (hrel : g₀.rel Lk = φ) (hupd : ι ∈ g₀.upd Lk)
    (hιlt : ι < g₀.acqTab.length) (hφ : g₀.acqPred ι = φ) (hspec : PoolSpec N Lk C K φ)
    {c : Config X64.isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true) :
    c.mem.finalVal C = BitVec.ofNat 128 N :=
  counter_of_theorem1Pure hT (fun _ hc' => spinWorker_ntFree hs hc') hE hpend
    (spin_promisePure hs _) hsafe hN hN0 hrel hupd hιlt hφ hspec hc hf

/-- **The x64 spinlock counter under TSO, from the initial state**: with the
initial resources of `SpinInitRes.lean` (`threadRes`, `poolRes` under
`lockPred` in `spinGhost`), only Theorem 1′ and the workers' `NPSafe`
remain as hypotheses (`counter_init` with `spinWorker_ntFree` and
`spin_promisePure`). -/
theorem x64_counter_init {fuel : Nat} (hT : Theorem1IIPure (I := X64.isa) Arch.tso fuel)
    {states : List X64.isa.State} {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, SpinPc s)
    {N : Nat} {Lk C : Loc} {K F : Nat → Loc}
    (hL : SpinLocs N Lk C K F) (hN : states.length = N) (hN0 : 0 < N)
    (hC0 : (Config.init states initMem).mem.initVal C = 0)
    (hLk0 : (Config.init states initMem).mem.initVal Lk = 0)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model X64.isa) Arch.tso (fun _ r _ => Post N Lk K r) tid n m True
      (Config.init states initMem) (threadRes (Config.init states initMem).mem N Lk K F tid)
      (spinGhost Lk (lockPred N Lk C K F) (poolRes (Config.init states initMem).mem N C K)))
    {c : Config X64.isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true) :
    c.mem.finalVal C = BitVec.ofNat 128 N :=
  counter_init hT hL hN hN0 hC0 hLk0 (fun _ hc' => spinWorker_ntFree hs hc') (spin_promisePure hs _) hsafe hc hf

end X64

end Spinlock

end Kraken.Promising.SLR
