/-
**Liveness of the x64 `xchg` spinlock with promises in the runner's
declarations form.**

`Live.SpinX64SemXchgLive.spin_xchg_live_sem` (deadlock-freedom) and
`spin_xchg_live_oneShot_sem` (per-thread, one-shot workers), on the machine
with semantic certification, are stated for workers with no declarations
(`SpinX64Xchg.XchgStart`: `StartStateV`, `decls = {}`). With the bridge of the
promise-free form (`LiveRunnerX64Spin`: `spinImageV_cellsDeclsAgree`,
`XchgStartD`; `LiveRunnerX64.execSimD`) unchanged:

- **`spin_xchg_live_sem_runner`** (`progressFromSem_transfer`) and
  `spin_xchg_live_oneShot_sem_runner` (`liveFromSem_transfer`,
  `LiveRunnerSemSim`), under `Fair = WeakFairSem ∧ MemFair` (as the existing
  theorems; on x86 `MemFair` is a modelling assumption — store buffers drain
  in finite time, see `LiveTrace.lean`), from every `XchgStartD ds`
  configuration (the same hypotheses as the promise-free
  `spin_xchg_live_pf_runner`), along `State.noDecls`;
- `_runner_concrete` (the runner's layout `spinLayoutV` and declarations
  `spinDeclsD`) and `_runnerN` (`N` copies of `spinWorkerD0`, the runner's
  initial memory; no hypothesis left).

**Short-name clash** (documented, not renamed): `spin_xchg_live_sem_runnerN`
here (declarations `ds` = the runner's `spinDeclsD`, workers `spinWorkerD0`)
has the same short name as the existing
`Live.SpinX64SemXchgLive.spin_xchg_live_sem_runnerN` (`decls = {}`, workers
`spinWorkerV0`). With both namespaces open, write them qualified, or use
the distinct additive alias **`spin_xchg_live_sem_runnerN_decls`** for the
one here.
-/
import Kraken.Promising.LiveRunnerSemSim
import Kraken.Promising.LiveRunnerX64Spin
import Kraken.Promising.LiveSpinX64SemXchgLive

namespace Kraken.Promising.Live.RunnerSemX64Xchg

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.Sem Kraken.Promising.Live.RunnerSemSim
open Kraken.Promising.Live.RunnerX64 Kraken.Promising.Live.RunnerX64Spin
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV symV)

section Generic

variable [layout : _root_.Layout]

/-- **`xchg` spinlock deadlock-freedom with promises and
declarations `ds`** (`SpinX64Sem.XchgSpinLiveSem` at `XchgStartD ds`;
`Fair = WeakFairSem ∧ MemFair`). -/
def XchgSpinLiveSemD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ states initMem, XchgStartD ds states initMem →
    SpinSem.ProgressFromSem Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) SpinX64Xchg.XchgWaiting SpinX64Xchg.XchgDone

/-- **Per-thread liveness of the one-shot `xchg` workers with
promises and declarations `ds`** (`SpinX64Sem.XchgSpinLiveOneShotSem` at
`XchgStartD ds`). -/
def XchgSpinLiveOneShotSemD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ states initMem, XchgStartD ds states initMem →
    LiveFromSem Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) SpinX64Xchg.XchgWaiting SpinX64Xchg.XchgDone

/-- `XchgStartD ds` maps along `State.noDecls` to the existing `XchgStart`. -/
theorem xchgStart_noDecls {ds : Decls} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : XchgStartD ds states initMem) :
    SpinX64Xchg.XchgStart (states.map State.noDecls) initMem :=
  ⟨hs.hlc, fun s h => by
    obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
    have h'' := hs.hst s' h'
    exact ⟨h''.exe, rfl, h''.pc, h''.endPc, h''.split⟩, hs.hL0⟩

/-- **Deadlock-freedom of the x64 `xchg` spinlock with promises and
the runner's declarations** (Stage 3, semantic certification;
`spinlock_spinlock2/3.kl` verbatim): on a valid layout of `spinImageV`, for
every `ds` that resolves `lock` and `counter` (4 bytes) to themselves, on
every `TraceSem` `Arch.tso` trace from a `XchgStartD ds` configuration under
`WeakFairSem ∧ MemFair` (x86 `MemFair`: a modelling assumption), if a thread
waits in its acquire loop, then some thread not yet past its release later
is. `spin_xchg_live_sem` transferred along `State.noDecls`
(`progressFromSem_transfer`, `execSimD`). -/
theorem spin_xchg_live_sem_runner [Executable.ValidLayout (layout spinImageV)] (ds : Decls) (fuel : Nat) :
    XchgSpinLiveSemD ds fuel := by
  intro states initMem hs
  refine progressFromSem_transfer (execSimD (spinImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodS_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  rw [mapC_init]
  exact SpinX64SemXchgLive.spin_xchg_live_sem fuel _ initMem (xchgStart_noDecls hs)

/-- **Per-thread liveness of the one-shot x64 `xchg` workers with
promises and the runner's declarations** (one-shot workers, not
starvation-freedom of the lock; `Fair = WeakFairSem ∧ MemFair`, x86
`MemFair` a modelling assumption): `spin_xchg_live_oneShot_sem` transferred
along `State.noDecls` (`liveFromSem_transfer`). -/
theorem spin_xchg_live_oneShot_sem_runner [Executable.ValidLayout (layout spinImageV)] (ds : Decls)
    (fuel : Nat) : XchgSpinLiveOneShotSemD ds fuel := by
  intro states initMem hs
  refine liveFromSem_transfer (execSimD (spinImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodS_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  rw [mapC_init]
  exact SpinX64SemXchgLive.spin_xchg_live_oneShot_sem fuel _ initMem (xchgStart_noDecls hs)

end Generic

/-! ## The runner's configuration -/

section Concrete

open Kraken.Promising.X64.EnvG.SpinAbs.Concrete
attribute [local instance] spinLayoutV

/-- `spin_xchg_live_sem_runner` at the runner's layout `spinLayoutV` and
declarations `spinDeclsD`. No hypothesis left. -/
theorem spin_xchg_live_sem_runner_concrete (fuel : Nat) : @XchgSpinLiveSemD spinLayoutV spinDeclsD fuel :=
  @spin_xchg_live_sem_runner spinLayoutV spinValidV spinDeclsD fuel

/-- `spin_xchg_live_oneShot_sem_runner` at the runner's layout and
declarations. No hypothesis left. -/
theorem spin_xchg_live_oneShot_sem_runner_concrete (fuel : Nat) :
    @XchgSpinLiveOneShotSemD spinLayoutV spinDeclsD fuel :=
  @spin_xchg_live_oneShot_sem_runner spinLayoutV spinValidV spinDeclsD fuel

/-- The runner's `N`-worker configuration satisfies `XchgStartD spinDeclsD`. -/
theorem xchgStartD_runnerN (N : Nat) :
    @XchgStartD spinLayoutV spinDeclsD (List.replicate N spinWorkerD0) spinInitMemV :=
  ⟨by show spinDeclsD.resolve _ 4 = _; rw [symV_lock]; rfl,
   by show spinDeclsD.resolve _ 4 = _; rw [symV_counter]; rfl,
   by rw [symV_lock, symV_counter]; decide,
   fun s hs => (List.eq_of_mem_replicate hs) ▸ spinWorkerD0_start,
   by rw [symV_lock]; simp only [Config.init_mem]; decide⟩

/-- **The runner's own configuration with promises, `N` workers**
(`spinlock2.kl`: `N = 2`, `spinlock3.kl`: `N = 3`): `N`
copies of the runner's prepared worker `spinWorkerD0` (declarations
`spinDeclsD` included), the runner's initial memory, at its layout, under
`WeakFairSem ∧ MemFair` (x86 `MemFair`: a modelling assumption). No
hypothesis left. -/
theorem spin_xchg_live_sem_runnerN (fuel N : Nat) :
    SpinSem.ProgressFromSem Arch.tso fuel (Config.init (List.replicate N spinWorkerD0) spinInitMemV)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg)
      (@SpinX64Xchg.XchgWaiting spinLayoutV) (@SpinX64Xchg.XchgDone spinLayoutV) :=
  spin_xchg_live_sem_runner_concrete fuel _ _ (xchgStartD_runnerN N)

/-- `spin_xchg_live_sem_runnerN` under a short name distinct from the existing
`Live.SpinX64SemXchgLive.spin_xchg_live_sem_runnerN` (`decls = {}`): the
runner's declarations `spinDeclsD` and workers `spinWorkerD0`. Additive
alias; same statement. -/
theorem spin_xchg_live_sem_runnerN_decls (fuel N : Nat) :
    SpinSem.ProgressFromSem Arch.tso fuel (Config.init (List.replicate N spinWorkerD0) spinInitMemV)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg)
      (@SpinX64Xchg.XchgWaiting spinLayoutV) (@SpinX64Xchg.XchgDone spinLayoutV) :=
  spin_xchg_live_sem_runnerN fuel N

/-- The one-shot per-thread form with promises at the runner's
configuration. No hypothesis left. -/
theorem spin_xchg_live_oneShot_sem_runnerN (fuel N : Nat) :
    LiveFromSem Arch.tso fuel (Config.init (List.replicate N spinWorkerD0) spinInitMemV)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg)
      (@SpinX64Xchg.XchgWaiting spinLayoutV) (@SpinX64Xchg.XchgDone spinLayoutV) :=
  spin_xchg_live_oneShot_sem_runner_concrete fuel _ _ (xchgStartD_runnerN N)

end Concrete

end Kraken.Promising.Live.RunnerSemX64Xchg

#print axioms Kraken.Promising.Live.RunnerSemX64Xchg.spin_xchg_live_sem_runner
#print axioms Kraken.Promising.Live.RunnerSemX64Xchg.spin_xchg_live_oneShot_sem_runner
#print axioms Kraken.Promising.Live.RunnerSemX64Xchg.spin_xchg_live_sem_runnerN
#print axioms Kraken.Promising.Live.RunnerSemX64Xchg.spin_xchg_live_sem_runnerN_decls
#print axioms Kraken.Promising.Live.RunnerSemX64Xchg.spin_xchg_live_oneShot_sem_runnerN
