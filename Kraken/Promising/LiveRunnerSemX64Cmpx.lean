/-
**Liveness of the x64 `lock cmpxchg` spinlock with promises in the runner's
declarations form.**

`Live.SpinX64SemCmpx.spin_cmpx_live_sem` (deadlock-freedom) and
`spin_cmpx_live_oneShot_sem` (per-thread, one-shot workers), on the machine
with semantic certification, are stated for workers with no declarations
(`SpinX64.CmpxStart`: `StartStateCV`, `decls = {}`). With the bridge of the
promise-free form (`LiveRunnerX64Spin`: `cmpxImageV_cellsDeclsAgree`,
`CmpxStartD`; `LiveRunnerX64.execSimD`) unchanged:

- **`spin_cmpx_live_sem_runner`** (`progressFromSem_transfer`) and
  `spin_cmpx_live_oneShot_sem_runner` (`liveFromSem_transfer`,
  `LiveRunnerSemSim`), under `Fair = WeakFairSem ∧ MemFair` (as the existing
  theorems; on x86 `MemFair` is a modelling assumption — store buffers drain
  in finite time, see `LiveTrace.lean`), from every `CmpxStartD ds`
  configuration (the same hypotheses as the promise-free
  `spin_cmpx_live_pf_runner`), along `State.noDecls`;
- `_runner_concrete` (the runner's layout `cmpxLayoutV` and declarations
  `cmpxDeclsD`) and `_runnerN` (`N` copies of `cmpxWorkerD0`, the runner's
  initial memory; no hypothesis left).
-/
import Kraken.Promising.LiveRunnerSemSim
import Kraken.Promising.LiveRunnerX64Spin
import Kraken.Promising.LiveSpinX64SemCmpx

namespace Kraken.Promising.Live.RunnerSemX64Cmpx

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.Sem Kraken.Promising.Live.RunnerSemSim
open Kraken.Promising.Live.RunnerX64 Kraken.Promising.Live.RunnerX64Spin
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV symC)

section Generic

variable [layout : _root_.Layout]

/-- **`lock cmpxchg` spinlock deadlock-freedom with promises and
declarations `ds`** (`SpinX64Sem.CmpxSpinLiveSem` at `CmpxStartD ds`;
`Fair = WeakFairSem ∧ MemFair`). -/
def CmpxSpinLiveSemD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ states initMem, CmpxStartD ds states initMem →
    SpinSem.ProgressFromSem Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) SpinX64.CmpxWaiting SpinX64.CmpxDone

/-- **Per-thread liveness of the one-shot `lock cmpxchg` workers with
promises and declarations `ds`** (`SpinX64Sem.CmpxSpinLiveOneShotSem` at
`CmpxStartD ds`). -/
def CmpxSpinLiveOneShotSemD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ states initMem, CmpxStartD ds states initMem →
    LiveFromSem Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) SpinX64.CmpxWaiting SpinX64.CmpxDone

/-- `CmpxStartD ds` maps along `State.noDecls` to the existing `CmpxStart`. -/
theorem cmpxStart_noDecls {ds : Decls} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : CmpxStartD ds states initMem) :
    SpinX64.CmpxStart (states.map State.noDecls) initMem :=
  ⟨hs.hlc, fun s h => by
    obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
    have h'' := hs.hst s' h'
    exact ⟨h''.exe, rfl, h''.pc, h''.endPc, h''.split⟩, hs.hL0⟩

/-- **Deadlock-freedom of the x64 `lock cmpxchg` spinlock with promises and
the runner's declarations** (Stage 3, semantic certification;
`spinlock_cmpxchg2/3.kl` verbatim): on a valid layout of `cmpxImageV`, for
every `ds` that resolves `lock` and `counter` (4 bytes) to themselves, on
every `TraceSem` `Arch.tso` trace from a `CmpxStartD ds` configuration under
`WeakFairSem ∧ MemFair` (x86 `MemFair`: a modelling assumption), if a thread
waits in its acquire loop, then some thread not yet past its release later
is. `spin_cmpx_live_sem` transferred along `State.noDecls`
(`progressFromSem_transfer`, `execSimD`). -/
theorem spin_cmpx_live_sem_runner [Executable.ValidLayout (layout cmpxImageV)] (ds : Decls) (fuel : Nat) :
    CmpxSpinLiveSemD ds fuel := by
  intro states initMem hs
  refine progressFromSem_transfer (execSimD (cmpxImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodS_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  rw [mapC_init]
  exact SpinX64SemCmpx.spin_cmpx_live_sem fuel _ initMem (cmpxStart_noDecls hs)

/-- **Per-thread liveness of the one-shot x64 `lock cmpxchg` workers with
promises and the runner's declarations** (one-shot workers, not
starvation-freedom of the lock; `Fair = WeakFairSem ∧ MemFair`, x86
`MemFair` a modelling assumption): `spin_cmpx_live_oneShot_sem` transferred
along `State.noDecls` (`liveFromSem_transfer`). -/
theorem spin_cmpx_live_oneShot_sem_runner [Executable.ValidLayout (layout cmpxImageV)] (ds : Decls)
    (fuel : Nat) : CmpxSpinLiveOneShotSemD ds fuel := by
  intro states initMem hs
  refine liveFromSem_transfer (execSimD (cmpxImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodS_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  rw [mapC_init]
  exact SpinX64SemCmpx.spin_cmpx_live_oneShot_sem fuel _ initMem (cmpxStart_noDecls hs)

end Generic

/-! ## The runner's configuration -/

section Concrete

open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete
attribute [local instance] cmpxLayoutV

/-- `spin_cmpx_live_sem_runner` at the runner's layout `cmpxLayoutV` and
declarations `cmpxDeclsD`. No hypothesis left. -/
theorem spin_cmpx_live_sem_runner_concrete (fuel : Nat) : @CmpxSpinLiveSemD cmpxLayoutV cmpxDeclsD fuel :=
  @spin_cmpx_live_sem_runner cmpxLayoutV cmpxValidV cmpxDeclsD fuel

/-- `spin_cmpx_live_oneShot_sem_runner` at the runner's layout and
declarations. No hypothesis left. -/
theorem spin_cmpx_live_oneShot_sem_runner_concrete (fuel : Nat) :
    @CmpxSpinLiveOneShotSemD cmpxLayoutV cmpxDeclsD fuel :=
  @spin_cmpx_live_oneShot_sem_runner cmpxLayoutV cmpxValidV cmpxDeclsD fuel

/-- The runner's `N`-worker configuration satisfies `CmpxStartD cmpxDeclsD`. -/
theorem cmpxStartD_runnerN (N : Nat) :
    @CmpxStartD cmpxLayoutV cmpxDeclsD (List.replicate N cmpxWorkerD0) cmpxInitMemV :=
  ⟨by show cmpxDeclsD.resolve _ 4 = _; rw [symC_lock]; rfl,
   by show cmpxDeclsD.resolve _ 4 = _; rw [symC_counter]; rfl,
   by rw [symC_lock, symC_counter]; decide,
   fun s hs => (List.eq_of_mem_replicate hs) ▸ cmpxWorkerD0_start,
   by rw [symC_lock]; simp only [Config.init_mem]; decide⟩

/-- **The runner's own configuration with promises, `N` workers**
(`spinlock_cmpxchg2.kl`: `N = 2`, `spinlock_cmpxchg3.kl`: `N = 3`): `N`
copies of the runner's prepared worker `cmpxWorkerD0` (declarations
`cmpxDeclsD` included), the runner's initial memory, at its layout, under
`WeakFairSem ∧ MemFair` (x86 `MemFair`: a modelling assumption). No
hypothesis left. -/
theorem spin_cmpx_live_sem_runnerN (fuel N : Nat) :
    SpinSem.ProgressFromSem Arch.tso fuel (Config.init (List.replicate N cmpxWorkerD0) cmpxInitMemV)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg)
      (@SpinX64.CmpxWaiting cmpxLayoutV) (@SpinX64.CmpxDone cmpxLayoutV) :=
  spin_cmpx_live_sem_runner_concrete fuel _ _ (cmpxStartD_runnerN N)

/-- The one-shot per-thread form with promises at the runner's
configuration. No hypothesis left. -/
theorem spin_cmpx_live_oneShot_sem_runnerN (fuel N : Nat) :
    LiveFromSem Arch.tso fuel (Config.init (List.replicate N cmpxWorkerD0) cmpxInitMemV)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg)
      (@SpinX64.CmpxWaiting cmpxLayoutV) (@SpinX64.CmpxDone cmpxLayoutV) :=
  spin_cmpx_live_oneShot_sem_runner_concrete fuel _ _ (cmpxStartD_runnerN N)

end Concrete

end Kraken.Promising.Live.RunnerSemX64Cmpx

#print axioms Kraken.Promising.Live.RunnerSemX64Cmpx.spin_cmpx_live_sem_runner
#print axioms Kraken.Promising.Live.RunnerSemX64Cmpx.spin_cmpx_live_oneShot_sem_runner
#print axioms Kraken.Promising.Live.RunnerSemX64Cmpx.spin_cmpx_live_sem_runnerN
#print axioms Kraken.Promising.Live.RunnerSemX64Cmpx.spin_cmpx_live_oneShot_sem_runnerN
