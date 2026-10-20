/-
**Liveness of the AArch64 CAS spinlock with promises in the runner's
declarations form.**

`Live.SpinSemCas.spin_cas_live_sem` (deadlock-freedom) and
`spin_cas_live_oneShot_sem` (per-thread, one-shot workers), on the machine
with semantic certification, are stated for threads with no declarations
(`Spin.CasStart`, `decls = {}`). With the bridge of the promise-free form
(`LiveRunnerA64Cas`: `SCas`, `stepOK_cas`, `CasStartD`, `casStart_noDecls`,
`casStartD_runner`; `execSimA`) unchanged:

- **`spin_cas_live_sem_runner`** (`progressFromSem_transfer`) and
  `spin_cas_live_oneShot_sem_runner` (`liveFromSem_transfer`), under
  `Fair = WeakFairSem ∧ MemFair` (as the existing theorems), from every
  `CasStartD ds` configuration (the same hypotheses as the promise-free
  `spin_cas_live_pf_runner`);
- `_runner_concrete` (the runner's layout `ConcreteCas.casLayout`) and
  `_runnerN` (`N` copies of `casWorkerD0`, the runner's initial memory; no
  hypothesis left).

Memory fairness `MemFair`: AArch64 basis Arm ARM B2.7.1 (see `MemFair`).
-/
import Kraken.Promising.LiveRunnerSemSim
import Kraken.Promising.LiveRunnerA64Cas
import Kraken.Promising.LiveSpinSemCas

namespace Kraken.Promising.Live.RunnerSemA64Cas

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.Sem Kraken.Promising.Live.RunnerSemSim
open Kraken.Promising.Live.RunnerA64 Kraken.Promising.Live.RunnerA64Cas
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker casTtasWorker_noPairs)

section Generic

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

/-- **CAS-spinlock deadlock-freedom with promises and declarations `ds`**
(`SpinSem.CasSpinLiveSem` at `CasStartD ds`; `Fair = WeakFairSem ∧
MemFair`). -/
def CasSpinLiveSemD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ l c states initMem, CasStartD ds l c states initMem →
    SpinSem.ProgressFromSem Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) Spin.CasWaiting Spin.CasDone

/-- **Per-thread liveness of the one-shot CAS workers with promises and
declarations `ds`** (`SpinSem.CasSpinLiveOneShotSem` at `CasStartD ds`). -/
def CasSpinLiveOneShotSemD (ds : Decls) (fuel : Nat) : Prop :=
  ∀ l c states initMem, CasStartD ds l c states initMem →
    LiveFromSem Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) Spin.CasWaiting Spin.CasDone

/-- **Deadlock-freedom of the AArch64 CAS spinlock with promises and the
runner's declarations** (Stage 3, semantic certification): on a valid layout
of `casTtasWorker`, for every `ds` that resolves the lock and counter words
to themselves, on every `TraceSem` `Arch.armv8` trace from a `CasStartD ds`
configuration under `WeakFairSem ∧ MemFair`, if a thread waits in its
try/spin loop, then some thread not yet past its release later is.
`spin_cas_live_sem` transferred along `State.noDecls`
(`progressFromSem_transfer`, `execSimA`). -/
theorem spin_cas_live_sem_runner (ds : Decls) (fuel : Nat) : CasSpinLiveSemD ds fuel := by
  intro l c states initMem hs
  refine progressFromSem_transfer (execSimA casTtasWorker_noPairs (stepOK_cas hs.agL hs.agC))
    (goodS_init initMem fun s h => ⟨(hs.hst s h).1, sCas_of_start (hs.hst s h).2⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact SpinSemCas.spin_cas_live_sem fuel l c _ initMem (casStart_noDecls hs)

/-- **Per-thread liveness of the one-shot CAS workers with promises and the
runner's declarations** (one-shot workers, not starvation-freedom of the
lock): `spin_cas_live_oneShot_sem` transferred along `State.noDecls`
(`liveFromSem_transfer`). -/
theorem spin_cas_live_oneShot_sem_runner (ds : Decls) (fuel : Nat) : CasSpinLiveOneShotSemD ds fuel := by
  intro l c states initMem hs
  refine liveFromSem_transfer (execSimA casTtasWorker_noPairs (stepOK_cas hs.agL hs.agC))
    (goodS_init initMem fun s h => ⟨(hs.hst s h).1, sCas_of_start (hs.hst s h).2⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact SpinSemCas.spin_cas_live_oneShot_sem fuel l c _ initMem (casStart_noDecls hs)

end Generic

/-! ## The runner's configuration -/

section Concrete

open Kraken.Promising.SLR.EnvG.ConcreteCas (casLayout casValid casInitMem casDeclsD casWorkerD0)
attribute [local instance] casLayout

/-- `spin_cas_live_sem_runner` at the runner's layout `ConcreteCas.casLayout`.
No hypothesis left. -/
theorem spin_cas_live_sem_runner_concrete (ds : Decls) (fuel : Nat) : @CasSpinLiveSemD casLayout ds fuel :=
  @spin_cas_live_sem_runner casLayout casValid ds fuel

/-- `spin_cas_live_oneShot_sem_runner` at the runner's layout. -/
theorem spin_cas_live_oneShot_sem_runner_concrete (ds : Decls) (fuel : Nat) :
    @CasSpinLiveOneShotSemD casLayout ds fuel :=
  @spin_cas_live_oneShot_sem_runner casLayout casValid ds fuel

/-- **The runner's own configuration with promises, `N` workers**
(`spinlock_cas2.kl`: `N = 2`, `spinlock_cas3.kl`: `N = 3`): `N` copies of the
runner's prepared worker `casWorkerD0` (declarations `casDeclsD` included),
the runner's initial memory, at its layout, under `WeakFairSem ∧ MemFair`.
No hypothesis left. -/
theorem spin_cas_live_sem_runnerN (fuel N : Nat) :
    SpinSem.ProgressFromSem Arch.armv8 fuel (Config.init (List.replicate N casWorkerD0) casInitMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg)
      (@Spin.CasWaiting casLayout) (@Spin.CasDone casLayout) :=
  spin_cas_live_sem_runner_concrete casDeclsD fuel _ _ _ _ (casStartD_runner N)

/-- The one-shot per-thread form with promises at the runner's
configuration. No hypothesis left. -/
theorem spin_cas_live_oneShot_sem_runnerN (fuel N : Nat) :
    LiveFromSem Arch.armv8 fuel (Config.init (List.replicate N casWorkerD0) casInitMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg)
      (@Spin.CasWaiting casLayout) (@Spin.CasDone casLayout) :=
  spin_cas_live_oneShot_sem_runner_concrete casDeclsD fuel _ _ _ _ (casStartD_runner N)

end Concrete

end Kraken.Promising.Live.RunnerSemA64Cas

#print axioms Kraken.Promising.Live.RunnerSemA64Cas.spin_cas_live_sem_runner
#print axioms Kraken.Promising.Live.RunnerSemA64Cas.spin_cas_live_sem_runnerN
#print axioms Kraken.Promising.Live.RunnerSemA64Cas.spin_cas_live_oneShot_sem_runnerN
