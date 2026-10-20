/-
**Liveness of the AArch64 SWP spinlocks with promises in the runner's
declarations form.**

`Live.SpinSemSwpLive.spin_swp(l)_live_sem` (deadlock-freedom) and
`spin_swp(l)_live_oneShot_sem` (per-thread, one-shot workers), on the machine
with semantic certification, are stated for threads with no declarations
(`SpinSwp.SwpStartG`, `decls = {}`). With the bridge of the promise-free form
(`LiveRunnerA64Swp`: `SSwp`, `stepOK_swp`, `sSwp_of_start`, `SwpStartGD`,
`swpStart_noDecls`, `swp(l)StartGD_runner`; `execSimA`) unchanged,
generically in the program (`SpinSwpTrees.SwpCode P`):

- `swp_live_sem_runner_gen` / `swp_live_oneShot_sem_runner_gen`: any
  `SpinSemSwp.SwpLiveSemUnderG` / `SwpOneShotSemUnderG` statement at
  `decls = {}` transfers (`progressFromSem_transfer` /
  `liveFromSem_transfer`, `LiveRunnerSemSim`);
- **`spin_swp_live_sem_runner`**, **`spin_swpl_live_sem_runner`** and the
  one-shot forms, under `Fair = WeakFairSem ∧ MemFair` (as the existing
  theorems), from every `SwpStartGD ds` configuration (the same hypotheses
  as the promise-free `spin_swp(l)_live_pf_runner`), with `_runner_concrete`
  (the runner's layouts) and `_runnerN` (`N` copies of `swpWorkerD0` /
  `swplWorkerD0`, the runner's initial memory; no hypothesis left).

Memory fairness `MemFair`: AArch64 basis Arm ARM B2.7.1 (see `MemFair`).
-/
import Kraken.Promising.LiveRunnerSemSim
import Kraken.Promising.LiveRunnerA64Swp
import Kraken.Promising.LiveSpinSemSwpLive

namespace Kraken.Promising.Live.RunnerSemA64Swp

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.Live.Sem Kraken.Promising.Live.RunnerSemSim
open Kraken.Promising.Live.RunnerA64 Kraken.Promising.Live.RunnerA64Swp
open Kraken.Promising.Live.SpinSwpTrees Kraken.Promising.Live.SpinSwp
open Kraken.Promising.Live.SpinSemSwp (FairSem SwpLiveSemUnderG SwpOneShotSemUnderG)
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.EnvG.SwplLock (swplWorker)

section Generic

variable [layout : _root_.Layout] {P : Program} [hv : Executable.ValidLayout (layout P)]

/-- `SpinSemSwp.SwpLiveSemUnderG` (with promises, `Fair = WeakFairSem ∧
MemFair`) at `SwpStartGD ds`. -/
def SwpLiveSemUnderGD (P : Program) (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (ds : Decls)
    (fuel : Nat) : Prop :=
  ∀ l c states initMem, SwpStartGD ds Start l c states initMem →
    SpinSem.ProgressFromSem Arch.armv8 fuel (Config.init states initMem) (FairSem fuel) (SwpWaitingG P)
      (SwpDoneG P)

/-- `SpinSemSwp.SwpOneShotSemUnderG` (with promises) at `SwpStartGD ds`. -/
def SwpOneShotSemUnderGD (P : Program) (Start : BitVec 64 → BitVec 64 → isa.State → Prop) (ds : Decls)
    (fuel : Nat) : Prop :=
  ∀ l c states initMem, SwpStartGD ds Start l c states initMem →
    LiveFromSem Arch.armv8 fuel (Config.init states initMem) (FairSem fuel) (SwpWaitingG P) (SwpDoneG P)

/-- **Generic transfer with promises, deadlock-freedom**: for an
SWP-spinlock program `P` without `LDXP`/`STXP` whose start states are
`StartG` states, a with-promises `SwpLiveSemUnderG` statement at
`decls = {}` holds at every `ds` agreeing at the two words. -/
theorem swp_live_sem_runner_gen (hC : SwpCode P) (hnp : Kraken.Executable.noPairs (layout P) = true)
    {Start : BitVec 64 → BitVec 64 → isa.State → Prop} (hStart : ∀ l c s, Start l c s → StartG P l c s)
    {fuel : Nat} (h : SwpLiveSemUnderG P Start fuel) (ds : Decls) : SwpLiveSemUnderGD P Start ds fuel := by
  intro l c states initMem hs
  refine progressFromSem_transfer (execSimA hnp (stepOK_swp hC hs.agL hs.agC))
    (goodS_init initMem fun s h' => ⟨(hs.hst s h').1, sSwp_of_start hC (hStart _ _ _ (hs.hst s h').2)⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact h l c _ initMem (swpStart_noDecls hs)

/-- **Generic transfer with promises, one-shot per-thread liveness.** -/
theorem swp_live_oneShot_sem_runner_gen (hC : SwpCode P) (hnp : Kraken.Executable.noPairs (layout P) = true)
    {Start : BitVec 64 → BitVec 64 → isa.State → Prop} (hStart : ∀ l c s, Start l c s → StartG P l c s)
    {fuel : Nat} (h : SwpOneShotSemUnderG P Start fuel) (ds : Decls) : SwpOneShotSemUnderGD P Start ds fuel := by
  intro l c states initMem hs
  refine liveFromSem_transfer (execSimA hnp (stepOK_swp hC hs.agL hs.agC))
    (goodS_init initMem fun s h' => ⟨(hs.hst s h').1, sSwp_of_start hC (hStart _ _ _ (hs.hst s h').2)⟩)
    (fun _ _ => exists_mapC _ _ _ _) (fun _ _ => exists_mapC _ _ _ _) ?_
  erw [mapC_init]
  exact h l c _ initMem (swpStart_noDecls hs)

end Generic

/-! ## The two locks -/

section Locks

variable [layout : _root_.Layout]

/-- **Deadlock-freedom of the SWP spinlock (`SWPA`/`STLR`) with promises
and the runner's declarations** (Stage 3, semantic certification): on a
valid layout of `swpWorker`, for every `ds` that resolves the lock and
counter words to themselves, on every `TraceSem` trace from a
`SwpStartGD ds SwpPublic.StartState` configuration under
`WeakFairSem ∧ MemFair`, if a thread waits in its try/spin loop, then some
thread not yet past its release later is. `spin_swp_live_sem` transferred
along `State.noDecls`. -/
theorem spin_swp_live_sem_runner [Executable.ValidLayout (layout swpWorker)] (ds : Decls) (fuel : Nat) :
    SwpLiveSemUnderGD swpWorker SLR.SwpPublic.StartState ds fuel :=
  swp_live_sem_runner_gen swpCode SLR.EnvG.SwpEnvG.swpWorker_noPairs (fun _ _ _ => SpinSwpFam.startG_swp)
    (SpinSemSwpLive.spin_swp_live_sem fuel) ds

/-- One-shot per-thread liveness of the SWP workers with promises and the
runner's declarations (not starvation-freedom of the lock). -/
theorem spin_swp_live_oneShot_sem_runner [Executable.ValidLayout (layout swpWorker)] (ds : Decls) (fuel : Nat) :
    SwpOneShotSemUnderGD swpWorker SLR.SwpPublic.StartState ds fuel :=
  swp_live_oneShot_sem_runner_gen swpCode SLR.EnvG.SwpEnvG.swpWorker_noPairs
    (fun _ _ _ => SpinSwpFam.startG_swp) (SpinSemSwpLive.spin_swp_live_oneShot_sem fuel) ds

/-- **Deadlock-freedom of the SWPL spinlock (`SWPA`/`SWPL`) with promises
and the runner's declarations** (Stage 3, semantic certification), on a
valid layout of `swplWorker`, for every `ds` agreeing at the two words,
under `WeakFairSem ∧ MemFair`. `spin_swpl_live_sem` transferred along
`State.noDecls`. -/
theorem spin_swpl_live_sem_runner [Executable.ValidLayout (layout swplWorker)] (ds : Decls) (fuel : Nat) :
    SwpLiveSemUnderGD swplWorker SLR.EnvG.SwplLock.StartState ds fuel :=
  swp_live_sem_runner_gen swplCode SLR.EnvG.SwplLock.swplWorker_noPairs (fun _ _ _ => SpinSwpFam.startG_swpl)
    (SpinSemSwpLive.spin_swpl_live_sem fuel) ds

/-- One-shot per-thread liveness of the SWPL workers with promises and the
runner's declarations (not starvation-freedom of the lock). -/
theorem spin_swpl_live_oneShot_sem_runner [Executable.ValidLayout (layout swplWorker)] (ds : Decls) (fuel : Nat) :
    SwpOneShotSemUnderGD swplWorker SLR.EnvG.SwplLock.StartState ds fuel :=
  swp_live_oneShot_sem_runner_gen swplCode SLR.EnvG.SwplLock.swplWorker_noPairs
    (fun _ _ _ => SpinSwpFam.startG_swpl) (SpinSemSwpLive.spin_swpl_live_oneShot_sem fuel) ds

end Locks

/-! ## The runner's configurations -/

section ConcreteSwp

open Kraken.Promising.SLR.SwpConcrete (swpLayout swpValid initMem2)
open Kraken.Promising.SLR.EnvG.A64SwpRunner (swpDeclsD swpWorkerD0)
attribute [local instance] swpLayout

/-- `spin_swp_live_sem_runner` at the runner's layout `SwpConcrete.swpLayout`.
No hypothesis left. -/
theorem spin_swp_live_sem_runner_concrete (ds : Decls) (fuel : Nat) :
    @SwpLiveSemUnderGD swpLayout swpWorker SLR.SwpPublic.StartState ds fuel :=
  @spin_swp_live_sem_runner swpLayout swpValid ds fuel

/-- `spin_swp_live_oneShot_sem_runner` at the runner's layout. -/
theorem spin_swp_live_oneShot_sem_runner_concrete (ds : Decls) (fuel : Nat) :
    @SwpOneShotSemUnderGD swpLayout swpWorker SLR.SwpPublic.StartState ds fuel :=
  @spin_swp_live_oneShot_sem_runner swpLayout swpValid ds fuel

/-- **The runner's own configuration with promises, `N` workers**
(`spinlock_swp2.kl`: `N = 2`, `spinlock_swp3.kl`: `N = 3`): `N` copies of
`swpWorkerD0` (declarations `swpDeclsD` included), the runner's initial
memory, at its layout, under `WeakFairSem ∧ MemFair`. No hypothesis left. -/
theorem spin_swp_live_sem_runnerN (fuel N : Nat) :
    SpinSem.ProgressFromSem Arch.armv8 fuel (Config.init (List.replicate N swpWorkerD0) initMem2) (FairSem fuel)
      (@SwpWaitingG swpLayout swpWorker) (@SwpDoneG swpLayout swpWorker) :=
  spin_swp_live_sem_runner_concrete swpDeclsD fuel _ _ _ _ (swpStartGD_runner N)

/-- The one-shot per-thread form with promises at the runner's
configuration. -/
theorem spin_swp_live_oneShot_sem_runnerN (fuel N : Nat) :
    LiveFromSem Arch.armv8 fuel (Config.init (List.replicate N swpWorkerD0) initMem2) (FairSem fuel)
      (@SwpWaitingG swpLayout swpWorker) (@SwpDoneG swpLayout swpWorker) :=
  spin_swp_live_oneShot_sem_runner_concrete swpDeclsD fuel _ _ _ _ (swpStartGD_runner N)

end ConcreteSwp

section ConcreteSwpl

open Kraken.Promising.SLR.EnvG.ConcreteSwpl (swplLayout swplValid swplInitMem swplDeclsD swplWorkerD0)
attribute [local instance] swplLayout

/-- `spin_swpl_live_sem_runner` at the runner's layout
`ConcreteSwpl.swplLayout`. No hypothesis left. -/
theorem spin_swpl_live_sem_runner_concrete (ds : Decls) (fuel : Nat) :
    @SwpLiveSemUnderGD swplLayout swplWorker SLR.EnvG.SwplLock.StartState ds fuel :=
  @spin_swpl_live_sem_runner swplLayout swplValid ds fuel

/-- `spin_swpl_live_oneShot_sem_runner` at the runner's layout. -/
theorem spin_swpl_live_oneShot_sem_runner_concrete (ds : Decls) (fuel : Nat) :
    @SwpOneShotSemUnderGD swplLayout swplWorker SLR.EnvG.SwplLock.StartState ds fuel :=
  @spin_swpl_live_oneShot_sem_runner swplLayout swplValid ds fuel

/-- **The runner's own configuration with promises, `N` workers**
(`spinlock_swpl2.kl`: `N = 2`, `spinlock_swpl3.kl`: `N = 3`): `N` copies of
`swplWorkerD0` (declarations `swplDeclsD` included), the runner's initial
memory, at its layout, under `WeakFairSem ∧ MemFair`. No hypothesis left. -/
theorem spin_swpl_live_sem_runnerN (fuel N : Nat) :
    SpinSem.ProgressFromSem Arch.armv8 fuel (Config.init (List.replicate N swplWorkerD0) swplInitMem)
      (FairSem fuel) (@SwpWaitingG swplLayout swplWorker) (@SwpDoneG swplLayout swplWorker) :=
  spin_swpl_live_sem_runner_concrete swplDeclsD fuel _ _ _ _ (swplStartGD_runner N)

/-- The one-shot per-thread form with promises at the runner's
configuration. -/
theorem spin_swpl_live_oneShot_sem_runnerN (fuel N : Nat) :
    LiveFromSem Arch.armv8 fuel (Config.init (List.replicate N swplWorkerD0) swplInitMem) (FairSem fuel)
      (@SwpWaitingG swplLayout swplWorker) (@SwpDoneG swplLayout swplWorker) :=
  spin_swpl_live_oneShot_sem_runner_concrete swplDeclsD fuel _ _ _ _ (swplStartGD_runner N)

end ConcreteSwpl

end Kraken.Promising.Live.RunnerSemA64Swp

#print axioms Kraken.Promising.Live.RunnerSemA64Swp.spin_swp_live_sem_runnerN
#print axioms Kraken.Promising.Live.RunnerSemA64Swp.spin_swp_live_oneShot_sem_runnerN
#print axioms Kraken.Promising.Live.RunnerSemA64Swp.spin_swpl_live_sem_runnerN
#print axioms Kraken.Promising.Live.RunnerSemA64Swp.spin_swpl_live_oneShot_sem_runnerN
