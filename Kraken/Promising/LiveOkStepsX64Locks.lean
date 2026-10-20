/-
**x64 lock corollaries: N1′ with no hypothesis.** The x64 counterpart of
`LiveOkStepsA64Locks.lean`: the
semantic fault-freedom twins (`ChainK/SemTwinsX64.lean`) of the four x64
locks at the `.kl` runner's layouts.
-/
import Kraken.Promising.LiveOkStepsX64
import Kraken.Promising.SLR.ChainK.SemTwinsX64

namespace Kraken.Promising.Live.NoStuck

open Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge
  Kraken.Promising.X64.EnvG

/-- N1′ for the `xchg` spinlock (`x64_spin_counter_envG_runner_faultFree_sem_concreteN`). -/
theorem spin_x64_stuckHasDeadPromise_concreteN (N : Nat) {A : Arch} {fuel : Nat} {c : Config isa}
    (hr : ReachableSem A fuel (Config.init (List.replicate N SpinAbs.Concrete.spinWorkerD0) SpinAbs.Concrete.spinInitMemV) c)
    (hst : StuckSem A fuel c) : DeadPromiseIn A fuel c :=
  stuckHasDeadPromise_init (SpinAbs.Concrete.x64_spin_counter_envG_runner_faultFree_sem_concreteN N) hr hst

/-- N1′ for the `cmpxchg` spinlock (`x64_cmpx_counter_envG_runner_faultFree_sem_concreteN`). -/
theorem cmpx_x64_stuckHasDeadPromise_concreteN (N : Nat) {A : Arch} {fuel : Nat} {c : Config isa}
    (hr : ReachableSem A fuel (Config.init (List.replicate N CmpxAbs.Concrete.cmpxWorkerD0) CmpxAbs.Concrete.cmpxInitMemV) c)
    (hst : StuckSem A fuel c) : DeadPromiseIn A fuel c :=
  stuckHasDeadPromise_init (CmpxAbs.Concrete.x64_cmpx_counter_envG_runner_faultFree_sem_concreteN N) hr hst

/-- N1′ for the two-word ticket lock (`ticket2_counter_envG_runner_faultFree_sem_concreteN`). -/
theorem ticket2_x64_stuckHasDeadPromise_concreteN (N : Nat) {A : Arch} {fuel : Nat} {c : Config isa}
    (hr : ReachableSem A fuel (Config.init (List.replicate N TicketX2.Concrete.tk2WorkerD0) TicketX2.Concrete.tk2InitMemV) c)
    (hst : StuckSem A fuel c) : DeadPromiseIn A fuel c :=
  stuckHasDeadPromise_init (TicketX2.Concrete.ticket2_counter_envG_runner_faultFree_sem_concreteN N) hr hst

/-- N1′ for the three-instruction ticket lock
(`ticket3_counter_envG_runner_faultFree_sem_concreteN`, which needs `N + 1 < 2^32`). -/
theorem ticket3_x64_stuckHasDeadPromise_concreteN (N : Nat) (hN : N + 1 < 2 ^ 32) {A : Arch} {fuel : Nat}
    {c : Config isa}
    (hr : ReachableSem A fuel (Config.init (List.replicate N TicketX.Concrete.tk3WorkerD0) TicketX.Concrete.tk3InitMemV) c)
    (hst : StuckSem A fuel c) : DeadPromiseIn A fuel c :=
  stuckHasDeadPromise_init (TicketX.Concrete.ticket3_counter_envG_runner_faultFree_sem_concreteN N hN) hr hst

end Kraken.Promising.Live.NoStuck
