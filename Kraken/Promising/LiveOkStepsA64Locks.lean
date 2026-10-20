/-
**AArch64 lock corollaries: N1′ with no hypothesis.**

`stuckHasDeadPromise_init` (`LiveOkSteps.lean`) at the semantic fault-freedom
twins (`ChainK/SemTwinsA64.lean`) of the AArch64 locks at the `.kl`
runner's layouts, for any `N` workers, any `Arch` and any `fuel`: every stuck
configuration reachable on the semantic machine has a thread with an
outstanding promise that it cannot fulfil alone. Every other program with a
`*_faultFree_sem*` twin gets the same by the same one-liner.
-/
import Kraken.Promising.LiveOkStepsA64
import Kraken.Promising.SLR.ChainK.SemTwinsA64

namespace Kraken.Promising.Live.NoStuck

open Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge
  Kraken.Promising.SLR.EnvG

/-- N1′ for the SWP spinlock (`swp_counter_envG_runner_faultFree_sem_concreteN`). -/
theorem swp_stuckHasDeadPromise_concreteN (N : Nat) {A : Arch} {fuel : Nat} {c : Config isa}
    (hr : ReachableSem A fuel (Config.init (List.replicate N A64SwpRunner.swpWorkerD0) SLR.SwpConcrete.initMem2) c)
    (hst : StuckSem A fuel c) : DeadPromiseIn A fuel c :=
  stuckHasDeadPromise_init (A64SwpRunner.swp_counter_envG_runner_faultFree_sem_concreteN N) hr hst

/-- N1′ for the CAS spinlock (`cas_counter_envG_runner_faultFree_sem_concreteN`). -/
theorem cas_stuckHasDeadPromise_concreteN (N : Nat) {A : Arch} {fuel : Nat} {c : Config isa}
    (hr : ReachableSem A fuel (Config.init (List.replicate N ConcreteCas.casWorkerD0) ConcreteCas.casInitMem) c)
    (hst : StuckSem A fuel c) : DeadPromiseIn A fuel c :=
  stuckHasDeadPromise_init (ConcreteCas.cas_counter_envG_runner_faultFree_sem_concreteN N) hr hst

/-- N1′ for the SWPL spinlock (`swpl_counter_envG_runner_faultFree_sem_concreteN`). -/
theorem swpl_stuckHasDeadPromise_concreteN (N : Nat) {A : Arch} {fuel : Nat} {c : Config isa}
    (hr : ReachableSem A fuel (Config.init (List.replicate N ConcreteSwpl.swplWorkerD0) ConcreteSwpl.swplInitMem) c)
    (hst : StuckSem A fuel c) : DeadPromiseIn A fuel c :=
  stuckHasDeadPromise_init (ConcreteSwpl.swpl_counter_envG_runner_faultFree_sem_concreteN N) hr hst

/-- N1′ for the ticket lock (`ticket_counter_envG_runner_faultFree_sem_concreteN`). -/
theorem ticket_stuckHasDeadPromise_concreteN (N : Nat) {A : Arch} {fuel : Nat} {c : Config isa}
    (hr : ReachableSem A fuel (Config.init (List.replicate N ConcreteTicketD.tkWorkerD0) ConcreteTicketAl.tkAlInitMem) c)
    (hst : StuckSem A fuel c) : DeadPromiseIn A fuel c :=
  stuckHasDeadPromise_init (ConcreteTicketD.ticket_counter_envG_runner_faultFree_sem_concreteN N) hr hst

/-- N1′ for the acquire-load ticket lock
(`ticket_al_counter_envG_runner_faultFree_sem_concreteN`). -/
theorem ticket_al_stuckHasDeadPromise_concreteN (N : Nat) {A : Arch} {fuel : Nat} {c : Config isa}
    (hr : ReachableSem A fuel (Config.init (List.replicate N ConcreteTicketAl.tkAlWorkerD0) ConcreteTicketAl.tkAlInitMem) c)
    (hst : StuckSem A fuel c) : DeadPromiseIn A fuel c :=
  stuckHasDeadPromise_init (ConcreteTicketD.ticket_al_counter_envG_runner_faultFree_sem_concreteN N) hr hst

end Kraken.Promising.Live.NoStuck
