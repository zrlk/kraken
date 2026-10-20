/-
**Liveness of the AArch64 `ldaddal` ticket lock with promises in the runner's
declarations form.** Semantic machine
(`CertOkN`/`TraceSem`, `WeakFairSem ∧ MemFair`).

`LiveRunnerSemA64Ticket.lean` re-elaborated at `tkWorkerAl` by the clone
command of `LiveTicketAlClone.lean`. Namespace `Live.RunnerSemA64TicketAl`:
`TicketAlLiveSemD ds fuel` (`TicketAlSem.TicketAlLiveSem` at
`RunnerA64TicketAl.TkStartAlD ds`); **`ticket_al_live_sem_runner`** (by
`liveFromSem_transfer`/`execSimA`, `LiveRunnerSemSim`, from
`TicketAlSem.ticket_al_live_sem`), `ticket_al_live_sem_runner_concrete`
(layout `ConcreteTicketAl.tkAlLayout`) and `ticket_al_live_sem_runnerN` (`N`
copies of `tkAlWorkerD0`; only `N + 1 < 2 ^ 32` left).
-/
import Kraken.Promising.LiveTicketAlClone
import Kraken.Promising.LiveTicketAlSem
import Kraken.Promising.LiveRunnerA64TicketAl
import Kraken.Promising.LiveRunnerSemA64Ticket

#ticket_al_clone "LiveRunnerSemA64Ticket.lean" with ["RunnerA64Ticket" => "RunnerA64TicketAl", "RunnerSemA64Ticket" => "RunnerSemA64TicketAl",
  "ConcreteTicketD" => "ConcreteTicketAl", "tkDeclsD" => "Kraken.Promising.SLR.EnvG.ConcreteTicketD.tkDeclsD",
  "tkLayoutD" => "tkAlLayout", "tkValidD" => "tkAlValid", "tkWorkerD0" => "tkAlWorkerD0",
  "tkWorker0_start" => "tkAlWorker0_start", "tkWorker_noPairs" => "tkWorkerAl_noPairs",
  "TkStartD" => "TkStartAlD", "TicketLivePFD" => "TicketAlLivePFD", "TicketLiveSemD" => "TicketAlLiveSemD",
  "ticket_live_pf_runner" => "ticket_al_live_pf_runner",
  "ticket_live_pf_runner_concrete" => "ticket_al_live_pf_runner_concrete",
  "ticket_live_pf_runnerN" => "ticket_al_live_pf_runnerN",
  "ticket_live_sem_runner" => "ticket_al_live_sem_runner",
  "ticket_live_sem_runner_concrete" => "ticket_al_live_sem_runner_concrete",
  "ticket_live_sem_runnerN" => "ticket_al_live_sem_runnerN"]
