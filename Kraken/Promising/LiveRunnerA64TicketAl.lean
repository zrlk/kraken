/-
**Liveness of the AArch64 `ldaddal` ticket lock (`ticketlock_al{2,3}.kl`) in
the runner's declarations form.** Executable machine
(`succs`/`TraceS`), promise-free fragment (`WeakFair ∧ MemFair ∧
PromiseFree`).

`LiveRunnerA64Ticket.lean` re-elaborated at `tkWorkerAl` by the clone command
of `LiveTicketAlClone.lean` (substitution `ticketAlSubst` plus the runner
names below). Namespace `Live.RunnerA64TicketAl`:

- `STk`, `stepOK_tk` (every `STk` state's tree, `TicketAlTrees.exec_*`,
  accesses only the three words), `sTk_of_start` (from `StartStateAl`);
- `TkStartAlD ds`: `TicketAl.TkStartAl` with the start states
  `WithDeclsD ds (StartStateAl x o c)` (as `ticket_al_counter_envG_runner`)
  and the three `Decls.AgreesAt` facts (no `StrictSized`, no `prom = []`);
- **`ticket_al_live_pf_runner`** (`TicketAlLivePFD ds fuel`, by
  `liveFrom_transfer`/`execSimA` from `TicketAlPF.ticket_al_live_pf`),
  `ticket_al_live_pf_runner_concrete` (layout `ConcreteTicketAl.tkAlLayout`)
  and `ticket_al_live_pf_runnerN` (`N` copies of the runner's
  `tkAlWorkerD0`, declarations `tkDeclsD` included, initial memory
  `tkAlInitMem`; only `N + 1 < 2 ^ 32` left).
-/
import Kraken.Promising.LiveTicketAlClone
import Kraken.Promising.LiveTicketAlPF
import Kraken.Promising.LiveRunnerA64Ticket

#ticket_al_clone "LiveRunnerA64Ticket.lean" with ["RunnerA64Ticket" => "RunnerA64TicketAl", "RunnerSemA64Ticket" => "RunnerSemA64TicketAl",
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
