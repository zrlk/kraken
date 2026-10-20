/-
**Stage 3: the event trees of the `ldaddal` ticket
lock worker** `tkWorkerAl` (`ticketlock_al2.kl`, `EnvG/TicketAlSmoke.lean`):
`LiveTicketTrees.lean` re-elaborated by `#ticket_al_clone`
(`LiveTicketAlClone.lean`): `tkWorker` → `tkWorkerAl`, the ticket RMW's kind
`.acq` → `.acqRel` (`exec_ldadda` → `exec_ldaddal`). Namespace
`Live.TicketAlTrees`; every other name as in `Live.TicketTrees`.
-/
import Kraken.Promising.LiveTicketAlClone
import Kraken.Promising.LiveTicketTrees
import Kraken.Promising.SLR.EnvG.TicketAlSmoke

#ticket_al_clone "LiveTicketTrees.lean"
