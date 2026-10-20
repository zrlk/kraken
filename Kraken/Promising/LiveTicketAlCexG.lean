/-
**Stage 3: `TicketAlLiveWF` is false**
(`ticketAlLiveWF_false`, executable machine `succs`/`TraceS`):
`LiveTicketCexG.lean` re-elaborated at the `ldaddal` worker `tkWorkerAl` by
the clone command of `LiveTicketAlClone.lean`. The lasso schedule of
`LiveTicketCex` (`prefixTr`, `loopTr`) is replayed cell for cell on the
`tkWorkerAl` configuration and every kernel check (`decide +kernel`) is
re-run; the generic `TicketCexG.lasso_not_live` closes the proof. Names as in
`LiveTicketCexG.lean`, in namespace `Live.TicketAlCexG`.
-/
import Kraken.Promising.LiveTicketAlClone
import Kraken.Promising.LiveTicketAl
import Kraken.Promising.LiveTicketCexG

-- The generic lasso lives in `TicketCexG` (`LiveTicketCex.lean`); the
-- clone's namespace is `TicketAlCexG`, so open the two names it uses.
open Kraken.Promising.Live.TicketCexG (LassoChecks lasso_not_live)

#ticket_al_clone "LiveTicketCexG.lean" with [
  "namespace Kraken.Promising.Live.TicketCexG" => "namespace Kraken.Promising.Live.TicketAlCexG",
  "end Kraken.Promising.Live.TicketCexG" => "end Kraken.Promising.Live.TicketAlCexG",
  "Kraken.Promising.Live.TicketCexG.ticketLiveWF_false" => "Kraken.Promising.Live.TicketAlCexG.ticketAlLiveWF_false",
  "ticketLiveWF_false" => "ticketAlLiveWF_false"]
