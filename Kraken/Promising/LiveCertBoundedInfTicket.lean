/-
**The fuel-free ticket-lock liveness headline on the
Inf machine** (AArch64; additive). `ticket_live_semU` and its `_concrete`
form (`LiveCertBoundedTicket.lean`) conclude on the fuel-free `…SemU`
machine, whose traces and predicates coincide with the Inf machine's
(`LiveSemInf.lean`). `#semU_inf_twin` (`ChainK/InfTwin.lean`) restates each on
the Inf machine (`_semU` ↦ `_semInf`) with **no** extra hypothesis: per-thread
liveness of the ticket lock with promises under `WeakFairSemInf ∧ MemFair`
(`ticket_live_semInf`, `ticket_live_semInf_concrete`; `TicketLiveSemU` is
unfolded).

The statements are re-checked by `tools/inf_twins.py` (listing
`INF_TWINS.md`, section "Headlines").
-/
import Kraken.Promising.LiveCertBoundedTicket
import Kraken.Promising.SLR.ChainK.InfTwin

#semU_inf_twin Kraken.Promising.Live.CertBoundedTicket.ticket_live_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedTicket.ticket_live_semU_concrete
