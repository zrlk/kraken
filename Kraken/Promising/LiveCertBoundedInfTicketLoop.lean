/-
**The fuel-free headlines of the repeated-acquire
ticket lock on the Inf machine** (AArch64; additive). The CertBounded
headlines of `LiveCertBoundedTicketLoop.lean` conclude on the fuel-free
`…SemU` machine, whose traces and predicates coincide with the Inf machine's
(`LiveSemInf.lean`). `#semU_inf_twin` (`ChainK/InfTwin.lean`) restates each
on the Inf machine (`_semU` ↦ `_semInf`) with **no** extra hypothesis, under
`WeakFairSemInf ∧ MemFair`:

- starvation-freedom per round (`ticket_loop_starve_semInf`);
- completion of all rounds (`ticket_loop_finish_semInf`);
- their conjunction (`ticket_loop_live_semInf`, `…_concrete`);
- termination (`ticket_loop_term_semInf`, `…_concrete`; `TermFromSemInf`).

The `TicketLoop…SemU` definitions are unfolded. The statements are
re-checked by `tools/inf_twins.py` (listing `INF_TWINS.md`, section
"Headlines").
-/
import Kraken.Promising.LiveCertBoundedTicketLoop
import Kraken.Promising.SLR.ChainK.InfTwin

#semU_inf_twin Kraken.Promising.Live.CertBoundedTicketLoop.ticket_loop_starve_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedTicketLoop.ticket_loop_finish_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedTicketLoop.ticket_loop_live_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedTicketLoop.ticket_loop_live_semU_concrete
#semU_inf_twin Kraken.Promising.Live.CertBoundedTicketLoop.ticket_loop_term_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedTicketLoop.ticket_loop_term_semU_concrete
