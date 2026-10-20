/-
**The fuel-free liveness of `treiber_pp.kl`
(AArch64) on the Inf machine** (additive). `LiveCertBoundedTreiberPpA64.lean`
proves `treiber_pp_live_semU` / `treiber_pp_live_runner_semU` (and
`_concrete`) on the fuel-free `…SemU` machine; `#semU_inf_twin`
(`ChainK/InfTwin.lean`) restates each on the Inf machine (`_semU` ↦
`_semInf`) under `WeakFairSemInf ∧ MemFair`, with **no** extra hypothesis.

The statements are re-checked by `tools/inf_twins.py` (listing
`INF_TWINS.md`, section "Headlines").
-/
import Kraken.Promising.LiveCertBoundedTreiberPpA64
import Kraken.Promising.SLR.ChainK.InfTwin

#semU_inf_twin Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_live_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_live_semU_concrete
#semU_inf_twin Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_live_runner_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedTreiberPpA64.treiber_pp_live_runner_semU_concrete
