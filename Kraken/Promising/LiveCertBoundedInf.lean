/-
**The fuel-free liveness and termination headlines on the
Inf machine** (AArch64; additive). The CertBounded headlines of
`LiveCertBoundedSpinCas.lean` and `LiveCertBoundedTreiber2.lean` /
`LiveCertBoundedTreiber2P.lean` conclude on the fuel-free `…SemU` machine,
whose traces and predicates coincide with the Inf machine's
(`LiveSemInf.lean`). `#semU_inf_twin` (`ChainK/InfTwin.lean`) restates each
on the Inf machine (`_semU` ↦ `_semInf`) with **no** extra hypothesis:

- deadlock-freedom / per-thread liveness of the CAS spinlock under
  `WeakFairSemInf ∧ MemFair` (`spin_cas_live_semInf`, `…_oneShot_…`,
  `…_concrete`; the `CasSpinLive…SemU` definitions are unfolded);
- bounded termination (`TermBoundSemInf`, no fairness) of the Treiber stack
  family `treiber2`, `treiber2_arm`, `treiber2_relaxed`, `treiber2_nodes`.

The statements are re-checked by `tools/inf_twins.py` (listing
`INF_TWINS.md`, section "Headlines").
-/
import Kraken.Promising.LiveCertBoundedSpinCas
import Kraken.Promising.LiveCertBoundedTreiber2
import Kraken.Promising.SLR.ChainK.InfTwin

#semU_inf_twin Kraken.Promising.Live.CertBoundedSpinCas.spin_cas_live_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedSpinCas.spin_cas_live_oneShot_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedSpinCas.spin_cas_live_semU_concrete
#semU_inf_twin Kraken.Promising.Live.CertBoundedSpinCas.spin_cas_live_oneShot_semU_concrete
#semU_inf_twin Kraken.Promising.Live.CertBoundedTreiber2P.term_semU_genP
#semU_inf_twin Kraken.Promising.Live.TermTreiber2.treiber2_term_semU_gen
#semU_inf_twin Kraken.Promising.Live.TermTreiber2.treiber2_term_semU
#semU_inf_twin Kraken.Promising.Live.TermTreiber2.treiber2_term_semU_concrete
#semU_inf_twin Kraken.Promising.Live.TermTreiber2Arm.treiber2_arm_term_semU_all
#semU_inf_twin Kraken.Promising.Live.TermTreiber2Arm.treiber2_arm_term_semU
#semU_inf_twin Kraken.Promising.Live.TermTreiber2Arm.treiber2_arm_term_semU_concrete
#semU_inf_twin Kraken.Promising.Live.TermTreiber2Relaxed.treiber2_relaxed_term_semU_all
#semU_inf_twin Kraken.Promising.Live.TermTreiber2Relaxed.treiber2_relaxed_term_semU
#semU_inf_twin Kraken.Promising.Live.TermTreiber2Nodes.treiber2_nodes_term_semU_all
#semU_inf_twin Kraken.Promising.Live.TermTreiber2Nodes.treiber2_nodes_term_semU
#semU_inf_twin Kraken.Promising.Live.TermTreiber2Nodes.treiber2_nodes_term_semU_concrete
