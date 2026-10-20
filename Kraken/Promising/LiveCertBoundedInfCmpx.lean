/-
**The x64 `lock cmpxchg` spinlock's fuel-free
liveness headlines on the Inf machine** (additive). The CertBounded
headlines of `LiveCertBoundedSpinCmpx.lean` conclude on the fuel-free
`…SemU` machine; `#semU_inf_twin` (`ChainK/InfTwin.lean`) restates each on
the Inf machine (`_semU` ↦ `_semInf`) with **no** extra hypothesis, as
`LiveCertBoundedInf.lean` does for the AArch64 CAS spinlock:
deadlock-freedom and per-thread liveness of the one-shot workers under
`WeakFairSemInf ∧ MemFair` (`spin_cmpx_live_semInf`, `…_oneShot_…`,
`…_concrete`; the `CmpxSpinLive…SemU` definitions are unfolded). `MemFair`
on x86 is a modelling assumption.

The statements are re-checked by `tools/inf_twins.py` (listing
`INF_TWINS.md`, section "Headlines").
-/
import Kraken.Promising.LiveCertBoundedSpinCmpx
import Kraken.Promising.SLR.ChainK.InfTwin

#semU_inf_twin Kraken.Promising.Live.CertBoundedSpinCmpx.spin_cmpx_live_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedSpinCmpx.spin_cmpx_live_oneShot_semU
#semU_inf_twin Kraken.Promising.Live.CertBoundedSpinCmpx.spin_cmpx_live_semU_concrete
#semU_inf_twin Kraken.Promising.Live.CertBoundedSpinCmpx.spin_cmpx_live_oneShot_semU_concrete
