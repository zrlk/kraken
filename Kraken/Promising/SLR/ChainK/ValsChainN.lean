/-
**CHAINK clone: the ISA-neutral value chain at the K world**.
`#chaink_clone'` (`ChainK/Clone.lean`) re-elaborates, at the K world, the
value chain of `EnvG/ValsChain.lean`: `promiseFresh_of_allInvK`,
`theorem1FChainVK`, `final_of_chainVK` (namespace
`Kraken.Promising.SLR.EnvG.Vals`), the same statements about `ReachableKF`
(= `ReachableK`, fuel ignored). The AArch64 value bridge
(`Lower/LSE2Final.lean`) and the x64 one (`Lower/KitX64ValsSem.lean`) both
build on this one clone.

The value-restricted purity step of `SLR/PromisePureVals.lean` is cloned on
top of it: `promisePure_of_relWritesVK` (namespace `Kraken.Promising.SLR`) and
`final_of_chainVPK` (namespace `Kraken.Promising.SLR.EnvG.Vals`); the
latter's `NTFree` step is `Config.ntFree_of_configInv_initK`, stated on
`ReachableK` and used unchanged. The x64 bridge with value-restricted purity
(`Lower/KitX64ValsPureSem.lean`) builds on these. The module imports nothing
ISA-specific.
-/
import Kraken.Promising.SLR.ChainK.TwinsCloneN
import Kraken.Promising.SLR.EnvG.ValsChain
import Kraken.Promising.SLR.PromisePureVals

open Kraken.Promising.Live.Bridge

#chaink_clone' "../EnvG/ValsChain.lean"
  only ["promiseFresh_of_allInv", "theorem1FChainV", "final_of_chainV"]

#chaink_clone' "../PromisePureVals.lean"
  only ["promisePure_of_relWritesV", "final_of_chainVP"]
