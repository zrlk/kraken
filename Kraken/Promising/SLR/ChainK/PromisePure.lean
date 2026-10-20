/-
**The K-world chain clone: condition `PromisePure`, the release-write rules and the
dispenser instance, `relWrites_reach` and `final_of_relWritesJ` at the K world**.
`#chaink_clone` (`ChainK/Clone.lean`) re-elaborates the declarations of the
listed modules that mention the executable machine or an earlier clone (see
`ChainK/Theorem1.lean`). The modules are imported so that lake rebuilds this
one when they change.
-/
import Kraken.Promising.SLR.ChainK.Final
import Kraken.Promising.SLR.TsoPromisePure
import Kraken.Promising.SLR.PromisePureGeneral
import Kraken.Promising.SLR.PromisePureF
import Kraken.Promising.SLR.RelPure
import Kraken.Promising.SLR.LoadClaimChain
import Kraken.Promising.SLR.LoadClaimFinal
import Kraken.Promising.SLR.TakeRuleThread
import Kraken.Promising.SLR.TicketRule
import Kraken.Promising.SLR.DispenserRun
import Kraken.Promising.SLR.DispenserFresh
import Kraken.Promising.SLR.EnvG.RelPureEnv

open Kraken.Promising.Live.Bridge

#chaink_clone "../TsoPromisePure.lean"

#chaink_clone "../PromisePureGeneral.lean"

#chaink_clone "../PromisePureF.lean"

#chaink_clone "../RelPure.lean"

#chaink_clone "../LoadClaimChain.lean"

#chaink_clone "../LoadClaimFinal.lean"

#chaink_clone "../TakeRuleThread.lean"

#chaink_clone "../TicketRule.lean"

#chaink_clone "../DispenserRun.lean"

#chaink_clone "../DispenserFresh.lean"

#chaink_clone "../EnvG/RelPureEnv.lean"
