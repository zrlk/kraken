/-
**The semantic twins clone: ISA-neutral modules**. `#chaink_clone'`
(`ChainK/Clone.lean`) re-elaborates, at the K world, the declarations of the
listed modules that the `#sem_twin` twins (`ChainK/SemTwinsA64/X64.lean`) need:
the published theorems and the lemmas they use that mention the executable
machine. The modules are imported so that lake rebuilds this one when they
change.
-/
import Kraken.Promising.SLR.ChainK.SemTwin
import Kraken.Promising.SLR.ChainK.PromisePure
import Kraken.Promising.SLR.ChainK.HubsN
import Kraken.Promising.SLR.EnvG.RmwFailRule
import Kraken.Promising.SLR.EnvG.RmwFailChain
import Kraken.Promising.SLR.EnvG.TakeFinalCommon
import Kraken.Promising.SLR.EnvG.TicketX2Reach
import Kraken.Promising.SLR.SpinInitRes

open Kraken.Promising.Live.Bridge

#chaink_clone' "../../SLR/EnvG/RmwFailRule.lean"
  only ["Theorem1FChain"]

#chaink_clone' "../../SLR/EnvG/RmwFailChain.lean"
  only ["theorem1FChain"]

#chaink_clone' "../../SLR/EnvG/TakeFinalCommon.lean"
  only ["final_of_relWritesJS"]

#chaink_clone' "../../SLR/EnvG/TicketX2Reach.lean"
  only ["inv_step", "inv_reachable"] keep_names ["Inv"]

#chaink_clone' "../../SLR/SpinInitRes.lean"
  only ["counter_init"]
