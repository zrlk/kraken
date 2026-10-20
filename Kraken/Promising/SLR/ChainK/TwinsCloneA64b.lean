/-
**The semantic twins clone: A64 modules, part 2**. `#chaink_clone'`
(`ChainK/Clone.lean`) re-elaborates, at the K world, the declarations of the
listed modules that the `#sem_twin` twins (`ChainK/SemTwinsA64.lean`) need:
the published theorems and the lemmas they use that mention the executable
machine. The modules are imported so that lake rebuilds this one when they
change.
-/
import Kraken.Promising.SLR.ChainK.TwinsCloneA64a
import Kraken.Promising.SLR.ChainK.HubsA64
import Kraken.Promising.SLR.ChainK.TicketA64Demo
import Kraken.Promising.SLR.EnvG.A64WholeRelaySwplConcrete
import Kraken.Promising.SLR.EnvG.A64WholeRelaySwplRunner
import Kraken.Promising.SLR.EnvG.A64SpscWholePublic
import Kraken.Promising.SLR.EnvG.A64SpscWholeConcrete
import Kraken.Promising.SLR.EnvG.A64SpscWholeRunner
import Kraken.Promising.SLR.EnvG.A64FaultFreeFixed
import Kraken.Promising.SLR.SwpPublic
import Kraken.Promising.SLR.EnvG.SwpEnvGPublic
import Kraken.Promising.SLR.EnvG.A64SwpRunner
import Kraken.Promising.SLR.EnvG.A64SwpNoFault
import Kraken.Promising.SLR.EnvG.Treiber2Public
import Kraken.Promising.SLR.EnvG.Treiber2DataPublic
import Kraken.Promising.SLR.EnvG.Treiber2ArmPublic
import Kraken.Promising.SLR.EnvG.ConcreteTreiber2
import Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data
import Kraken.Promising.SLR.EnvG.A64Treiber2ArmWhole
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2Runner
import Kraken.Promising.SLR.EnvG.A64Treiber2ArmRunner
import Kraken.Promising.SLR.EnvG.MsQueuePublic
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue1
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue1Concrete
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue1Runner
import Kraken.Promising.SLR.EnvG.MsQueue2Public
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue2

open Kraken.Promising.Live.Bridge

#chaink_clone' "../../SLR/EnvG/A64WholeRelaySwplConcrete.lean"
  only ["mp_relay3_swpl_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeRelaySwplRunner.lean"
  only ["mp_relay3_swpl_envG_runner", "mp_relay3_swpl_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/A64SpscWholePublic.lean"
  only ["a64_spsc_envG_whole"]

#chaink_clone' "../../SLR/EnvG/A64SpscWholeConcrete.lean"
  only ["a64_spsc_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64SpscWholeRunner.lean"
  only ["a64_spsc_envG_runner", "a64_spsc_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/A64FaultFreeFixed.lean"
  only ["cas_counter_envG_runner_faultFree", "cas_counter_envG_runner_faultFree_concreteN", "swpl_counter_envG_runner_faultFree", "swpl_counter_envG_runner_faultFree_concreteN", "ticket_counter_envG_runner_faultFree", "ticket_al_counter_envG_runner_faultFree", "ticket_counter_envG_runner_faultFree_concreteN", "ticket_al_counter_envG_runner_faultFree_concreteN", "mp_relay3_envG_runner_faultFree", "mp_relay3_envG_runner_faultFree_concrete", "mp_relay3_swpl_envG_runner_faultFree", "mp_relay3_swpl_envG_runner_faultFree_concrete", "a64_spsc_envG_runner_faultFree", "a64_spsc_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/SwpPublic.lean"
  only ["swp_counter_public", "reachable_nil"]

#chaink_clone' "../../SLR/EnvG/SwpEnvGPublic.lean"
  only ["swp_counter_envG"]

#chaink_clone' "../../SLR/EnvG/A64SwpRunner.lean"
  only ["swp_counter_envG_runner", "swp_counter_envG_runner_concreteN", "swp_counter_envG_runner_concrete2", "swp_counter_envG_runner_concrete3"]

#chaink_clone' "../../SLR/EnvG/A64SwpNoFault.lean"
  only ["swp_counter_envG_runner_faultFree", "swp_counter_envG_runner_faultFree_concreteN"]

#chaink_clone' "../../SLR/EnvG/Treiber2Public.lean"
  only ["treiber2_nodes_envG"]

#chaink_clone' "../../SLR/EnvG/Treiber2DataPublic.lean"
  only ["treiber2_envG"]

#chaink_clone' "../../SLR/EnvG/Treiber2ArmPublic.lean"
  only ["treiber2_arm_envG"]

#chaink_clone' "../../SLR/EnvG/ConcreteTreiber2.lean"
  only ["treiber2_nodes_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/ConcreteTreiber2Data.lean"
  only ["treiber2_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/A64Treiber2ArmWhole.lean"
  only ["treiber2_arm_envG_whole", "treiber2_arm_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeTreiber2.lean"
  only ["treiber2_envG_whole", "treiber2_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeTreiber2Runner.lean"
  only ["treiber2_envG_runner", "treiber2_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/A64Treiber2ArmRunner.lean"
  only ["treiber2_arm_envG_runner", "treiber2_arm_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/MsQueuePublic.lean"
  only ["msqueue1_envG"]

#chaink_clone' "../../SLR/EnvG/A64WholeMsQueue1.lean"
  only ["msqueue1_envG_whole"]

#chaink_clone' "../../SLR/EnvG/A64WholeMsQueue1Concrete.lean"
  only ["msqueue1_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeMsQueue1Runner.lean"
  only ["msqueue1_envG_runner", "msqueue1_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/MsQueue2Public.lean"
  only ["msqueue2_envG"]

#chaink_clone' "../../SLR/EnvG/A64WholeMsQueue2.lean"
  only ["msqueue2_envG_whole"]
