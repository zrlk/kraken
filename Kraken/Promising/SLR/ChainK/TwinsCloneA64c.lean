/-
**The semantic twins clone: A64 modules, part 3**. `#chaink_clone'`
(`ChainK/Clone.lean`) re-elaborates, at the K world, the declarations of the
listed modules that the `#sem_twin` twins (`ChainK/SemTwinsA64.lean`) need:
the published theorems and the lemmas they use that mention the executable
machine. The modules are imported so that lake rebuilds this one when they
change.
-/
import Kraken.Promising.SLR.ChainK.TwinsCloneA64b
import Kraken.Promising.SLR.ChainK.HubsA64
import Kraken.Promising.SLR.ChainK.TicketA64Demo
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue2Concrete
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue2Runner
import Kraken.Promising.SLR.EnvG.MsQueue3Public
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue3
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue3Concrete
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue3Runner
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2Nodes
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2NodesRunner
import Kraken.Promising.SLR.EnvG.TreiberPublic
import Kraken.Promising.SLR.EnvG.A64WholeTreiberPublic
import Kraken.Promising.SLR.EnvG.ConcreteTreiber
import Kraken.Promising.SLR.EnvG.A64WholeTreiberConcrete
import Kraken.Promising.SLR.EnvG.A64WholeTreiberRunner
import Kraken.Promising.SLR.EnvG.ConcreteMsQueue
import Kraken.Promising.SLR.EnvG.ConcreteMsQueue2
import Kraken.Promising.SLR.EnvG.ConcreteMsQueue3
import Kraken.Promising.SLR.EnvG.MemValsA64MsQueue
import Kraken.Promising.SLR.EnvG.MemValsA64MsQueue23
import Kraken.Promising.SLR.EnvG.MemValsA64Treiber2
import Kraken.Promising.SLR.EnvG.MemValsA64Treiber2Arm
import Kraken.Promising.SLR.EnvG.MemValsA64Treiber2Nodes
import Kraken.Promising.SLR.EnvG.MemValsA64TreiberPP
import Kraken.Promising.SLR.EnvG.RunnerSafeFFA64
import Kraken.Promising.SLR.EnvG.RunnerSafeFFSwp

open Kraken.Promising.Live.Bridge

#chaink_clone' "../../SLR/EnvG/A64WholeMsQueue2Concrete.lean"
  only ["msqueue2_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeMsQueue2Runner.lean"
  only ["msqueue2_envG_runner", "msqueue2_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/MsQueue3Public.lean"
  only ["msqueue3_envG"]

#chaink_clone' "../../SLR/EnvG/A64WholeMsQueue3.lean"
  only ["msqueue3_envG_whole"]

#chaink_clone' "../../SLR/EnvG/A64WholeMsQueue3Concrete.lean"
  only ["msqueue3_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeMsQueue3Runner.lean"
  only ["msqueue3_envG_runner", "msqueue3_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeTreiber2Nodes.lean"
  only ["treiber2_nodes_envG_whole", "treiber2_nodes_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeTreiber2NodesRunner.lean"
  only ["treiber2_nodes_envG_runner", "treiber2_nodes_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/TreiberPublic.lean"
  only ["treiber_pp_envG"]

#chaink_clone' "../../SLR/EnvG/A64WholeTreiberPublic.lean"
  only ["treiber_pp_envG_whole"]

#chaink_clone' "../../SLR/EnvG/ConcreteTreiber.lean"
  only ["treiber_pp_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeTreiberConcrete.lean"
  only ["treiber_pp_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeTreiberRunner.lean"
  only ["treiber_pp_envG_runner", "treiber_pp_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/ConcreteMsQueue.lean"
  only ["msqueue1_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/ConcreteMsQueue2.lean"
  only ["msqueue2_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/ConcreteMsQueue3.lean"
  only ["msqueue3_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsA64MsQueue.lean"
  only ["msqueue1_envG_runner_faultFree", "msqueue1_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsA64MsQueue23.lean"
  only ["msqueue2_envG_runner_faultFree", "msqueue2_envG_runner_faultFree_concrete", "msqueue3_envG_runner_faultFree", "msqueue3_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsA64Treiber2.lean"
  only ["treiber2_envG_runner_faultFree", "treiber2_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsA64Treiber2Arm.lean"
  only ["treiber2_arm_envG_runner_faultFree", "treiber2_arm_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsA64Treiber2Nodes.lean"
  only ["treiber2_nodes_envG_runner_faultFree", "treiber2_nodes_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsA64TreiberPP.lean"
  only ["treiber_pp_envG_runner_faultFree", "treiber_pp_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/RunnerSafeFFA64.lean"
  only ["cas_counter_envG_runner_safe_faultFree", "cas_counter_envG_runner_safe_faultFree_concreteN", "swpl_counter_envG_runner_safe_faultFree", "swpl_counter_envG_runner_safe_faultFree_concreteN", "ticket_counter_envG_runner_safe_faultFree", "ticket_al_counter_envG_runner_safe_faultFree", "ticket_counter_envG_runner_safe_faultFree_concreteN", "ticket_al_counter_envG_runner_safe_faultFree_concreteN", "mp_relay3_envG_runner_safe_faultFree", "mp_relay3_envG_runner_safe_faultFree_concrete", "mp_relay3_swpl_envG_runner_safe_faultFree", "mp_relay3_swpl_envG_runner_safe_faultFree_concrete", "a64_spsc_envG_runner_safe_faultFree", "a64_spsc_envG_runner_safe_faultFree_concrete", "treiber_pp_envG_runner_safe_faultFree", "treiber_pp_envG_runner_safe_faultFree_concrete", "treiber2_envG_runner_safe_faultFree", "treiber2_envG_runner_safe_faultFree_concrete", "treiber2_nodes_envG_runner_safe_faultFree", "treiber2_nodes_envG_runner_safe_faultFree_concrete", "treiber2_arm_envG_runner_safe_faultFree", "treiber2_arm_envG_runner_safe_faultFree_concrete", "msqueue1_envG_runner_safe_faultFree", "msqueue1_envG_runner_safe_faultFree_concrete", "msqueue2_envG_runner_safe_faultFree", "msqueue2_envG_runner_safe_faultFree_concrete", "msqueue3_envG_runner_safe_faultFree", "msqueue3_envG_runner_safe_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/RunnerSafeFFSwp.lean"
  only ["swp_counter_envG_runner_safe_faultFree", "swp_counter_envG_runner_safe_faultFree_concreteN"]
