/-
**The semantic twins clone: A64 modules, part 1**. `#chaink_clone'`
(`ChainK/Clone.lean`) re-elaborates, at the K world, the declarations of the
listed modules that the `#sem_twin` twins (`ChainK/SemTwinsA64.lean`) need:
the published theorems and the lemmas they use that mention the executable
machine. The modules are imported so that lake rebuilds this one when they
change.
-/
import Kraken.Promising.SLR.ChainK.TwinsCloneN
import Kraken.Promising.SLR.ChainK.HubsA64
import Kraken.Promising.SLR.ChainK.TicketA64Demo
import Kraken.Promising.SLR.EnvG.A64RmwFailFinal
import Kraken.Promising.SLR.EnvG.TakeFinal
import Kraken.Promising.SLR.EnvG.A64DeclsLink
import Kraken.Promising.SLR.EnvG.CasPublic
import Kraken.Promising.SLR.EnvG.ConcreteCas
import Kraken.Promising.SLR.EnvG.SwplLockPublic
import Kraken.Promising.SLR.EnvG.ConcreteSwpl
import Kraken.Promising.SLR.SwpPure
import Kraken.Promising.SLR.SwpAdequacy
import Kraken.Promising.SLR.SwpFinal
import Kraken.Promising.SLR.SwpConcrete
import Kraken.Promising.SLR.EnvG.A64CasRunner
import Kraken.Promising.SLR.EnvG.MemValsA64
import Kraken.Promising.SLR.EnvG.RelayPublic
import Kraken.Promising.SLR.EnvG.RelaySwplPublic
import Kraken.Promising.SLR.EnvG.A64SpscPublic
import Kraken.Promising.SLR.EnvG.A64SpscConcrete
import Kraken.Promising.SLR.EnvG.A64SwplRunner
import Kraken.Promising.SLR.EnvG.TicketAlPublic
import Kraken.Promising.SLR.EnvG.ConcreteTicketAl
import Kraken.Promising.SLR.EnvG.A64TicketRunner
import Kraken.Promising.SLR.EnvG.A64WholeRelayPublic
import Kraken.Promising.SLR.EnvG.A64WholeRelayConcrete
import Kraken.Promising.SLR.EnvG.A64WholeRelayRunner
import Kraken.Promising.SLR.EnvG.A64WholeRelaySwpl

open Kraken.Promising.Live.Bridge

#chaink_clone' "../../SLR/EnvG/A64RmwFailFinal.lean"
  only ["final_of_relPureSafelyF"]

#chaink_clone' "../../SLR/EnvG/TakeFinal.lean"
  only ["final_of_relPureSafelyS"]

#chaink_clone' "../../SLR/EnvG/A64DeclsLink.lean"
  only ["final_of_relPureSafelyFD", "final_of_relPureSafelySD"]

#chaink_clone' "../../SLR/EnvG/CasPublic.lean"
  only ["cas_counter_envG"]

#chaink_clone' "../../SLR/EnvG/ConcreteCas.lean"
  only ["cas_counter_envG_concreteN", "cas_counter_envG_concrete2"]

#chaink_clone' "../../SLR/EnvG/SwplLockPublic.lean"
  only ["swpl_counter_envG"]

#chaink_clone' "../../SLR/EnvG/ConcreteSwpl.lean"
  only ["swpl_counter_envG_concreteN", "swpl_counter_envG_concrete2"]

#chaink_clone' "../../SLR/SwpPure.lean"
  only ["swp_promisePure"]

#chaink_clone' "../../SLR/SwpAdequacy.lean"
  only ["swp_counter", "swp_counter_armv8_of_cells"]

#chaink_clone' "../../SLR/SwpFinal.lean"
  only ["swp_counter_armv8"]

#chaink_clone' "../../SLR/SwpConcrete.lean"
  only ["swp_counter_2"]

#chaink_clone' "../../SLR/EnvG/A64CasRunner.lean"
  only ["cas_counter_envG_runner", "cas_counter_envG_runner_concreteN", "cas_counter_envG_runner_concrete2", "cas_counter_envG_runner_concrete3"]

#chaink_clone' "../../SLR/EnvG/MemValsA64.lean"
  only ["a64_faultFree_of_valSpecs", "a64_faultFree_of_addrSpecs"]

#chaink_clone' "../../SLR/EnvG/RelayPublic.lean"
  only ["mp_relay3_envG"]

#chaink_clone' "../../SLR/EnvG/RelaySwplPublic.lean"
  only ["mp_relay3_swpl_envG"]

#chaink_clone' "../../SLR/EnvG/A64SpscPublic.lean"
  only ["a64_spsc_envG"]

#chaink_clone' "../../SLR/EnvG/A64SpscConcrete.lean"
  only ["a64_spsc_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/A64SwplRunner.lean"
  only ["swpl_counter_envG_runner", "swpl_counter_envG_runner_concreteN", "swpl_counter_envG_runner_concrete2", "swpl_counter_envG_runner_concrete3"]

#chaink_clone' "../../SLR/EnvG/TicketAlPublic.lean"
  only ["ticket_al_counter_envG"]

#chaink_clone' "../../SLR/EnvG/ConcreteTicketAl.lean"
  only ["ticket_al_counter_envG_concreteN", "ticket_al_counter_envG_concrete2", "ticket_al_counter_envG_concrete3"]

#chaink_clone' "../../SLR/EnvG/A64TicketRunner.lean"
  only ["ticket_counter_ofD", "ticket_counter_envG_runner", "ticket_al_counter_envG_runner", "ticket_counter_envG_runner_concreteN", "ticket_counter_envG_runner_concrete2", "ticket_counter_envG_runner_concrete3", "ticket_al_counter_envG_runner_concreteN", "ticket_al_counter_envG_runner_concrete2", "ticket_al_counter_envG_runner_concrete3"]

#chaink_clone' "../../SLR/EnvG/A64WholeRelayPublic.lean"
  only ["mp_relay3_envG_whole"]

#chaink_clone' "../../SLR/EnvG/A64WholeRelayConcrete.lean"
  only ["mp_relay3_envG_whole_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeRelayRunner.lean"
  only ["mp_relay3_envG_runner", "mp_relay3_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/A64WholeRelaySwpl.lean"
  only ["mp_relay3_swpl_envG_whole"]
