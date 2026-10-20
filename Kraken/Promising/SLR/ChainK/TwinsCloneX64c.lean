/-
**The semantic twins clone: X64 modules, part 3**. `#chaink_clone'`
(`ChainK/Clone.lean`) re-elaborates, at the K world, the declarations of the
listed modules that the `#sem_twin` twins (`ChainK/SemTwinsX64.lean`) need:
the published theorems and the lemmas they use that mention the executable
machine. The modules are imported so that lake rebuilds this one when they
change.
-/
import Kraken.Promising.SLR.ChainK.TwinsCloneX64b
import Kraken.Promising.SLR.ChainK.HubsX64
import Kraken.Promising.SLR.EnvG.X64RelayAbsRunner
import Kraken.Promising.SLR.EnvG.X64SpinAbsConcrete
import Kraken.Promising.SLR.EnvG.X64SpinAbsRunner
import Kraken.Promising.SLR.EnvG.TicketXPure
import Kraken.Promising.SLR.EnvG.TicketXPublic
import Kraken.Promising.SLR.EnvG.TicketXRunner
import Kraken.Promising.SLR.EnvG.X64FaultFreeFixed
import Kraken.Promising.SLR.EnvG.RunnerSafeFFX64
import Kraken.Promising.SLR.EnvG.RunnerSafeFFX64ABA
import Kraken.Promising.SLR.EnvG.X64MpIncConcrete
import Kraken.Promising.SLR.EnvG.X64RelayXchgConcrete
import Kraken.Promising.SLR.EnvG.X64SpscConcrete
import Kraken.Promising.SLR.EnvG.X64Ticket2Public
import Kraken.Promising.SLR.EnvG.X64Ticket2Runner
import Kraken.Promising.SLR.EnvG.X64Ticket2FaultFree
import Kraken.Promising.SLR.EnvG.X64TreiberConcrete
import Kraken.Promising.SLR.EnvG.X64VecPublishConcrete
import Kraken.Promising.SLR.X64SpinNoNT
import Kraken.Promising.SLR.X64SpinAdequacy
import Kraken.Promising.SLR.X64SpinFinal
import Kraken.Promising.SLR.X64SpinFinalX
import Kraken.Promising.SLR.X64SpinConcrete
import Kraken.Promising.SLR.X64SpinPublic

open Kraken.Promising.Live.Bridge

#chaink_clone' "../../SLR/EnvG/X64RelayAbsRunner.lean"
  only ["mp_relay3_xchg_envG_runner", "mp_relay3_xchg_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/X64SpinAbsConcrete.lean"
  only ["x64_spin_counter_envG_verbatim_concreteN", "x64_spin_counter_envG_verbatim_concrete2"]

#chaink_clone' "../../SLR/EnvG/X64SpinAbsRunner.lean"
  only ["x64_spin_counter_envG_runner", "x64_spin_counter_envG_runner_concreteN", "x64_spin_counter_envG_runner_concrete2", "x64_spin_counter_envG_runner_concrete3"]

#chaink_clone' "../../SLR/EnvG/TicketXPure.lean"
  only ["ticket_counter_ofX"]

#chaink_clone' "../../SLR/EnvG/TicketXPublic.lean"
  only ["ticket3_counter_envG_of", "ticket3_counter_envG_verbatim", "ticket3_counter_envG_runner"]

#chaink_clone' "../../SLR/EnvG/TicketXRunner.lean"
  only ["ticket3_counter_envG_runner_concreteN", "ticket3_counter_envG_runner_concrete3"]

#chaink_clone' "../../SLR/EnvG/X64FaultFreeFixed.lean"
  only ["x64_spin_counter_envG_runner_faultFree", "x64_spin_counter_envG_runner_faultFree_concreteN", "x64_cmpx_counter_envG_runner_faultFree", "x64_cmpx_counter_envG_runner_faultFree_concreteN", "x64_dekker_public_runner_faultFree", "x64_dekker_public_runner_faultFree_concrete", "ticket3_counter_envG_runner_faultFree", "ticket3_counter_envG_runner_faultFree_concreteN", "mp_relay3_xchg_envG_runner_faultFree", "mp_relay3_xchg_envG_runner_faultFree_concrete", "x64_mp_incl_envGV_runner_faultFree", "x64_mp_incl_envGV_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/RunnerSafeFFX64.lean"
  only ["x64_spin_counter_envG_runner_safe_faultFree", "Concrete.x64_spin_counter_envG_runner_safe_faultFree_concreteN", "x64_cmpx_counter_envG_runner_safe_faultFree", "Concrete.x64_cmpx_counter_envG_runner_safe_faultFree_concreteN", "x64_dekker_public_runner_safe_faultFree", "Concrete.x64_dekker_public_runner_safe_faultFree_concrete", "ticket3_counter_envG_runner_safe_faultFree", "Concrete.ticket3_counter_envG_runner_safe_faultFree_concreteN", "mp_relay3_xchg_envG_runner_safe_faultFree", "Concrete.mp_relay3_xchg_envG_runner_safe_faultFree_concrete", "x64_mp_incl_envGV_runner_safe_faultFree", "Concrete.x64_mp_incl_envGV_runner_safe_faultFree_concrete", "x64_spsc_envG_runner_safe_faultFree", "Concrete.x64_spsc_envG_runner_safe_faultFree_concrete", "x64_treiber_pp_envG_runner_safe_faultFree", "Concrete.x64_treiber_pp_envG_runner_safe_faultFree_concrete", "x64_treiber2_envG_runner_safe_faultFree", "Concrete.x64_treiber2_envG_runner_safe_faultFree_concrete", "x64_msqueue2_envG_runner_safe_faultFree", "Concrete.x64_msqueue2_envG_runner_safe_faultFree_concrete", "x64_msqueue3_envG_runner_safe_faultFree", "Concrete.x64_msqueue3_envG_runner_safe_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/RunnerSafeFFX64ABA.lean"
  only ["x64_treiber_aba_tagged_runner_safe_faultFree", "x64_treiber_aba_tagged_runner_concrete", "x64_treiber_aba_tagged_runner_safe_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/X64MpIncConcrete.lean"
  only ["x64_mp_incl_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/X64RelayXchgConcrete.lean"
  only ["mp_relay3_xchg_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/X64SpscConcrete.lean"
  only ["x64_spsc_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/X64Ticket2Public.lean"
  only ["ticket2_counter_envG_of", "ticket2_counter_envG_verbatim", "ticket2_counter_envG_runner"]

#chaink_clone' "../../SLR/EnvG/X64Ticket2Runner.lean"
  only ["ticket2_counter_envG_runner_concreteN", "ticket2_counter_envG_runner_concrete2"]

#chaink_clone' "../../SLR/EnvG/X64Ticket2FaultFree.lean"
  only ["ticket2_counter_envG_runner_faultFree", "ticket2_counter_envG_runner_faultFree_concreteN", "ticket2_counter_envG_runner_safe_faultFree", "Concrete.ticket2_counter_envG_runner_safe_faultFree_concreteN"]

#chaink_clone' "../../SLR/EnvG/X64TreiberConcrete.lean"
  only ["x64_treiber_pp_envG_concrete"]

#chaink_clone' "../../SLR/EnvG/X64VecPublishConcrete.lean"
  only ["x64_publish_movdqa_verbatim_concrete", "x64_publish_movdqa_verbatim_concrete_faultFree"]

#chaink_clone' "../../SLR/X64SpinNoNT.lean"
  only ["spinWorker_ntFree"]

#chaink_clone' "../../SLR/X64SpinAdequacy.lean"
  only ["spin_promisePure", "x64_counter_init"]

#chaink_clone' "../../SLR/X64SpinFinal.lean"
  only ["x64_counter_spin_of_cells"]

#chaink_clone' "../../SLR/X64SpinFinalX.lean"
  only ["x64_counter_spin"]

#chaink_clone' "../../SLR/X64SpinConcrete.lean"
  only ["x64_counter_2"]

#chaink_clone' "../../SLR/X64SpinPublic.lean"
  only ["x64_counter_public", "reachable_nil"]
