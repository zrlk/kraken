/-
**The semantic twins clone: X64 modules, part 2**. `#chaink_clone'`
(`ChainK/Clone.lean`) re-elaborates, at the K world, the declarations of the
listed modules that the `#sem_twin` twins (`ChainK/SemTwinsX64.lean`) need:
the published theorems and the lemmas they use that mention the executable
machine. The modules are imported so that lake rebuilds this one when they
change.
-/
import Kraken.Promising.SLR.ChainK.TwinsCloneX64a
import Kraken.Promising.SLR.ChainK.HubsX64
import Kraken.Promising.SLR.EnvG.X64Treiber2Runner
import Kraken.Promising.SLR.EnvG.MemValsTreiber2
import Kraken.Promising.SLR.EnvG.X64TreiberAbsConcrete
import Kraken.Promising.SLR.EnvG.X64TreiberAbsRunner
import Kraken.Promising.SLR.EnvG.MemValsTreiberPP
import Kraken.Promising.SLR.EnvG.X64VecPublish
import Kraken.Promising.SLR.EnvG.X64VecTreiberABA
import Kraken.Promising.SLR.EnvG.MemValsX64ABA
import Kraken.Promising.SLR.EnvG.MemValsX64ABAConcrete
import Kraken.Promising.SLR.EnvG.X64SpscPublic
import Kraken.Promising.SLR.EnvG.X64SpscAbsPublic
import Kraken.Promising.SLR.EnvG.X64SpscAbsConcrete
import Kraken.Promising.SLR.EnvG.X64SpscAbsRunner
import Kraken.Promising.SLR.EnvG.MemValsX64Spsc
import Kraken.Promising.SLR.EnvG.X64CmpxPublic
import Kraken.Promising.SLR.EnvG.X64CmpxFinal
import Kraken.Promising.SLR.EnvG.X64RelayXchgPublic
import Kraken.Promising.SLR.EnvG.X64CmpxAbsPublic
import Kraken.Promising.SLR.EnvG.X64CmpxAbsConcrete
import Kraken.Promising.SLR.EnvG.X64CmpxAbsRunner
import Kraken.Promising.SLR.EnvG.X64MpInclAbsPublic
import Kraken.Promising.SLR.EnvG.X64MpInclAbsConcrete
import Kraken.Promising.SLR.EnvG.X64MpInclAbsRunner
import Kraken.Promising.SLR.EnvG.X64RelayAbsPublic
import Kraken.Promising.SLR.EnvG.X64RelayAbsConcrete

open Kraken.Promising.Live.Bridge

#chaink_clone' "../../SLR/EnvG/X64Treiber2Runner.lean"
  only ["x64_treiber2_envG_runner", "x64_treiber2_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsTreiber2.lean"
  only ["x64_treiber2_envG_runner_faultFree", "x64_treiber2_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/X64TreiberAbsConcrete.lean"
  only ["x64_treiber_pp_envG_verbatim_concrete"]

#chaink_clone' "../../SLR/EnvG/X64TreiberAbsRunner.lean"
  only ["x64_treiber_pp_envG_runner", "x64_treiber_pp_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsTreiberPP.lean"
  only ["x64_treiber_pp_envG_runner_faultFree", "x64_treiber_pp_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/X64VecPublish.lean"
  only ["x64_publish_movdqa_verbatim", "x64_publish_movdqa_verbatim_faultFree"]

#chaink_clone' "../../SLR/EnvG/X64VecTreiberABA.lean"
  only ["x64_treiber_aba_tagged_never"]

#chaink_clone' "../../SLR/EnvG/MemValsX64ABA.lean"
  only ["x64_treiber_aba_tagged_runner_faultFree"]

#chaink_clone' "../../SLR/EnvG/MemValsX64ABAConcrete.lean"
  only ["x64_treiber_aba_tagged_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/X64SpscPublic.lean"
  only ["x64_spsc_envG"]

#chaink_clone' "../../SLR/EnvG/X64SpscAbsPublic.lean"
  only ["x64_spsc_envG_verbatim"]

#chaink_clone' "../../SLR/EnvG/X64SpscAbsConcrete.lean"
  only ["x64_spsc_envG_verbatim_concrete"]

#chaink_clone' "../../SLR/EnvG/X64SpscAbsRunner.lean"
  only ["x64_spsc_envG_runner", "x64_spsc_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsX64Spsc.lean"
  only ["x64_spsc_envG_runner_faultFree", "x64_spsc_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/X64CmpxPublic.lean"
  only ["x64_cmpx_counter_envG"]

#chaink_clone' "../../SLR/EnvG/X64CmpxFinal.lean"
  only ["x64_cmpx_counter_envG'"]

#chaink_clone' "../../SLR/EnvG/X64RelayXchgPublic.lean"
  only ["mp_relay3_xchg_envG"]

#chaink_clone' "../../SLR/EnvG/X64CmpxAbsPublic.lean"
  only ["x64_cmpx_counter_envG_verbatim"]

#chaink_clone' "../../SLR/EnvG/X64CmpxAbsConcrete.lean"
  only ["x64_cmpx_counter_envG_verbatim_concreteN", "x64_cmpx_counter_envG_verbatim_concrete2"]

#chaink_clone' "../../SLR/EnvG/X64CmpxAbsRunner.lean"
  only ["x64_cmpx_counter_envG_runner", "x64_cmpx_counter_envG_runner_concreteN", "x64_cmpx_counter_envG_runner_concrete2", "x64_cmpx_counter_envG_runner_concrete3"]

#chaink_clone' "../../SLR/EnvG/X64MpInclAbsPublic.lean"
  only ["x64_mp_incl_envGV_verbatim"]

#chaink_clone' "../../SLR/EnvG/X64MpInclAbsConcrete.lean"
  only ["x64_mp_incl_envGV_verbatim_concrete"]

#chaink_clone' "../../SLR/EnvG/X64MpInclAbsRunner.lean"
  only ["x64_mp_incl_envGV_runner", "x64_mp_incl_envGV_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/X64RelayAbsPublic.lean"
  only ["mp_relay3_xchg_envG_verbatim"]

#chaink_clone' "../../SLR/EnvG/X64RelayAbsConcrete.lean"
  only ["mp_relay3_xchg_envG_verbatim_concrete"]
