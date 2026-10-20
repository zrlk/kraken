/-
**The semantic twins clone: X64 modules, part 1**. `#chaink_clone'`
(`ChainK/Clone.lean`) re-elaborates, at the K world, the declarations of the
listed modules that the `#sem_twin` twins (`ChainK/SemTwinsX64.lean`) need:
the published theorems and the lemmas they use that mention the executable
machine. The modules are imported so that lake rebuilds this one when they
change.
-/
import Kraken.Promising.SLR.ChainK.TwinsCloneN
import Kraken.Promising.SLR.ChainK.HubsX64
import Kraken.Promising.SLR.EnvG.DekkerPublicX
import Kraken.Promising.SLR.EnvG.X64SpinPublicG
import Kraken.Promising.SLR.EnvG.X64SpinAbsPublic
import Kraken.Promising.SLR.EnvG.DekkerAbsPublic
import Kraken.Promising.SLR.EnvG.DekkerAbsConcrete
import Kraken.Promising.SLR.EnvG.RelPureEnvX64F
import Kraken.Promising.SLR.EnvG.X64VecDecls
import Kraken.Promising.SLR.EnvG.X64VecDeclsLinkAdj
import Kraken.Promising.SLR.EnvG.TakeX64Final
import Kraken.Promising.SLR.EnvG.X64DeclsLink
import Kraken.Promising.SLR.EnvG.DekkerAbsRunner
import Kraken.Promising.SLR.EnvG.X64MpIncPublic
import Kraken.Promising.SLR.EnvG.LRValMpIncPublic
import Kraken.Promising.SLR.EnvG.MemValsX64
import Kraken.Promising.SLR.EnvG.X64TreiberPublic
import Kraken.Promising.SLR.EnvG.X64TreiberAbsPublic
import Kraken.Promising.SLR.EnvG.X64Treiber2Public
import Kraken.Promising.SLR.EnvG.X64MsQueue2Public
import Kraken.Promising.SLR.EnvG.X64MsQueue2Concrete
import Kraken.Promising.SLR.EnvG.X64MsQueue2Runner
import Kraken.Promising.SLR.EnvG.X64MsQueue3Public
import Kraken.Promising.SLR.EnvG.X64MsQueue3Concrete
import Kraken.Promising.SLR.EnvG.X64MsQueue3Runner
import Kraken.Promising.SLR.EnvG.MemValsMsQueue
import Kraken.Promising.SLR.EnvG.X64Treiber2Concrete

open Kraken.Promising.Live.Bridge

#chaink_clone' "../../SLR/EnvG/DekkerPublicX.lean"
  only ["x64_dekker_public"]

#chaink_clone' "../../SLR/EnvG/X64SpinPublicG.lean"
  only ["x64_spin_counter_envG"]

#chaink_clone' "../../SLR/EnvG/X64SpinAbsPublic.lean"
  only ["x64_spin_counter_envG_verbatim"]

#chaink_clone' "../../SLR/EnvG/DekkerAbsPublic.lean"
  only ["x64_dekker_public_verbatim"]

#chaink_clone' "../../SLR/EnvG/DekkerAbsConcrete.lean"
  only ["x64_dekker_public_verbatim_concrete"]

#chaink_clone' "../../SLR/EnvG/RelPureEnvX64F.lean"
  only ["final_of_relPureSafelyQX_tsoF", "final_of_relPureSafelyQX_tsoF'"]

#chaink_clone' "../../SLR/EnvG/X64VecDecls.lean"
  only ["inv_reachableD", "faultFree_of_threadSpecD"]

#chaink_clone' "../../SLR/EnvG/X64VecDeclsLinkAdj.lean"
  only ["final_of_relPureSafelyVecD_tsoF"]

#chaink_clone' "../../SLR/EnvG/TakeX64Final.lean"
  only ["final_of_relPureSafelyQX_tsoS"]

#chaink_clone' "../../SLR/EnvG/X64DeclsLink.lean"
  only ["final_of_relPureSafelyQX_tsoFD", "final_of_relPureSafelyQX_tsoSD"]

#chaink_clone' "../../SLR/EnvG/DekkerAbsRunner.lean"
  only ["x64_dekker_public_runner", "x64_dekker_public_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/X64MpIncPublic.lean"
  only ["x64_mp_incl_envG"]

#chaink_clone' "../../SLR/EnvG/LRValMpIncPublic.lean"
  only ["x64_mp_incl_envGV"]

#chaink_clone' "../../SLR/EnvG/MemValsX64.lean"
  only ["x64_faultFree_of_valSpecs_env", "x64_faultFree_of_valSpecs", "x64_faultFree_of_relPureSpecsQXD'", "x64_faultFree_of_relPureSpecsQXD"]

#chaink_clone' "../../SLR/EnvG/X64TreiberPublic.lean"
  only ["x64_treiber_pp_envG"]

#chaink_clone' "../../SLR/EnvG/X64TreiberAbsPublic.lean"
  only ["x64_treiber_pp_envG_verbatim"]

#chaink_clone' "../../SLR/EnvG/X64Treiber2Public.lean"
  only ["x64_treiber2_envG_verbatim"]

#chaink_clone' "../../SLR/EnvG/X64MsQueue2Public.lean"
  only ["x64_msqueue2_envG_verbatim"]

#chaink_clone' "../../SLR/EnvG/X64MsQueue2Concrete.lean"
  only ["x64_msqueue2_envG_verbatim_concrete"]

#chaink_clone' "../../SLR/EnvG/X64MsQueue2Runner.lean"
  only ["x64_msqueue2_envG_runner", "x64_msqueue2_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/X64MsQueue3Public.lean"
  only ["x64_msqueue3_envG_verbatim"]

#chaink_clone' "../../SLR/EnvG/X64MsQueue3Concrete.lean"
  only ["x64_msqueue3_envG_verbatim_concrete"]

#chaink_clone' "../../SLR/EnvG/X64MsQueue3Runner.lean"
  only ["x64_msqueue3_envG_runner", "x64_msqueue3_envG_runner_concrete"]

#chaink_clone' "../../SLR/EnvG/MemValsMsQueue.lean"
  only ["x64_msqueue2_envG_runner_faultFree", "x64_msqueue3_envG_runner_faultFree", "x64_msqueue2_envG_runner_faultFree_concrete", "x64_msqueue3_envG_runner_faultFree_concrete"]

#chaink_clone' "../../SLR/EnvG/X64Treiber2Concrete.lean"
  only ["x64_treiber2_envG_verbatim_concrete"]
