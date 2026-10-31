import WeakCore.TermWdCover
import WeakCore.TermNoHold

/-! # TermPromPred: T3a `promPred` weakened to the epoch case (S10)

`TermWdCover.storeCrZ_ofM` consumes `PromPred` only at an epoch-counter unit
(its non-epoch branch is the `wd n` count).  `PromPredE` (`TermNoHold`) is that
case; `TermNoHold.promPredT` derives it from the one-step stage-A fact
`StepPredNum` and the certificate run premise at the pre-step configuration.
Under (H) the memory-count route (`storeCrZ_ofM`) is gone; `StoreCrZ` is now
`StoreNI ∧ StoreLeafPayAll`, proved in `toObligationsCX` (TermMain) without the pinned slot
cover.  This module keeps `promPred_weaken` (the old field implies the new one). -/

namespace TermPromPred
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermLiveHeld TermDwf TermWdCover
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem promPred_weaken {E : TEnv} {s : St} (h : PromPred E s) : TermNoHold.PromPredE E s :=
  fun t m ht hm hr n P hw _ => h t m ht hm hr ⟨n, P, hw⟩

/-! ## `StoreCrZ` without `WdCover` -/

#print axioms TermPromPred.promPred_weaken

end TermPromPred
