import WeakCore.TermFgnClos
import WeakCore.TermRiniCohW
import WeakCore.TermOwnCMain
import WeakCore.TermCellOwn
import WeakCore.TermPubCons
import WeakCore.TermPredHoldP
import WeakCore.TermPredStoreFree
import WeakCore.TermPredHoldW
import WeakCore.TermPlantWin
import WeakCore.TermZwIniP
import WeakCore.TermInterf
import WeakCore.TermPlantFrz
import WeakCore.TermBal
import WeakCore.TermInit
import WeakCore.TermFreshU
import WeakCore.TermDwf
import WeakCore.TermWdCover
import WeakCore.TermIall
import WeakCore.TermK5Z
import WeakCore.TermBufPubT
import WeakCore.TermRunLocK
import WeakCore.TermBiiF
import WeakCore.TermNoHold
import WeakCore.TermPlantF
import WeakCore.TermPlantS
import WeakCore.TermPlantP
import WeakCore.TermStoreNI
import WeakCore.TermPromNU
import WeakCore.TermSeenHid
import WeakCore.TermShty
import WeakCore.TermOwnFresh
import WeakCore.TermOwnNet
import WeakCore.TermCohLe
import WeakCore.TermCertScope
import WeakCore.TermRmw
import WeakCore.TermPinBIOf
import WeakCore.TermWin
import WeakCore.TermB5
import WeakCore.TermPromPred
import WeakCore.TermStepPred
import WeakCore.TermPlantW2
import WeakCore.TermPlantH
import WeakCore.TermPromStep
import WeakCore.TermMsgWords
import WeakCore.TermBNamed
import WeakCore.TermBoxOwn
import WeakCore.TermVwrLt
import WeakCore.TermBoxPV
import WeakCore.TermRunPay
import WeakCore.TermBiiT
import WeakCore.TermRunPayT
import WeakCore.TermRunLoc
import WeakCore.TermPtrStab
import WeakCore.TermUndefLowT
import WeakCore.TermPromAboveG
import WeakCore.TermPlantFul
import WeakCore.TermPlantOpG
import WeakCore.TermOwnCoh
import WeakCore.TermPromAlloc
import WeakCore.TermViewInvH
import WeakCore.TermUndefInv
import WeakCore.TermPlantHidOf
import WeakCore.TermOwnPub
import WeakCore.TermPlantPair
import WeakCore.TermPlantR1
import WeakCore.TermIniOpK
import WeakCore.TermFootBPK
import WeakCore.TermDBWire
import WeakCore.TermFgnCnt
import WeakCore.TermFulCntROf
import WeakCore.TermPlantAtB
import WeakCore.TermFootNCBOf
import WeakCore.TermWrSiteA
import WeakCore.TermPoolThread
import WeakCore.TermPoolResplit
import WeakCore.TermSelfPlantK
import WeakCore.TermHbiPOf
import WeakCore.TermFootBPKB
import WeakCore.TermOverCrA3
import WeakCore.TermPoolF1
import WeakCore.TermPoolTagOwn
import WeakCore.TermPoolBal
import WeakCore.TermPoolTagW
import WeakCore.TermHWbRWrap
import WeakCore.TermFgnNew
import WeakCore.TermStoreCrZE
import WeakCore.TermScopeWCk
import WeakCore.TermTidLbl
import WeakCore.TermScalIni
/-! **TermMainPre**: the declarations of `TermMain` that the certificate-window proof uses
(`pwSkel_ok`, `pwSubS_ok`, `pwSig_ok`, `SpArms`), placed below that proof so that `TermMain` can import it.
Names and bodies are unchanged. -/
namespace TermMain
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-- Counted words read only the skeleton. -/
theorem pwSkel_ok : PwSkel := fun _ _ h ws => (TermK2a.pubWords_of_skel h).2.1 ws

/-- Subsumption keeps the counted words. -/
theorem pwSubS_ok : PwSubS := fun _ _ _ h σs c d ws => (TermK2a.pubWords_subS h σs c d).2.1 ws

/-- Counted words read only the signature. -/
theorem pwSig_ok : PwSig := TermK2a.pubWords_sig

/-- (spawn) **The run-closed start facts** of `toObligationsCX` over `StepsG … Sp` (at `Sp := ⊥`
from the old start facts, `SpArms.bot`; at `Sp := Spawn …` the arms). -/
structure SpArms (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (c0 : Cfg) : Prop where
  viewInv : TermViewInv.ViewInvR p k arch Sp c0
  promNodup : TermBal.PromNodupR p k arch Sp c0
  runDRF : TermScope.RunScopeR p k arch Sp c0
  promViewLt : TermPlantF.PromViewLtR p k arch Sp c0
  promPos : TermPlantAtPos.PromPosR p k arch Sp c0

end TermMain
