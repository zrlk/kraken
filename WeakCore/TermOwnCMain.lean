import WeakCore.TermOwnCRead
import WeakCore.TermPoolStaging

/-! # TermOwnCMain: the `ownC` pool-staging member (TermMain H2)

`ownC_of_prov`: `TermPoolStaging.ownC` (= `OpenOverCrOwnC`) from
* `hsc : StepScopeF` (TermMain: `O.scope` = `TermScope.scope_of O.progScope O.runDRF0`);
* The `NewCohF`, `ReadClsFE`, `PredRdF` are proved (`tctx_newCoh`, `tctx_readCls`, `tctx_predRd`): no other premise.
No `CfgCoh c0` (`TermRiseLoc.tstep_riseLoc`); no `PubKeepF` (PK's `KeepQRS` conjunct).
-/

namespace TermOwnCMain
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem ownC_of_prov {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hsc : TermInterf.StepScopeF p k arch Sp Init MintOK c0) :
    TermPoolStaging.ownC p k arch Sp Init MintOK c0 :=
  TermOwnCRead.openOverCrOwnC_of2 hsc TermNewCoh.tctx_newCoh

#print axioms ownC_of_prov

end TermOwnCMain
