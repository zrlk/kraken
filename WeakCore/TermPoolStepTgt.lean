import WeakCore.TermHtgW1
import WeakCore.TermPoolStaging

/-! **`StepTgt` supply** at the TermMain step, with the target choice `tg := tgIn η.fp Pδ0`.
Inputs:
- the stepper's discarded slots, `Drop` and `PubShape → GdCovT`;
- the `¬ PubShape → Gd = []` (the `TKA_zfNB` last slot);
- the pre-state `MemInv`;
- the `hPd_sup` / `htgW1_sup`. -/

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

namespace TermPoolStepTgt
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- `StepTgt` at `tg := tgIn η.fp (Pδ0 …)`. -/
theorem stepTgt_supply {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    {Gd : List TermPiece.GdE}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hDr : TermPiece.Drop (CE η) (stOf c.mem c.pairs th) Gd)
    (hGc : TermPiece.PubShape cx th →
      TermPiece.GdCovT (CE η) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) Gd th)
    (hNP : ¬ TermPiece.PubShape cx th → Gd = [])
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th)) :
    TermPoolStaging.StepTgt p k arch c c' Eg i th r η cx E' Gd
      (TermPlant.tgIn η.fp (TermHtgW1.Pδ0 c c' Eg i th)) :=
  ⟨hGc, TermHtgW1.hPd_sup, fun _ _ _ _ _ hji hj hc2 hown _ => TermHtgW1.htgW1_sup X Y Z hDr hji hj hc2 hown,
    fun h => ⟨hNP h, hm⟩⟩

end TermPoolStepTgt

#print axioms TermPoolStepTgt.stepTgt_supply
