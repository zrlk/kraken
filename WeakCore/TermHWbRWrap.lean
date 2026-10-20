import WeakCore.TermPoolSupp
import WeakCore.TermFreeQWP
import WeakCore.TermA4P2

/-! # TermHWbRWrap: hWbR under A1 at `wrapTop` cells (A1 checker invariant; pre-wiring)

Note: `PfrWrapTop` is a lemma hypothesis, never a field, final premise or
`ObligationsF` entry — universally quantified over `Eg` it is FALSE (WitGap/G1);
under the A1 checker invariant it is supplied by the `SysInvN` `stoW` clause for the invariant's `Eg`.

* `hWbRUp_of_wrap`: `HWbRUp` (its `FreeP` disjunct, the `freeP_of_pieceT`) from `Ante` and `PfrWrapTop`.
* `fgnCov_of_wrap`: the amended `fgnCov` from `PfrWrapTop` alone (via `TermPoolSupp.fgnCov_of_wb`).
-/

namespace TermHWbRWrap
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper TermPool TermOverCrW TermPoolStaging TermPoolFgnCov
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (target: the `SysInvN` `stoW` clause) Every cell's type is `wrapTop`. -/
def PfrWrapTop (Eg : GEnv) : Prop :=
  ∀ l cl, Eg.sto l = some cl → TermA4.wrapTop cl.ty = true

/-- **hWbR at a `wrapTop` frontier cell**: the pre-cover's list (`OverCrG`) and, at every lost unit,
the `FreeP` disjunct (`TermA4.freeP_of_pieceT`). -/
theorem hWbRUp_of_wrap {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
    {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (hA : Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F
      cr' db' δ Gd tg j thj Sj l cl)
    (hWr : PfrWrapTop Eg) :
    TermFreeQW.HWbRUp c c' Eg (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (crPl cr pl) j thj Sj l cl := by
  obtain ⟨X, Y, Z, hOC, -, -, -, -, hji, hj, hc2, hown, hpf2⟩ := hA
  have hgf := gfoot_of X Y Z
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, -, -, hpfr2⟩ := own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hstoE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l =
      (Cut Eg j Sj).sto l := hc2.trans hpre_c.symm
  have hpf2' : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f :=
    hpfr2.trans hf
  obtain ⟨Gs, hL, hHL⟩ := hOC j thj Sj hj l cl hpre_c hown hpf
  refine ⟨Gs, hL, hHL, fun o tw b U us hv _ _ _ hP hus hb ho => .inl ?_⟩
  exact TermA4.freeP_of_pieceT (hWr l cl hs) (X.inv.clo l cl hs) (X.inv.shty l cl ⟨f, hf⟩ hs)
    (X.inv.stoNI l cl hs) hpre_c hP hus hb ho
    (fun hw => hv ⟨(WordUnit_congr (a := ⟨l, o⟩) hstoE).2 hw, Vis_pfr hpf2'⟩)

#print axioms hWbRUp_of_wrap

/-- **The amended `fgnCov` from `PfrWrapTop`** (the hypothesis is route (B)'s target). -/
theorem fgnCov_of_wrap {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hsc : TermInterf.StepScopeF p k arch Sp Init MintOK c0)
    (hWr : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
      {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
      {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell},
      Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ
        Gd tg j thj Sj l cl → PfrWrapTop Eg) :
    fgnCov p k arch Sp Init MintOK c0 :=
  TermPoolSupp.fgnCov_of_wb hsc (fun hA _ => hWbRUp_of_wrap hA (hWr hA))

#print axioms fgnCov_of_wrap

end TermHWbRWrap
