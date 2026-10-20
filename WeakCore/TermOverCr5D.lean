import WeakCore.TermOverCr5
import WeakCore.TermZwIniP

/-! # TermOverCr5D: the `promIni` premise of `overCr_ownopR` at a thread's cut

`overCr_ownopR`'s `hpi` is `TermZwIni.PromIniE` at the pre-step environment; at a cut of the
global environment it is the `SysInvN` clause `promIni` (`TermZwIniP.promIniE_cut`).
-/

namespace TermOverCr5D
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **`hpi` of `overCr_ownopR` from `promIni`.** -/
theorem hpi_of_promIni {Eg : GEnv} {c : Cfg} {i : Nat} {th : TTh} {S : AllocLabel → Prop}
    (h : PromIniOK Eg c) (hth : c.ths[i]? = some th) :
    ∀ t m, t ∈ (stOf c.mem c.pairs th).promises → (stOf c.mem c.pairs th).mem[t]? = some m →
      ∀ cl, (Cut Eg i S).sto m.loc.label = some cl → (Cut Eg i S).pfr m.loc.label ≠ none →
        InitR (Cut Eg i S) cl m.loc.label m.loc.offset :=
  TermZwIniP.promIniE_cut h hth

#print axioms hpi_of_promIni

end TermOverCr5D
