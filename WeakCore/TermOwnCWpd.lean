import WeakCore.TermFulW
import WeakCore.TermOwnCOld

/-! # TermOwnCWpd: `overCr_old`'s `hFP` at every step kind (ownC)

`TermFulW.tctx_wpd` has no `opAtomP` restriction: its `storeUnits` branch covers every
`UnitsOp` (including `storePub`), its `fetch`/`cas` branch the RMW targets.  So `hFP` holds at
any own frontier cell, given `StepScopeF` (`TermScope.scope_of`). -/

namespace TermOwnCWpd
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem hFP_of_wpd {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {l : AllocLabel} {cl : Cell}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hpa : PromAbove (stOf r.1 r.2.1 r.2.2))
    (hsto : (CE η).sto l = some cl) (hown : cl.owner = some i) (hpf : (CE η).pfr l ≠ none) :
    ∀ t m, t ∈ (stOf c.mem c.pairs th).promises → t ∉ (stOf r.1 r.2.1 r.2.2).promises →
      (stOf c.mem c.pairs th).mem[t]? = some m → m.loc.label = l →
      ¬ WordUnit (CE η) m.loc → ∀ q S usS, TermPiece.Piece cl.ty q S → accs S = some usS → q ≤ m.loc.offset →
        m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
          TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨l, o⟩ th0 → th0 ∉ (stOf r.1 r.2.1 r.2.2).promises := by
  intro t m ht hn hmt hl hnw q S' usS hP hus h1 h2 o th0 ho1 ho2 hlo
  subst hl
  exact TermFulW.tctx_wpd hsc X Y hm hpa t m cl ht hn hmt hsto hown hpf hnw q S' usS hP hus h1 h2 o th0
    ho1 ho2 hlo

#print axioms hFP_of_wpd

end TermOwnCWpd
