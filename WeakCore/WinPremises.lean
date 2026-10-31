import WeakCore.WinPubSplit
/-! (B11 P0) The window premises of the ♭ chain at a `TCtxX` configuration. -/
namespace FlatWinStart
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermOwnX2.Flat
  TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **(P0) The chain premises at a window start**: program facts, `ScopeAtB` along certified solo runs,
`ViewInv`, `TidAt` and `rini ≤ ini` at the cut. -/
theorem winPrem {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    (hck : checkProg p = .ok ()) (hsw : TermScope.ProgScopeOKW p = true) (A : SpArms p k arch Sp c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (S : AllocLabel → Prop) :
    ProgT p ∧ ProgRetIall p ∧ TermA4.ProgCkWC p ∧
      (∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ScopeAtB p i c1) ∧ TermViewInv.ViewInv c ∧
      TermTyped.TidAt i c (Cut Eg i S) ∧ ∀ l, (Cut Eg i S).rini l ≤ (Cut Eg i S).ini l := by
  have hPSc : TermScope.ProgScopeOK p = true := TermScope.ProgScopeOKW.scope hsw
  refine ⟨TermScope.progT_of_check hck,
    ⟨fun _ hd => TermScope.noIallV_of_drf _ (TermScope.ProgScopeOK.decl hPSc hd).2.1, hck⟩,
    ⟨TermA4.progCkW_of_scopeW hsw, hck⟩,
    TermCertScope.Flat.scopeAtB_solo hPSc (A.runDRF X.run), A.viewInv X.run, TermMain.tidAt_cut X.inv i S, ?_⟩
  intro l
  exact X.inv.rle l

end FlatWinStart
