import WeakCore.TermK5R

/-!
# TermK5Z: the post-publish `bufInit` exclusion in the producers' `hZp` form (S1b, stage iv)
-/

namespace TermK5Z
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open TermCut TermSys TermCertScope TermPlantF TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **`hZp` at a promise step's certificate run**, from the raw certificate-window hypotheses (`TermK5R.bufInitPubFR`). -/
theorem hZp_of [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : WeakMem.Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (S : WeakMem.AllocLabel → Prop) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ c1 th1 c1' c3 th3 l cl, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c1 → c1.ths[j]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 j → Solo p k arch j c1' c3 →
      Certified p k arch c3 j → c3.ths[j]? = some th3 → (Cut Eg j S).sto l = some cl →
      cl.owner = some (Cut Eg j S).tid → ¬ BufInitOn th3 l :=
  fun _ _ _ _ _ _ _ h1 hth1 hpub hs h2 hc3 hth3 hcl ho =>
    TermK5R.bufInitPubFR (hV0 := hV0) hP hsc hw X ((cutSto_some.1 hcl).1) (.inl ho) h1.toSolo hth1 hpub hs h2 hc3 hth3 hPS hSub hSig

/-- **`TermPlantF.BufInitPubFR` holds**, from the raw certificate-window hypotheses. -/
theorem bufInitPubFR_of [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    BufInitPubFR p k arch Sp Init MintOK c0 :=
  fun X S => hZp_of (hV0 := hV0) hP hsc hw X S hPS hSub hSig

end TermK5Z

#print axioms TermK5Z.hZp_of
#print axioms TermK5Z.bufInitPubFR_of
