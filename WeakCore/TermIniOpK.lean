import WeakCore.TermOwnK5
import WeakCore.TermPlantF
import WeakCore.TermNoBufOwn

/-!
# TermIniOpK: the run-wide `bufInit` exclusion of iniop (stage 2), 

`TermPlantF.BufInitPubF`/`BufInitPubT` say that no `bufInit` along a certificate run targets one of
the start's published cells (`IniZF`), nor, at a thread step, the cell the step publishes (`IniZT`).
They are the run-wide `hZr` of the typed runs' count locality `IniLoc`. Both follow from the `ownSeen`
chain of `TermOwnK5`: a published own cell has no own use along the run (`OwnXLe 0`), and a
`bufInit` needs one (`bufInit_ne_of_use`).
-/

namespace TermIniOpK
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open TermCertScope TermOwnK5 TermPlantF
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **`BufInitPubF`** from the promise-step certificate-window hypotheses. -/
theorem bufInitPubF_of [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    BufInitPubF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w Y c1 h1 hc1 th1 hth1 l hb hz
  rcases hz with ⟨hpub, hsto⟩ | ⟨cl, hsto, ho, hk0⟩
  · obtain ⟨y, bb, ib, v', e, rt, w', ad, g, hterm, hea, hwv, hl⟩ := hb
    exact bufInitIniF_pub (hV0 := hV0) hP hsc hw Y hpub hsto h1 hc1 hth1 hterm hPS hSub hSig rt w' ad g hea hwv hl
  · exact TermNoBufOwn.noBufF_noKey (hV0 := hV0) hP hsc hw Y hsto (.inl ho) hk0 hPS hSub hSig c1 h1 hc1 th1 hth1 hb

/-- **`BufInitPubT`** from the thread-step certificate-window hypotheses: a start-published cell by the `OwnXLe 0`
run from the step's source, the cell the step publishes by `bufInitIniT_pub`. -/
theorem bufInitPubT_of [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeC p k arch Sp Init MintOK c0) (hw : CertWinC p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    BufInitPubT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r X c1 h1 hc1 th1 hth1 l hb hz
  rcases hz with hz | ⟨cl, hsto, ho, hk0⟩
  rotate_left
  · exact TermNoBufOwn.noBufT_noKey (hV0 := hV0) hP hsc hw X hsto (.inl ho) hk0 hPS hSub hSig c1 h1 hc1 th1 hth1 hb
  obtain ⟨y, bb, ib, v', e, rt, w', ad, g, hterm, hea, hwv, hl⟩ := hb
  rcases hz with ⟨hpub, hsto⟩ | ⟨cl, y', a', e', rt', ws, ad', g', hsto, hown, hterm', hea', hws, hx⟩
  · obtain ⟨S, hS⟩ := X.inv.thr i th X.hth
    obtain ⟨th2, hth2, h⟩ := ownXLe0_run_noOwnUse hP (winQC hsc hw X hS) (TermViewInv.viewInv_run hV0 X.run)
      (TermOwnX2.ownXLe_start_pub X.inv X.hth hS hpub hsto) (TermMain.tidAt_cut X.inv i S) (.thread X.hc' h1) hc1 hPS hSub hSig
    obtain rfl : th2 = th1 := Option.some.inj (hth2.symm.trans hth1)
    exact bufInit_ne_of_use hterm h rt w' ad g hea hwv hl
  · exact bufInitIniT_pub (hV0 := hV0) hP hsc hw X hsto hown hterm' hea' hws hx h1 hc1 hth1 hterm hPS hSub hSig rt w' ad g hea hwv hl

end TermIniOpK

#print axioms TermIniOpK.bufInitPubF_of
#print axioms TermIniOpK.bufInitPubT_of
