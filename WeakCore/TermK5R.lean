import WeakCore.TermIniOpK
import WeakCore.TermOwnG0Defs

/-!
# TermK5R: the run-wide `bufInit` exclusion at cells published during the run (S1b, stage i)

`TermPlantF.BufInitPubF` excludes a `bufInit` along a promise step's certificate run only at the cells
published at the start (`IniZF`).  `bufInitPubFR` extends it to a cell `l` of the promiser's cut
that the run itself publishes: after the `publish` naming `l`, no `bufInit` of the run targets `l`.
`OwnXLe 1` holds at the promise start (`ownXLe_start` at `c`, then the promise step `ownXStepP_all`),
and the publish chain `TermOwnK5.ownXLe_pub_noOwnUse` gives no own use of `l` after the publish.

The window premise is `TermOwnK5.winQP` from the raw certificate fields `CertScopeP`/`CertWinP`
(the direction allowed by TermOwnK5's circularity note: nothing here discharges `certWin*`,
`CertFreshC` or `NoHoldPub`).
-/

namespace TermK5R
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open TermCut TermSys TermCertScope TermOwnK5 TermOwnK1 TermOwnX2 TermPlantF TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **No `bufInit` at a cell published during a promise step's certificate run**, after its
`publish`: `l` is a cell of the promiser's cut (own, or with a frontier). -/
theorem bufInitPubFR [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {l : AllocLabel} {cl : Cell} (hsto : Eg.sto l = some cl) (hin : cl.owner = some j ∨ Eg.pfr l ≠ none)
    {c1 c1' c2 : Cfg} {th1 th2 : TTh} (h1 : Solo p k arch j (promise c j a v w) c1)
    (hth1 : c1.ths[j]? = some th1) (hpub : TermOwnG0Defs.PubAt th1 l) (hs : c1' ∈ threadSteps p k arch c1 j)
    (h2 : Solo p k arch j c1' c2) (hc2 : Certified p k arch c2 j) (hth2 : c2.ths[j]? = some th2) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ¬ BufInitOn th2 l := by
  rintro ⟨y, bb, ib, v', e, rt, w', ad, g, hterm, hea, hwv, hl⟩
  obtain ⟨y1, a1, e1, rt1, ws1, ad1, hterm1, hea1, hws1, hx1⟩ := hpub
  obtain ⟨S, hS⟩ := X.inv.thr j th X.hth
  have h0 : OwnXLe p k arch (Cut Eg j S) j l 1 (promise c j a v w) :=
    ownXStepP_all 1 _ c a v w (ownXLe_start X.inv X.hth hS hsto hin) X.hw X.cert
  obtain ⟨th3, hth3, h⟩ :=
    ownXLe_pub_noOwnUse hP (winQP hsc hw X hS) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw) h0 (TermMain.tidAt_cutP X.inv j S) h1 hs hth1 hterm1 hea1 hws1 hx1 h2 hc2 hPS hSub hSig
  obtain rfl : th3 = th2 := Option.some.inj (hth3.symm.trans hth2)
  exact bufInit_ne_of_use hterm h rt w' ad g hea hwv hl

/-- **`bufInitPubFR` at a planted label**: a planted label is an own cell of the promiser's cut (its
last `PlantR` edge). -/
theorem bufInitPubFR_plant [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {l : AllocLabel} (hL : PlantL c Eg j th a v w l)
    {c1 c1' c2 : Cfg} {th1 th2 : TTh} (h1 : Solo p k arch j (promise c j a v w) c1)
    (hth1 : c1.ths[j]? = some th1) (hpub : TermOwnG0Defs.PubAt th1 l) (hs : c1' ∈ threadSteps p k arch c1 j)
    (h2 : Solo p k arch j c1' c2) (hc2 : Certified p k arch c2 j) (hth2 : c2.ths[j]? = some th2) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ¬ BufInitOn th2 l := by
  obtain ⟨l', -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, -⟩ := hL
  subst hal
  exact bufInitPubFR (hV0 := hV0) hP hsc hw X (cutSto_sub hc1) (.inl ho1) h1 hth1 hpub hs h2 hc2 hth2 hPS hSub hSig

end TermK5R

#print axioms TermK5R.bufInitPubFR
#print axioms TermK5R.bufInitPubFR_plant
