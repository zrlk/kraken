import WeakCore.EtaCertWinFst
/-! **EtaCertWinSnd** (B12 conj 2): conjunct 2 of `CertWinPNX` (the post-promise anchor `Cut (EgP …) j S1`)
from `win_gen` (EtaW) at the window start `promise c j a v w`, with the `SysInvN` base `c`.  The start facts
at the promise state (`PredHoldG`/`PromTyAOK`/`TidAt` at `EgP …`) come from W's plant chain, run on the
conjunct-1 retypes of EtaCertWinFst (conjunct 2 is not read), `certWinP1_of` and `certWinC_of`. -/
namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The plant keeps the cut cells of `Eg` (frontiers only appear). -/
theorem cutSto_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat} {i : Nat}
    {l : AllocLabel} {cl : Cell} (h : cutSto Eg i l = some cl) : cutSto (EgP Eg P N j n) i l = some cl := by
  obtain ⟨hs, ho⟩ := cutSto_some.1 h
  apply cutSto_some.2
  refine ⟨hs, ?_⟩
  rcases ho with ho | ⟨f, hf⟩
  · exact .inl ho
  · rcases e : P l with _ | f'
    · exact .inr ⟨f, by simp only [EgP, GEnv.withFp, plantG, e]; exact hf⟩
    · exact .inr ⟨f', by simp only [EgP, GEnv.withFp, plantG, e]⟩

/-- Off the plant's labels the plant keeps `ini`. -/
theorem ini_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat} {l : AllocLabel}
    (hsp : PlantSpec Eg P j n) (hl : Eg.sto l = none) : (EgP Eg P N j n).ini l = Eg.ini l := by
  rcases e : P l with _ | f
  · simp only [EgP, GEnv.withFp, plantG, e]
  · obtain ⟨cl, hcl, -⟩ := (hsp l f e).2.1
    rw [hl] at hcl
    cases hcl

/-- `TidAt` at the post-promise cut (box labels carry frontier `0`, so are never planted). -/
theorem tidAt_cutEgP {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c : Cfg}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) {j n : Nat} {P : AllocLabel → Option Ts}
    {N : AllocLabel → Nat} (hsp : PlantSpec Eg P j n) (S : AllocLabel → Prop) {a : Address}
    {v : WeakMem.Val} {w : Ts} : TermTyped.TidAt j (promise c j a v w) (Cut (EgP Eg P N j n) j S) := by
  intro th' hth' l hl
  obtain ⟨hs, hp⟩ := tidAt_cutP h j S th' hth' l hl
  refine ⟨cutSto_egP hs, ?_⟩
  have hp' : Eg.pfr l = some 0 := hp
  show (EgP Eg P N j n).pfr l = some 0
  rcases e : P l with _ | f
  · simp only [EgP, GEnv.withFp, plantG, e]; exact hp'
  · exact absurd (hsp l f e).1 (by rw [hp']; exact Option.some_ne_none 0)

/-- **(B12) `CertWinPNX`, second conjunct** (the post-promise anchor) from the named window temporaries:
`hW` (base, as `certWinP1_of`), `hWC` (as `certWinC_of`), and `hWA` (the anchor temporaries at
`Cut (EgP …) j S1`, window from `promise c j a v w`). -/
theorem certWinP2_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (hck : checkProg p = .ok ()) (hsw : TermScope.ProgScopeOKW p = true)
    (hk : k.storeDepRts = true) (A : SpArms p k arch Sp c0)
    (hWC : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh}, TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
      ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      WinTmp p k arch Eg i S c th)
    (hW : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts}, PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      WinTmp p k arch Eg j S c th)
    (hWA : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts}, PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ (HP' HS' : Res) (cr' db' : Ts → Res) S1,
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (Tot j) HP' HS' cr' db' S1 →
      WinTmpA p k arch (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        j S1 (promise c j a v w)) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts}, PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ (HP' HS' : Res) (cr' db' : Ts → Res) S1,
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (Tot j) HP' HS' cr' db' S1 →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
        NoHoldPubN p k arch (Cut Eg j S1)
          (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S1) j c1 := by
  intro c Eg Tot HP HS cr db j th a v w X HP' HS' cr' db' S1 hS1 c1 h1 h2
  have hP : ProgT p := TermScope.progT_of_check hck
  have hPSc : TermScope.ProgScopeOK p = true := TermScope.ProgScopeOKW.scope hsw
  haveI hR : ProgRetIall p := ⟨fun _ hd => TermScope.noIallV_of_drf _ (TermScope.ProgScopeOK.decl hPSc hd).2.1, hck⟩
  haveI : TermA4.ProgCkWC p := ⟨TermA4.progCkW_of_scopeW hsw, hck⟩
  haveI : TermTyped.WrIniC := TermWrSiteA.wrIniC
  -- the run facts, on conjunct 1 only
  have P1 : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0 := fun X S hS c1 h1 h2 =>
    TermDPlus.noHoldPubA_of_N (certWinP1_of hck hsw A hW X S hS c1 h1 h2)
  have hsc : TermCertScope.CertScopeP p k arch Sp Init MintOK c0 := TermCertScope.certScopeP_of hPSc A.runDRF
  have hRP : TermNoHold.CertRunP p k arch Sp Init MintOK c0 := fun X S hS c1 h1 h2 =>
    ⟨hsc X c1 h1 h2, P1 X S hS c1 h1 h2⟩
  have hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0 :=
    TermCertScope.certWinC_of_N (certWinC_of hck hsw A hWC)
  have hNP : TermPtrKey.NoFulPlRunGL p k arch :=
    TermPtrKey.noFulPlRunGL_of (hPS := pwSkel_ok) (hSub := pwSubS_ok) (hSig := pwSig_ok) hP
      (TermK2aFin.ptrRtsThreadGL_v3d (TermFulCntROf.fulCntR_of p)) (TermPtrKey.footNCB_of p pwSkel_ok pwSubS_ok pwSig_ok)
  have hRA : TermPlantF.RunAgreeF p k arch Sp Init MintOK c0 :=
    TermRunPay.runAgreeF_of (TermRunLocK.runAgreeFT3_holds1 (hV0 := A.viewInv) A.promViewLt hk hP hPSc A.runDRF
      hsc P1 hCW hNP pwSkel_ok pwSubS_ok pwSig_ok).1
  have hBP : TermPlantF.BufInitPubF p k arch Sp Init MintOK c0 :=
    TermIniOpK.bufInitPubF_of1 (hV0 := A.viewInv) hP hsc P1 pwSkel_ok pwSubS_ok pwSig_ok
  have hBPR : TermPlantF.BufInitPubFR p k arch Sp Init MintOK c0 :=
    TermK5Z.bufInitPubFR_of1 (hV0 := A.viewInv) hP hsc P1 pwSkel_ok pwSubS_ok pwSig_ok
  have hbuf : TermPlantF.BufInitIniF p k arch Sp Init MintOK c0 := TermBiiF.bufInitIniF_of (hV0 := A.viewInv) hP hRP hRA hBP hBPR pwSkel_ok pwSubS_ok pwSig_ok
  have hW2 : TermPlantF.PromWordWF p k arch Sp Init MintOK c0 := TermPlantW2.promWordW_of (hV0 := A.viewInv) hP hRP A.promViewLt hRA hBP hBPR pwSkel_ok pwSubS_ok pwSig_ok
  have hspecF : TermInterf.PlantSpecF p k arch Sp Init MintOK c0 TermPlantF.plantOf := fun X =>
    TermPlantF.plantSpec_of (hV0 := A.viewInv) hP hRP X pwSkel_ok pwSubS_ok pwSig_ok
  have hnew : TermPlantF.PromNewOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN :=
    TermPlantF.promNewOK_of (hV0 := A.viewInv) hP hRP hRA hBP hBPR hbuf hW2 pwSkel_ok pwSubS_ok pwSig_ok
  have hpl : TermPlantF.PlantPromOKF p k arch Sp Init MintOK c0 TermPlantF.plantOf TermPlantF.plantN :=
    TermPlantF.plantPromOK_of (hV0 := A.viewInv) hP hRP A.promViewLt hRA hBP hBPR hbuf hW2
    pwSkel_ok pwSubS_ok pwSig_ok
  -- the start facts at the promise state
  have hspec := hspecF X
  have hPT := TermPlantF.promTyAPostP_of hspecF hnew hpl X
  have hPH := TermPredHoldP.predHold_promX (n' := c.mem.size) X X.inv.predHold hspec (TermPredHoldP.plantHeld_of X)
  obtain ⟨epc, hpj, -⟩ := promise_inv (a := a) (v := v) (w := w) X.hth
  have hthS : (promise c j a v w).ths[j]? = some (thP th c.mem.size) := hpj
  have hrsS : TermScope.RunScope (promise c j a v w) := TermCertScope.drf_prom (A.runDRF X.run)
  have hvIS : TermViewInv.ViewInv (promise c j a v w) := TermViewInv.viewInv_prom (A.viewInv X.run) X.hw
  have hTAS := tidAt_cutEgP X.inv (N := TermPlantF.plantN c Eg j a v w) hspec S1 (a := a) (v := v) (w := w)
  have hmS : MemInv (gOf p k arch (promise c j a v w) j)
      (Cut (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) j S1)
      (stOf (promise c j a v w).mem (promise c j a v w).pairs (thP th c.mem.size)) := by
    have hg : gOf p k arch (promise c j a v w) j = gOf p k arch c j := gOf_promise
    rw [hg, epc]; exact hS1.2.2.1
  -- the `SysInvN` base at `c`
  obtain ⟨S0, hS0⟩ := X.inv.thr j th X.hth
  have hW0 := hW X S0 hS0
  exact win_gen hP hPSc X.inv X.hth hS0 (A.runDRF X.run) (A.viewInv X.run)
    (hWA X HP' HS' cr' db' S1 hS1) hthS hrsS hvIS hTAS hPH hPT
    (ScalFlat.scalIni_egP (S := S0) X.inv.scalIni hspec (ScalFlat.plantN0_of c Eg j a v w) (ScalFlat.memInv_ownHid hS0.2.2.1)) hmS (fun _ _ h => cutSto_egP h)
    (fun _ h => h) (fun _ hl => ini_egP hspec hl) (.prom a v w X.hw h1) h1 h2

/-- **(B12) `CertWinPNX`** (both conjuncts) from the named window temporaries. -/
theorem certWinP_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (hck : checkProg p = .ok ()) (hsw : TermScope.ProgScopeOKW p = true)
    (hk : k.storeDepRts = true) (A : SpArms p k arch Sp c0)
    (hWC : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh}, TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
      ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      WinTmp p k arch Eg i S c th)
    (hW : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts}, PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      WinTmp p k arch Eg j S c th)
    (hWA : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts}, PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ (HP' HS' : Res) (cr' db' : Ts → Res) S1,
      ThSysAt p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        (Tot j) HP' HS' cr' db' S1 →
      WinTmpA p k arch (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size)
        j S1 (promise c j a v w)) :
    TermCertScope.CertWinPNX p k arch Sp Init MintOK c0 :=
  fun X => ⟨certWinP1_of hck hsw A hW X, certWinP2_of hck hsw hk A hWC hW hWA X⟩

end CertWinProof
