import WeakCore.EtaFD
import WeakCore.ContIV
import WeakCore.WinPremises
import WeakCore.BornW
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! **EtaW** (B12 on (R′)): `NoHoldPubN` at every certified configuration of a window from a `SysInvN`
start, from `noHold_eta` (EtaN).  The holder premises `hPH`/`hPT`/`hm0`, `hbf`, `hlab`, `hnp` and the non-fresh oracle are
discharged here (SysInvN, ThSysAt, the x-free lineage EtaF, the ♭ ownership chain); the remaining inputs are
the NAMED window temporaries `WinTmp`:

* (`contB`, ContB at the cut, is DISCHARGED: ContIV `contB_of` from the base `MemInv` + `hinv.rle` + D1.)
* (`contE`, ContE at the adversarial typing, is DISCHARGED: ContIV `contE_of` from the WinAnte `MemInv`.)
* (`sup0`, `∃ b, FreshSup P b (CE η)`, is DROPPED: never consumed.  The plan parameter `P` went with it.)
* (`rini0`, the `FreshLP` rini clause at `CE η`, is DISCHARGED: read from W's `FreshLP` inside `MemInv`.)
* (`scal`, W's `ScalIni Eg` clause, is DISCHARGED: `hinv.scalIni` at the SysInvN base.)
  At an anchor it is an input `hscS` of `win_gen` (base: `hinv.scalIni`; post-promise: `ScalFlat.scalIni_egP`);
* (`oFresh`, the oracle at a fresh label of the window, is DISCHARGED: BornW `oFresh_of`, ownXLe_born.)

`win_gen` separates the window start / anchor (`cS`, `Cut Eg i S`: `WinTmpA`; `hscS`) from the
`SysInvN` base (`c`, `Cut Eg0 i S0`: `contB`); conjunct 2 of `CertWinPNX` (EtaCertWinSnd) uses it at
`cS := promise c j a v w`, `Eg := EgP …`. -/
namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- PubWinSAN's antecedents at a certified configuration `c1` of the window from `c`, anchor `Cut Eg i S`. -/
def WinAnte (p : Prog) (k : Promises.Knobs) (arch : Arch) (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) (c c1 : Cfg)
    (th1 : TTh) (ρ : Nat → Nat) (η : TEnv) (cx : Cx) : Prop :=
  Solo p k arch i c c1 ∧ Certified p k arch c1 i ∧ c1.ths[i]? = some th1 ∧ EnvOK p η ∧ Typed p cx th1.term ∧
    TvOK cx ∧ FInv ρ η th1.σs (Resume p th1.stack) cx th1.env ∧
    MemInv (gOf p k arch c1 i) (CE η) (stOf c1.mem c1.pairs th1) ∧ Ext (Cut Eg i S) (CE η) ∧
    IniAnch (Cut Eg i S) (CE η) ∧ RiniMem (Cut Eg i S) (CE η) (stOf c1.mem c1.pairs th1)

/-- **The anchor temporaries** of a window from `cS` at the anchor `Cut Eg i S` (quantified over `WinAnte`). -/
structure WinTmpA (p : Prog) (k : Promises.Knobs) (arch : Arch) (Eg : GEnv) (i : Nat)
    (S : AllocLabel → Prop) (cS : Cfg) : Prop

/-- **The named window temporaries** at a window start `c` (thread `i`, `th`, cut `Cut Eg i S`). -/
structure WinTmp (p : Prog) (k : Promises.Knobs) (arch : Arch) (Eg : GEnv) (i : Nat)
    (S : AllocLabel → Prop) (c : Cfg) (th : TTh) : Prop extends WinTmpA p k arch Eg i S c

/-- A thread with no own-count at `x` is not publishing `x`. -/
theorem own_pub_ne {p : Prog} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {th : TTh} {x : AllocLabel}
    {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word} {ad : Address}
    (hE : EnvOKB p η) (hTy : Typed p cx th.term) (hFI : FInvRB glb gnum gi ρ η th.σs (ResumeRB glb gnum gi p th.stack Rs) cx th.env Rf)
    (h0 : Rf (.own x) = 0) (hterm : th.term = .let_ y (.publish a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) : ad.label ≠ x := by
  rw [hterm] at hTy
  cases hTy with
  | let_ hop he =>
    cases hop with
    | publish hu hsh hb => exact use_own_neB hu hFI hE (Or.inl ⟨_, rfl⟩) h0 hea hws
    | publishBuf hu hsh hb => exact use_own_neB hu hFI hE (Or.inr ⟨_, _, _, rfl⟩) h0 hea hws

/-- **(B12 core, general anchor)** `NoHoldPubN` at every certified configuration `c1` of a window from `cS`,
anchor `Cut Eg i S`, where the lineage (EtaF), the ♭ chain and the oracle run from a `SysInvN` base `c`
(`Eg0`, `S0`) with `Solo c c1`; `Eg` keeps `Eg0`'s cut cells, adds no `pubd`, and keeps `ini` off `Eg0`'s cells. -/
theorem win_gen {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg0 : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {S0 : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg0 Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg0 (Tot i) (HP i) HS (cr i) (db i) S0)
    (hrs : TermScope.RunScope c) (hvI : TermViewInv.ViewInv c)
    {cS : Cfg} {thS : TTh} {Eg : GEnv} {S : AllocLabel → Prop} (hW : WinTmpA p k arch Eg i S cS)
    (hthS : cS.ths[i]? = some thS) (hrsS : TermScope.RunScope cS) (hvIS : TermViewInv.ViewInv cS)
    (hTAS : TermTyped.TidAt i cS (Cut Eg i S)) (hPHS : TermPredHold.PredHoldG Eg cS)
    (hPTS : TermMain.PromTyAOK Eg cS) (hscS : ScalFlat.ScalIni Eg) (hmS : MemInv (gOf p k arch cS i) (Cut Eg i S) (stOf cS.mem cS.pairs thS))
    (hcut : ∀ l cl, cutSto Eg0 i l = some cl → cutSto Eg i l = some cl)
    (hpub : ∀ l, Eg.pubd l → Eg0.pubd l) (hini : ∀ l, Eg0.sto l = none → Eg.ini l = Eg0.ini l)
    {E0 : TEnv} {c1 : Cfg} (hsolo : Solo p k arch i c c1) (hsoloS : Solo p k arch i cS c1)
    (hc1 : Certified p k arch c1 i) :
    NoHoldPubN p k arch E0 (Cut Eg i S) i c1 := by
  intro th1 hth1 ρ η cx hE hT htv hF hm hExt hA hR hTy hDy _hRP y a e rt ws ad hterm hea hws hns
  have hPS := TermMain.pwSkel_ok
  have hSub := TermMain.pwSubS_ok
  have hSig := TermMain.pwSig_ok
  have hWA : WinAnte p k arch Eg i S cS c1 th1 ρ η cx := ⟨hsoloS, hc1, hth1, hE, hT, htv, hF, hm, hExt, hA, hR⟩
  have hTA := TermMain.tidAt_cut hinv i S0
  have hQ := TermCertScope.Flat.scopeAtB_solo (i := i) (k := k) (arch := arch) hps hrs
  have hB0 : FlatAnchor.ContB c.lbase c.n i p th (Cut Eg0 i S0) := ContAnchor.contB_of hth hS.2.2.1 hinv.rle
  -- O1: the lineage (and its `RecFresh`) from the base only: `seedFD` at `c`, `eta_soloFD` to `c1`.
  have hF1 := EtaDyFr.eta_soloFD hP hPS hSub hSig hps hsolo hc1 hrs hTA (EtaDyFr.seedFD hinv hth hS)
  have hRc : RecFresh (gOf p k arch c1 i) i th1.nalloc := by
    obtain ⟨th1', _, hth1', _, _, _, _, _, _, _, _, _, hr⟩ := hF1
    rw [hth1] at hth1'
    cases hth1'
    exact hr
  have hbf1 : (gOf p k arch c1 i).boxFence = true := by
    obtain ⟨_, _, _, _, _, hb, _⟩ := hF1
    exact hb
  rcases EtaDyFr.pub_splitFD hF1 hth1 hterm hea hws with hin | ⟨j, hj, hjl⟩
  · -- the published label is in the base cut: owned by `i`
    obtain ⟨cl, hcl⟩ : ∃ cl, (Cut Eg0 i S0).sto ad.label = some cl := Option.ne_none_iff_exists'.mp hin
    have hEg0 : Eg0.sto ad.label = some cl := (cutSto_some.1 hcl).1
    have hclA : cutSto Eg i ad.label = some cl := hcut _ _ hcl
    have hEg : Eg.sto ad.label = some cl := (cutSto_some.1 hclA).1
    obtain ⟨cl', hcl', ho'⟩ := TermOwnX2.publish_own_cell hT hF hterm hea hws
    have h1 : (CE η).sto ad.label = some cl := hExt.2.2.2.2.1 _ _ hclA
    have h2 : (CE η).tid = i := hExt.2.2.2.1
    have h3 : η.sto ad.label = some cl := h1
    rw [hcl'] at h3
    cases h3
    have ho : cl.owner = some i := by rw [ho']; exact congrArg some h2
    have hlab : (∃ cl0, Eg.sto ad.label = some cl0 ∧ cl0.owner = some i) ∨ Eg.ini ad.label = 0 :=
      .inl ⟨cl, hEg, ho⟩
    have hnp : ¬ Eg.pubd ad.label := by
      intro hpd
      have hz := ((hinv.ownPub _ (hpub _ hpd)).2 (by rw [hEg0]; exact fun h0 => by cases h0)).1 i th hth
      have h00 := FlatWinStart.ownXLeB_start_le (n := 0) hinv hth hS hEg0 (.inl ho) (Nat.le_of_eq hz) hB0
      have h01 := ownXLe_runAllS hP hPS hSub hSig hQ hvI h00 hTA hsolo hc1
      obtain ⟨th', hth', ρ', η', cx', Rf, Rs, hE', hTy', hFI', hz'⟩ := OwnXLeB.rf_zero h01
      rw [hth1] at hth'
      cases hth'
      exact own_pub_ne hE' hTy' hFI' hz' hterm hea hws rfl
    have hO := eta_oracle hP hPS hSub hSig hQ hvI (FlatWinStart.ownXLeB_start hinv hth hS hEg0 (.inl ho) hB0) hTA
      hsolo hth1 hterm hea hws hinv.rle
    exact noHold_eta hP hPS hSub hSig hps hthS hsoloS hc1 hth1 hrsS hvIS hTAS hPHS hPTS hmS hE hT htv
      hF hm hExt hA hR hterm hea hws hns (ContAnchor.contE_of hth1 hm) hbf1 hO hlab hnp hscS hTy hDy hRc
  · -- the published label is a fresh label of the window
    have hG := hinv.fresh i th hth j hj
    have hjl' : ad.label = freshLabel c.lbase c.n i j := hjl
    have hlab : (∃ cl0, Eg.sto ad.label = some cl0 ∧ cl0.owner = some i) ∨ Eg.ini ad.label = 0 :=
      .inr (by rw [hjl', hini _ hG.1]; exact hG.2.2.1)
    have hnp : ¬ Eg.pubd ad.label := fun hpd =>
      (hinv.ownPub _ (hpub _ hpd)).1 (by rw [hjl']; exact hG.2.2.2.1)
    have hO := oFresh_of hP hps hinv hth hS hrs hvI hB0 c1 th1 y a e rt ws ad j hsolo hc1 hth1 hterm hea hws hj hjl'
    exact noHold_eta hP hPS hSub hSig hps hthS hsoloS hc1 hth1 hrsS hvIS hTAS hPHS hPTS hmS hE hT htv
      hF hm hExt hA hR hterm hea hws hns (ContAnchor.contE_of hth1 hm) hbf1 hO hlab hnp hscS hTy hDy hRc

/-- **(B12 core)** `NoHoldPubN` at every certified configuration of a window from a `SysInvN` start. -/
theorem win_core {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hrs : TermScope.RunScope c) (hvI : TermViewInv.ViewInv c) (hW : WinTmp p k arch Eg i S c th)
    {E0 : TEnv} {c1 : Cfg} (hsolo : Solo p k arch i c c1) (hc1 : Certified p k arch c1 i) :
    NoHoldPubN p k arch E0 (Cut Eg i S) i c1 :=
  win_gen hP hps hinv hth hS hrs hvI hW.toWinTmpA hth hrs hvI (TermMain.tidAt_cut hinv i S)
    hinv.predHold hinv.promTy hinv.scalIni hS.2.2.1 (fun _ _ h => h) (fun _ h => h) (fun _ _ => rfl) hsolo hsolo hc1

/-- **(B12) `CertWinCNX`** from the named window temporaries. -/
theorem certWinC_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (hck : checkProg p = .ok ()) (hsw : TermScope.ProgScopeOKW p = true)
    (A : SpArms p k arch Sp c0)
    (hW : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh}, TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
      ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      WinTmp p k arch Eg i S c th) :
    TermCertScope.CertWinCNX p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r X S hS c1 h1 h2
  obtain ⟨hP, hRI, hCk, -, hvI, -, -⟩ := FlatWinStart.winPrem hck hsw A X S
  haveI := hRI
  haveI := hCk
  exact win_core hP (TermScope.ProgScopeOKW.scope hsw) X.inv X.hth hS (A.runDRF X.run) hvI (hW X S hS) h1 h2

/-- **(B12) `CertWinPNX`, first conjunct** (the pre-promise anchor): the window from `c` through the promise. -/
theorem certWinP1_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (hck : checkProg p = .ok ()) (hsw : TermScope.ProgScopeOKW p = true)
    (A : SpArms p k arch Sp c0)
    (hW : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts}, PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      WinTmp p k arch Eg j S c th) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts}, PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
        NoHoldPubN p k arch (Cut Eg j S) (Cut Eg j S) j c1 := by
  intro c Eg Tot HP HS cr db j th a v w X S hS c1 h1 h2
  have hP : ProgT p := TermScope.progT_of_check hck
  have hPSc : TermScope.ProgScopeOK p = true := TermScope.ProgScopeOKW.scope hsw
  haveI : ProgRetIall p := ⟨fun _ hd => TermScope.noIallV_of_drf _ (TermScope.ProgScopeOK.decl hPSc hd).2.1, hck⟩
  haveI : TermA4.ProgCkWC p := ⟨TermA4.progCkW_of_scopeW hsw, hck⟩
  exact win_core hP hPSc X.inv X.hth hS (A.runDRF X.run) (A.viewInv X.run) (hW X S hS) (.prom a v w X.hw h1) h2

end CertWinProof
