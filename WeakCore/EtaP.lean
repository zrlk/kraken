import WeakCore.EtaS
import WeakCore.ShadowPubStep
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! **EtaP**: the resource-free shadow publish on N.  The port of
`pub_stepS`/`pubBuf_stepS` (ShadowPubStep) with `FInvB`/`ResumeBN` and no `PubWin`; the typing manipulation is the one
of NLayer's `tstepM_publishBN`, the env is the shadow env `shE` (frontier only, `pubP`) and `MemInvB` comes from
`FlatShadowPub.MemInv_publishSB`. -/
namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The shadow env of a publish of `lab` at `V`: only the frontier changes. -/
abbrev shE (η : TEnv) (lab : AllocLabel) (V : Ts) : TEnv := η.withStoB η.sto η.ini (pubP η lab V)

theorem ext_shE (η : TEnv) (lab : AllocLabel) (V : Ts) : ExtB (CE η) (CE (shE η lab V)) := by
  have hx := FlatShadowPub.envShrink_pubS η lab V
  exact ⟨Coh_CEB _, rfl, hx.1.symm, hx.2.1.symm, hx.2.2.1.sto, hx.2.2.1.ini, hx.2.2.1.pfr, fun _ h => h,
    hx.2.2.1.box, Nat.le_refl _, CohR_CEB _, hx.2.2.1.rini⟩

theorem sup_shE {P : Plan} {b : Nat} {η : TEnv} {lab : AllocLabel} {V : Ts} (hl : η.sto lab ≠ none)
    (hs : FreshSup P b (CE η)) : FreshSup P b (CE (shE η lab V)) := by
  have hne : ∀ l, P.Tail b l → l ≠ lab := fun l ht e => hl (by rw [← e]; exact hs.sto l ht)
  refine ⟨hs.sto, hs.box, hs.ini, hs.rini, fun l ht => ?_, hs.seen, hs.pay⟩
  show pubP η lab V l = none
  simp only [pubP, if_neg (hne l ht)]
  exact hs.pfr l ht

theorem shE_ini (η : TEnv) (lab : AllocLabel) (V : Ts) : (CE (shE η lab V)).ini = (CE η).ini := rfl
theorem shE_rini (η : TEnv) (lab : AllocLabel) (V : Ts) : (CE (shE η lab V)).rini = (CE η).rini := rfl
theorem shE_sto (η : TEnv) (lab : AllocLabel) (V : Ts) : (CE (shE η lab V)).sto = (CE η).sto := rfl

/-- **(L3) The shadow publish on N.** -/
theorem pub_stepN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ y (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hsc : PubScope cx a)
    (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ E1, ThInvEBN g.lbase g.n g.i p E1 r.2.2 ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧
      (E1 = CE η ∨ ∃ lab V, η.sto lab ≠ none ∧ E1 = CE (shE η lab V)) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu, hsh, hb⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) ∧
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind y (.ptr .pub u) = .ok c' := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨hi1, lab, c, pw, μr, ru, hea, hpw, hsto, hcty, hown, hacc, hl⟩ := ownPtr_invB hu hi
    have hwsv : [pw].map (·.val) = [.loc ⟨lab, 0⟩ 0] := by simp [hpw]
    obtain ⟨s1, s2, s3, s4⟩ :=
      pubCell_sideB hE htv (FInvB_monoK (fun _ _ _ => trivial) hi1) hu hsh hsc hcty hacc
    have hx : ExtB η (shE η lab (stOf mem pairs th).vs.vWr) :=
      Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _)
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (y, .ptr .pub ru, [pw]) :: th.env } (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    have hvr : (VRF False) ρ (shE η lab (stOf mem pairs th).vs.vWr) (.ptr .pub u) (shp (.ptr .pub ru)) [pw] := by
      simp only [VRF, VRb2]
      exact ⟨⟨lab, 0⟩, c, hwsv, rfl, hsto, hcty,
        ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP],
          Or.inr (Or.inr ⟨hown, Or.inr (fun N e h => hacc (by rw [h]; rfl))⟩)⟩, hacc⟩
    exact ⟨CE (shE η lab (stOf mem pairs th).vs.vWr),
      ⟨ρ, shE η lab (stOf mem pairs th).vs.vWr, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, hck⟩ hx.2.1, htv',
        bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (Lay_ptr_remode hl rfl rfl),
        retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      FlatShadowPub.MemInv_publishSB hm hsto hown s1 s2 s3 s4,
      Or.inr ⟨lab, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩
  | publishBuf hu hsh hb =>
    obtain ⟨n, k, u, c₁, hu, hsh, hb⟩ : ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) ∧
        Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true ∧
        c₁.bind y (.refine (.loc .pub (.array n u)) (.ini k)) = .ok c' := ⟨_, _, _, _, hu, hsh, hb⟩
    obtain ⟨hi1, μr, nr, ur, ψ, wsb, hea, hvb, hlay⟩ := ownBuf_invB (bkG := False) hu hi
    have hl := hlay .pub .pub rfl rfl
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (y, .refine (.loc .pub (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, hir⟩ := hvb
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat, hFU, hmode, hini⟩
    · have hvr : (VRF False) ρ η (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VRF, VRb2]; exact ⟨Or.inl ⟨hnull, e0, he0⟩, IniR_mono (TEnv.selIni_le_ini η _) hir.1,
          fun _ => Or.inr hir.1⟩
      exact ⟨CE η, ⟨ρ, η, c', rfl, hE, ⟨he, hck⟩, htv', bind_FInvB hb hi1 hvr hl,
        retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_fenceB hm, Or.inl rfl⟩
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c.owner = some η.tid := hmode
      have hx : ExtB η (shE η ad.label (stOf mem pairs th).vs.vWr) :=
        Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _)
      have hvr : (VRF False) ρ (shE η ad.label (stOf mem pairs th).vs.vWr)
          (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VRF, VRb2]
        exact ⟨Or.inr ⟨ad, c, _, hws, hsto, hat, .refl,
          ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP],
            Or.inr (Or.inr ⟨hown, Or.inr hini⟩)⟩,
          (IniAt_mono (modeIni_le_ini _ _ _) hini)⟩, IniR_mono (TEnv.selIni_le_ini η _) hir.1,
            fun _ => Or.inr hir.1⟩
      have hcu : Ty.coupledOKIn c₁.ke (.array n u) = true := by
        simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
      have htbu : tb c₁.ke.length (.array n u) = true := by
        have h := (use_TvOK hu htv).2.1
        rw [← (use_TvOK hu htv).2.2] at h
        simpa [tb] using h
      have hcp := coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu
      obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
      exact ⟨CE (shE η ad.label (stOf mem pairs th).vs.vWr),
        ⟨ρ, shE η ad.label (stOf mem pairs th).vs.vWr, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, hck⟩ hx.2.1, htv',
          bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr hl, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
        FlatShadowPub.MemInv_publishSB hm hsto hown
          (fun b S hseg ha => by
            rcases hseg with ⟨-, rfl, -⟩ | ⟨N, usS, j, hT, -, -, -⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · have e1 := AtOff_arr_here hat hT ha (by simp [cl, accs])
              rw [hT] at e1
              simp only [cl, Ty.array.injEq] at e1
              obtain ⟨-, rfl⟩ := e1
              have := hcp
              simp only [cl, Ty.coupledOK, Ty.coupledOKIn] at this; exact TearOK_of_cplB this)
          (by
            rcases LayT_of_CellOKB hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]; exact hcp)
          (by
            rcases LayT_of_CellOKB hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              have hnu : Ty.noOwnIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
              exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
                (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) _ hnu htbu)
          (by
            rcases LayT_of_CellOKB hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              exact TermC1.drf1_cl_frameR ρ hi1.2.2.2.2.2.2.2.2.2.2 htbu
                (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))),
        Or.inr ⟨ad.label, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩

/-! (route (a), shadow `region` / `intoRgn`): the publish-free ♭ chains (EtaFD / EtaR) take `region`
and `intoRgn` on an own cell to the shadow env `shE η lab vWr` (pfr set, `seen` untouched), as `pub_stepD` does
for `publish`: the `.rgn` mode is the `pub` clause, met by its owner disjunct.  No `NoHold`, no new premise. -/

/-- The own pointer's `VRF` at the shadow env, as a `pub` pointer (owner disjunct). -/
theorem shE_ptr_VRB {ρ : Nat → Nat} {η : TEnv} {u : Ty} {rt : Shp} {ws : List Word} (V : Ts) {ad : Address}
    (hv : (VRF False) ρ η (.ptr .own u) rt ws) (had : ws.map (·.val) = [.loc ad 0]) :
    (VRF False) ρ (shE η ad.label V) (.ptr .pub u) rt ws := by
  simp only [VRF, VRb2] at hv ⊢
  obtain ⟨a, c, h1, h2, h3, h4, hm, h6⟩ := hv
  have e : a = ad := by rw [h1] at had; simpa using had
  subst e
  exact ⟨a, c, h1, h2, h3, h4, ⟨(η.pfr a.label).getD V, by simp [TEnv.withStoB, pubP],
    Or.inr (Or.inr ⟨hm, Or.inr (fun N e h => h6 (by rw [h]; rfl))⟩)⟩, h6⟩

/-- The own buffer locative's `VRF` at the shadow env, as a `pub` locative (owner disjunct). -/
theorem shE_buf_VRB {ρ : Nat → Nat} {η : TEnv} {t : Ty} {ψ : Pred} {rt : Shp} {ws : List Word} (V : Ts)
    {ad : Address} (hv : (VRF False) ρ η (.refine (.loc .own t) ψ) rt ws) (had : ws.map (·.val) = [.loc ad 0]) :
    (VRF False) ρ (shE η ad.label V) (.refine (.loc .pub t) ψ) rt ws := by
  simp only [VRF, VRb2] at hv ⊢
  obtain ⟨hv, hir⟩ := hv
  rcases hv with ⟨hnull, -, -⟩ | ⟨a, c, U, hws, hsto, hat, hFU, hmode, hini⟩
  · rw [hnull] at had; simp at had
  · have e : a = ad := by rw [hws] at had; simpa using had
    subst e
    exact ⟨Or.inr ⟨a, c, U, hws, hsto, hat, hFU, ⟨(η.pfr a.label).getD V, by simp [TEnv.withStoB, pubP],
      Or.inr (Or.inr ⟨hmode, Or.inr hini⟩)⟩, IniAt_mono (modeIni_le_ini _ _ _) hini⟩,
      IniR_mono (TEnv.selIni_le_ini η _) hir.1, fun _ => Or.inr hir.1⟩

/-- **Shadow `region`** (the `pub_stepD` shape). -/
theorem rgn_stepD {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {rn pn tn : String} {e : Expr}
    (hterm : th.term = .region a rn pn tn e)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hcpl : RgnCpl cx a) (hsc : PubScope cx a)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ E1, ThInvEB g.lbase g.n g.i p E1 r.2.2 ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧
      (E1 = CE η ∨ ∃ lab V, η.sto lab ≠ none ∧ E1 = CE (shE η lab V)) := by
  have hT0 := hT
  rw [hterm] at hT0 hCk
  have hT1 := hT0
  have hfe := fence_region (g := g) (mem := mem) (pairs := pairs) hterm
  cases hT0 with
  | region hu hrc hb1 hb2 he =>
    obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
    obtain ⟨μ', u', rfl, -, -⟩ := eskel_eq_ptr (by simpa [close, substTs, skel, etok] using hl.2.1)
    have hv0 := hv
    simp only [VRF, VRb2] at hv0
    obtain ⟨ad, c0, hws, -, hsto, hcty, hmode, hacc⟩ := hv0
    have hown : c0.owner = some η.tid := hmode
    have hF := pubTyFactsB hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
      (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1) (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
    have hx : ExtB η (shE η ad.label (stOf mem pairs th).vs.vWr) :=
      Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _)
    have hEs : EnvOKB p (shE η ad.label (stOf mem pairs th).vs.vWr) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    have hxb := Ext_bumpRB hEs.2.1
    have hf := bind_FInvB hb2 (bind_FInvB (rt := .ptr (.rgn (.lit 0)) _) hb1
      (push_FInvB rn (ridNext (shE η ad.label (stOf mem pairs th).vs.vWr)) (FInv_extB hE.2.1 hx hi1))
      (region_ptr_VRB_pub (bkG := False) _ (shE_ptr_VRB _ hv hws)) (region_ptr_Lay hl)) region_tok_VRB region_tok_Lay
    refine ⟨by simp only [tstep, hterm, hea]; simp, fun r hr => ?_⟩
    have hs := hfe r hr
    simp only [tstep, hterm, hea, List.mem_singleton] at hr
    subst hr
    refine ⟨CE (shE η ad.label (stOf mem pairs th).vs.vWr),
      ⟨_, bumpRB (shE η ad.label (stOf mem pairs th).vs.vWr), _, CE_bumpRB _,
        ⟨hEs.1, hxb.1, hxb.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, TermA4.CkW_region hCk hu hb1 hb2⟩ (hxb.2.1.trans hx.2.1),
        region_TvOK hu (fun h => by simpa [tb] using h) (fun h => by simpa [mg] using h) hb1 hb2 htv,
        FInv_extB hEs.2.1 hxb (by simpa [withS] using hf),
        retPw_skel hPS hRP (skel_subst_eq (by rw [bind_ret hb2, bind_ret hb1, push_ret, skel_shiftI, use_ret hu]) th.σs 0 0 0),
        hDy.sameW (fun _ => by rw [hterm]; rfl) (hxb.2.1.trans hx.2.1)⟩,
      ?_, Or.inr ⟨ad.label, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩
    rw [hs]
    exact FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2
  | regionBuf hu hrc hb1 hb2 he =>
    obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
    obtain ⟨μ', u', ψ', rfl⟩ := eskel_eq_refloc (by simpa [close, substTs, skel, rf, etok] using hl.2.1)
    have hv0 := hv
    simp only [VRF, VRb2] at hv0
    obtain ⟨hv1, -⟩ := hv0
    rcases hv1 with ⟨hnull, -, -⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, -⟩
    · -- a null handle (an empty buffer): only the fence, at `CE η`
      obtain ⟨c, hc, hvc, hk, hcase⟩ := region_stepKB hT1 hCk hi htv (ridNext η)
        (fun rt' ws' ad' hea' hws' => by rw [hea] at hea'; cases hea'; rw [hnull] at hws'; simp at hws')
      have hf : FInvB g.lbase g.n g.i (vcons (ridNext η) ρ) η th.σs (ResumeB g.lbase g.n g.i p th.stack) c
          ((tn, .tok (.lit 0) none, []) :: (pn, .refine (.loc (.rgn (.lit 0)) u') ψ', ws) :: th.env) := by
        rcases hcase with ⟨μ2, u2, ws2, hea2, hf2⟩ | ⟨μ2, u2, ψ2, ws2, hea2, hf2⟩
        · rw [hea] at hea2; cases hea2
        · rw [hea] at hea2; cases hea2; exact hf2
      have hxb := Ext_bumpRB hE.2.1
      refine ⟨by simp only [tstep, hterm, hea]; simp, fun r hr => ?_⟩
      have hs := hfe r hr
      simp only [tstep, hterm, hea, List.mem_singleton] at hr
      subst hr
      refine ⟨CE η, ⟨_, bumpRB η, c, CE_bumpRB η, ⟨hE.1, hxb.1, hxb.2.2.2.2.2.2.2.2.2.2.1⟩, hc.wit hxb.2.1, hvc,
          FInv_extB hE.2.1 hxb (by simpa [withS] using hf), retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0),
          hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩, ?_, Or.inl rfl⟩
      rw [hs]
      exact MemInv_fenceB hm
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBufB hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat
        (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1 (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      have hx : ExtB η (shE η ad.label (stOf mem pairs th).vs.vWr) :=
        Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _)
      have hEs : EnvOKB p (shE η ad.label (stOf mem pairs th).vs.vWr) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
      have hxb := Ext_bumpRB hEs.2.1
      have hf := bind_FInvB hb2 (bind_FInvB (rt := .refine (.loc (.rgn (.lit 0)) _) _) hb1
        (push_FInvB rn (ridNext (shE η ad.label (stOf mem pairs th).vs.vWr)) (FInv_extB hE.2.1 hx hi1))
        (region_buf_VRB_pub (bkG := False) _ (shE_buf_VRB _ hv hws)) (region_buf_Lay hl)) region_tok_VRB region_tok_Lay
      refine ⟨by simp only [tstep, hterm, hea]; simp, fun r hr => ?_⟩
      have hs := hfe r hr
      simp only [tstep, hterm, hea, List.mem_singleton] at hr
      subst hr
      refine ⟨CE (shE η ad.label (stOf mem pairs th).vs.vWr),
        ⟨_, bumpRB (shE η ad.label (stOf mem pairs th).vs.vWr), _, CE_bumpRB _,
          ⟨hEs.1, hxb.1, hxb.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, TermA4.CkW_regionBuf hCk hu hb1 hb2⟩ (hxb.2.1.trans hx.2.1), regionBuf_TvOK hu hb1 hb2 htv,
          FInv_extB hEs.2.1 hxb (by simpa [withS] using hf),
          retPw_skel hPS hRP (skel_subst_eq (by rw [bind_ret hb2, bind_ret hb1, push_ret, skel_shiftI, use_ret hu]) th.σs 0 0 0),
          hDy.sameW (fun _ => by rw [hterm]; rfl) (hxb.2.1.trans hx.2.1)⟩,
        ?_, Or.inr ⟨ad.label, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩
      rw [hs]
      exact FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2

/-- **Shadow `intoRgn`** (the `pub_stepD` shape, region-moded result). -/
theorem into_stepD {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.intoRgn rn a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hcpl : RgnCpl cx a) (hsc : PubScope cx a)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ E1, ThInvEB g.lbase g.n g.i p E1 r.2.2 ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧
      (E1 = CE η ∨ ∃ lab V, η.sto lab ≠ none ∧ E1 = CE (shE η lab V)) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | intoRgnBuf hr hu hrc hb =>
    rename_i c₁ r n k u
    obtain ⟨hi1, μr, nr, ur, ψ, wsb, hea, hvb, hlay⟩ := ownBuf_invB (bkG := False) hu hi
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    have hl := hlay (.rgn r) (.rgn (.lit 0)) (by simp [skelM]) (by simp [modeC, idxC, ofMs])
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, hir⟩ := hvb
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, hini⟩
    · have hvr : (VRF False) ρ η (.refine (.loc (.rgn r) (.array n u)) (.ini k))
          (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ)) wsb := by
        simp only [VRF, VRb2]; exact ⟨Or.inl ⟨hnull, e0, he0⟩, IniR_mono (TEnv.selIni_le_ini η _) hir.1,
          fun _ => Or.inl (fun a h => by rw [hnull] at h; simp at h)⟩
      exact ⟨CE η, ⟨ρ, η, c', rfl, hE, ⟨he, hck⟩, htv', bind_FInvB hb hi1 hvr hl,
          retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_fenceB hm, Or.inl rfl⟩
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBufB hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat
        (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1 (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      have hx : ExtB η (shE η ad.label (stOf mem pairs th).vs.vWr) :=
        Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _)
      have hvr : (VRF False) ρ (shE η ad.label (stOf mem pairs th).vs.vWr)
          (.refine (.loc (.rgn r) (.array n u)) (.ini k)) (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ)) wsb := by
        simp only [VRF, VRb2]
        exact ⟨Or.inr ⟨ad, c0, _, hws, hsto, hat, .refl,
          ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP],
            Or.inr (Or.inr ⟨hown, Or.inr hini⟩)⟩, IniAt_mono (modeIni_le_ini _ _ _) hini⟩,
          IniR_mono (TEnv.selIni_le_ini η _) hir.1, fun _ => Or.inr hir.1⟩
      exact ⟨CE (shE η ad.label (stOf mem pairs th).vs.vWr),
        ⟨ρ, shE η ad.label (stOf mem pairs th).vs.vWr, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, hck⟩ hx.2.1, htv',
          bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr hl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0),
          hDy.letW hterm rfl⟩,
        FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2,
        Or.inr ⟨ad.label, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩
  | intoRgn hr hu hrc hb =>
  rename_i c₁ r u
  obtain ⟨hi1, lab, c0, pw, μr, ru, hea, hpw, hsto, hcty, hown, hacc, hl⟩ := ownPtr_invB hu hi
  have hwsv : [pw].map (·.val) = [.loc ⟨lab, 0⟩ 0] := by simp [hpw]
  have hF := pubTyFactsB hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
    (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1)
    (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
  have hx : ExtB η (shE η lab (stOf mem pairs th).vs.vWr) :=
    Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _)
  have key : tstep g mem pairs th =
      [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
        withS { th with term := e, env := (x, .ptr (.rgn (.lit 0)) ru, [pw]) :: th.env }
          (fenceS (stOf mem pairs th) .st))] := by
    simp only [tstep, hterm, evalOp, hea]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : (VRF False) ρ (shE η lab (stOf mem pairs th).vs.vWr) (.ptr (.rgn r) u)
      (shp (.ptr (.rgn (.lit 0)) ru)) [pw] := by
    simp only [VRF, VRb2]
    exact ⟨⟨lab, 0⟩, c0, hwsv, rfl, hsto, hcty,
      ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP],
        Or.inr (Or.inr ⟨hown, Or.inr (fun N e h => hacc (by rw [h]; rfl))⟩)⟩, hacc⟩
  have hlay : Lay th.σs (.ptr (.rgn r) u) (.ptr (.rgn (.lit 0)) ru) [pw] :=
    Lay_ptr_remode hl (by simp [skelM]) (by simp [modeC, idxC, ofMs])
  exact ⟨CE (shE η lab (stOf mem pairs th).vs.vWr),
    ⟨ρ, shE η lab (stOf mem pairs th).vs.vWr, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, hck⟩ hx.2.1, htv',
      bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0),
      hDy.letW hterm rfl⟩,
    FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2,
    Or.inr ⟨lab, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩

/-- **Shadow `region`** (the `pub_stepD` shape). -/
theorem rgn_stepN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {rn pn tn : String} {e : Expr}
    (hterm : th.term = .region a rn pn tn e)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hcpl : RgnCpl cx a) (hsc : PubScope cx a)
    (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel)
    (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ E1, ThInvEBN g.lbase g.n g.i p E1 r.2.2 ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧
      (E1 = CE η ∨ ∃ lab V, η.sto lab ≠ none ∧ E1 = CE (shE η lab V)) := by
  have hT0 := hT
  rw [hterm] at hT0 hCk
  have hT1 := hT0
  have hfe := fence_region (g := g) (mem := mem) (pairs := pairs) hterm
  cases hT0 with
  | region hu hrc hb1 hb2 he =>
    obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
    obtain ⟨μ', u', rfl, -, -⟩ := eskel_eq_ptr (by simpa [close, substTs, skel, etok] using hl.2.1)
    have hv0 := hv
    simp only [VRF, VRb2] at hv0
    obtain ⟨ad, c0, hws, -, hsto, hcty, hmode, hacc⟩ := hv0
    have hown : c0.owner = some η.tid := hmode
    have hF := pubTyFactsB hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
      (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1) (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
    have hx : ExtB η (shE η ad.label (stOf mem pairs th).vs.vWr) :=
      Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _)
    have hEs : EnvOKB p (shE η ad.label (stOf mem pairs th).vs.vWr) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    have hxb := Ext_bumpRB hEs.2.1
    have hf := bind_FInvB hb2 (bind_FInvB (rt := .ptr (.rgn (.lit 0)) _) hb1
      (push_FInvB rn (ridNext (shE η ad.label (stOf mem pairs th).vs.vWr)) (FInv_extB hE.2.1 hx hi1))
      (region_ptr_VRB_pub (bkG := False) _ (shE_ptr_VRB _ hv hws)) (region_ptr_Lay hl)) region_tok_VRB region_tok_Lay
    refine ⟨by simp only [tstep, hterm, hea]; simp, fun r hr => ?_⟩
    have hs := hfe r hr
    simp only [tstep, hterm, hea, List.mem_singleton] at hr
    subst hr
    refine ⟨CE (shE η ad.label (stOf mem pairs th).vs.vWr),
      ⟨_, bumpRB (shE η ad.label (stOf mem pairs th).vs.vWr), _, CE_bumpRB _,
        ⟨hEs.1, hxb.1, hxb.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, TermA4.CkW_region hCk hu hb1 hb2⟩ (hxb.2.1.trans hx.2.1),
        region_TvOK hu (fun h => by simpa [tb] using h) (fun h => by simpa [mg] using h) hb1 hb2 htv,
        FInv_extB hEs.2.1 hxb (by simpa [withS] using hf),
        retPwN_skel hPS hRP (skel_subst_eq (by rw [bind_ret hb2, bind_ret hb1, push_ret, skel_shiftI, use_ret hu]) th.σs 0 0 0),
        hDy.sameW (fun _ => by rw [hterm]; rfl) (hxb.2.1.trans hx.2.1)⟩,
      ?_, Or.inr ⟨ad.label, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩
    rw [hs]
    exact FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2
  | regionBuf hu hrc hb1 hb2 he =>
    obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
    obtain ⟨μ', u', ψ', rfl⟩ := eskel_eq_refloc (by simpa [close, substTs, skel, rf, etok] using hl.2.1)
    have hv0 := hv
    simp only [VRF, VRb2] at hv0
    obtain ⟨hv1, -⟩ := hv0
    rcases hv1 with ⟨hnull, -, -⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, -⟩
    · -- a null handle (an empty buffer): only the fence, at `CE η`
      obtain ⟨c, hc, hvc, hk, hcase⟩ := region_stepKB hT1 hCk hi htv (ridNext η)
        (fun rt' ws' ad' hea' hws' => by rw [hea] at hea'; cases hea'; rw [hnull] at hws'; simp at hws')
      have hf : FInvB g.lbase g.n g.i (vcons (ridNext η) ρ) η th.σs (ResumeBN g.lbase g.n g.i p th.stack) c
          ((tn, .tok (.lit 0) none, []) :: (pn, .refine (.loc (.rgn (.lit 0)) u') ψ', ws) :: th.env) := by
        rcases hcase with ⟨μ2, u2, ws2, hea2, hf2⟩ | ⟨μ2, u2, ψ2, ws2, hea2, hf2⟩
        · rw [hea] at hea2; cases hea2
        · rw [hea] at hea2; cases hea2; exact hf2
      have hxb := Ext_bumpRB hE.2.1
      refine ⟨by simp only [tstep, hterm, hea]; simp, fun r hr => ?_⟩
      have hs := hfe r hr
      simp only [tstep, hterm, hea, List.mem_singleton] at hr
      subst hr
      refine ⟨CE η, ⟨_, bumpRB η, c, CE_bumpRB η, ⟨hE.1, hxb.1, hxb.2.2.2.2.2.2.2.2.2.2.1⟩, hc.wit hxb.2.1, hvc,
          FInv_extB hE.2.1 hxb (by simpa [withS] using hf), retPwN_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0),
          hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩, ?_, Or.inl rfl⟩
      rw [hs]
      exact MemInv_fenceB hm
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBufB hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat
        (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1 (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      have hx : ExtB η (shE η ad.label (stOf mem pairs th).vs.vWr) :=
        Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _)
      have hEs : EnvOKB p (shE η ad.label (stOf mem pairs th).vs.vWr) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
      have hxb := Ext_bumpRB hEs.2.1
      have hf := bind_FInvB hb2 (bind_FInvB (rt := .refine (.loc (.rgn (.lit 0)) _) _) hb1
        (push_FInvB rn (ridNext (shE η ad.label (stOf mem pairs th).vs.vWr)) (FInv_extB hE.2.1 hx hi1))
        (region_buf_VRB_pub (bkG := False) _ (shE_buf_VRB _ hv hws)) (region_buf_Lay hl)) region_tok_VRB region_tok_Lay
      refine ⟨by simp only [tstep, hterm, hea]; simp, fun r hr => ?_⟩
      have hs := hfe r hr
      simp only [tstep, hterm, hea, List.mem_singleton] at hr
      subst hr
      refine ⟨CE (shE η ad.label (stOf mem pairs th).vs.vWr),
        ⟨_, bumpRB (shE η ad.label (stOf mem pairs th).vs.vWr), _, CE_bumpRB _,
          ⟨hEs.1, hxb.1, hxb.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, TermA4.CkW_regionBuf hCk hu hb1 hb2⟩ (hxb.2.1.trans hx.2.1), regionBuf_TvOK hu hb1 hb2 htv,
          FInv_extB hEs.2.1 hxb (by simpa [withS] using hf),
          retPwN_skel hPS hRP (skel_subst_eq (by rw [bind_ret hb2, bind_ret hb1, push_ret, skel_shiftI, use_ret hu]) th.σs 0 0 0),
          hDy.sameW (fun _ => by rw [hterm]; rfl) (hxb.2.1.trans hx.2.1)⟩,
        ?_, Or.inr ⟨ad.label, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩
      rw [hs]
      exact FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2

/-- **Shadow `intoRgn`** (the `pub_stepD` shape, region-moded result). -/
theorem into_stepN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.intoRgn rn a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hcpl : RgnCpl cx a) (hsc : PubScope cx a)
    (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel)
    (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ E1, ThInvEBN g.lbase g.n g.i p E1 r.2.2 ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧
      (E1 = CE η ∨ ∃ lab V, η.sto lab ≠ none ∧ E1 = CE (shE η lab V)) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | intoRgnBuf hr hu hrc hb =>
    rename_i c₁ r n k u
    obtain ⟨hi1, μr, nr, ur, ψ, wsb, hea, hvb, hlay⟩ := ownBuf_invB (bkG := False) hu hi
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    have hl := hlay (.rgn r) (.rgn (.lit 0)) (by simp [skelM]) (by simp [modeC, idxC, ofMs])
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, hir⟩ := hvb
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, hini⟩
    · have hvr : (VRF False) ρ η (.refine (.loc (.rgn r) (.array n u)) (.ini k))
          (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ)) wsb := by
        simp only [VRF, VRb2]; exact ⟨Or.inl ⟨hnull, e0, he0⟩, IniR_mono (TEnv.selIni_le_ini η _) hir.1,
          fun _ => Or.inl (fun a h => by rw [hnull] at h; simp at h)⟩
      exact ⟨CE η, ⟨ρ, η, c', rfl, hE, ⟨he, hck⟩, htv', bind_FInvB hb hi1 hvr hl,
          retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_fenceB hm, Or.inl rfl⟩
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBufB hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat
        (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1 (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      have hx : ExtB η (shE η ad.label (stOf mem pairs th).vs.vWr) :=
        Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _)
      have hvr : (VRF False) ρ (shE η ad.label (stOf mem pairs th).vs.vWr)
          (.refine (.loc (.rgn r) (.array n u)) (.ini k)) (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ)) wsb := by
        simp only [VRF, VRb2]
        exact ⟨Or.inr ⟨ad, c0, _, hws, hsto, hat, .refl,
          ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP],
            Or.inr (Or.inr ⟨hown, Or.inr hini⟩)⟩, IniAt_mono (modeIni_le_ini _ _ _) hini⟩,
          IniR_mono (TEnv.selIni_le_ini η _) hir.1, fun _ => Or.inr hir.1⟩
      exact ⟨CE (shE η ad.label (stOf mem pairs th).vs.vWr),
        ⟨ρ, shE η ad.label (stOf mem pairs th).vs.vWr, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, hck⟩ hx.2.1, htv',
          bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr hl, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0),
          hDy.letW hterm rfl⟩,
        FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2,
        Or.inr ⟨ad.label, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩
  | intoRgn hr hu hrc hb =>
  rename_i c₁ r u
  obtain ⟨hi1, lab, c0, pw, μr, ru, hea, hpw, hsto, hcty, hown, hacc, hl⟩ := ownPtr_invB hu hi
  have hwsv : [pw].map (·.val) = [.loc ⟨lab, 0⟩ 0] := by simp [hpw]
  have hF := pubTyFactsB hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
    (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1)
    (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
  have hx : ExtB η (shE η lab (stOf mem pairs th).vs.vWr) :=
    Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _)
  have key : tstep g mem pairs th =
      [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
        withS { th with term := e, env := (x, .ptr (.rgn (.lit 0)) ru, [pw]) :: th.env }
          (fenceS (stOf mem pairs th) .st))] := by
    simp only [tstep, hterm, evalOp, hea]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : (VRF False) ρ (shE η lab (stOf mem pairs th).vs.vWr) (.ptr (.rgn r) u)
      (shp (.ptr (.rgn (.lit 0)) ru)) [pw] := by
    simp only [VRF, VRb2]
    exact ⟨⟨lab, 0⟩, c0, hwsv, rfl, hsto, hcty,
      ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP],
        Or.inr (Or.inr ⟨hown, Or.inr (fun N e h => hacc (by rw [h]; rfl))⟩)⟩, hacc⟩
  have hlay : Lay th.σs (.ptr (.rgn r) u) (.ptr (.rgn (.lit 0)) ru) [pw] :=
    Lay_ptr_remode hl (by simp [skelM]) (by simp [modeC, idxC, ofMs])
  exact ⟨CE (shE η lab (stOf mem pairs th).vs.vWr),
    ⟨ρ, shE η lab (stOf mem pairs th).vs.vWr, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, TypedK.wit ⟨he, hck⟩ hx.2.1, htv',
      bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr hlay, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0),
      hDy.letW hterm rfl⟩,
    FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2,
    Or.inr ⟨lab, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩

end CertWinProof
