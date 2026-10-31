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
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hsc : PubScope cx a)
    (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ E1, ThInvEBN g.lbase g.n g.i p E1 r.2.2 ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧
      (E1 = CE η ∨ ∃ lab V, η.sto lab ≠ none ∧ E1 = CE (shE η lab V)) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
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
      ⟨ρ, shE η lab (stOf mem pairs th).vs.vWr, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv',
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
      exact ⟨CE η, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hl,
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
        ⟨ρ, shE η ad.label (stOf mem pairs th).vs.vWr, c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv',
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
              exact rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk) hcu
                (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))),
        Or.inr ⟨ad.label, _, by rw [hsto]; exact Option.some_ne_none _, rfl⟩⟩

end CertWinProof
