import WeakCore.ShadowPub
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
-- PORTB TermOwnK4.lean:213 pubBuf_step
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem pubBuf_stepS {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {a : At} {e : Expr} {Rf Rs : Res} {n k : Idx} {u : Ty}
    (hterm : th.term = .let_ y (.publish a) e) (hP : ProgT p)
    (hu : cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁))
    (hsh : Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true)
    (hb : c₁.bind y (.refine (.loc .pub (.array n u)) (.ini k)) = .ok c') (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hsc : PubScope cx a)
    (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, ∃ rt ws E1 Tot', evalAt th.env a = some (rt, ws) ∧ ThInvREB g.lbase g.n g.i p E1 r.2.2 Tot' ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧ (stOf r.1 r.2.1 r.2.2).mem = mem ∧
      (stOf r.1 r.2.1 r.2.2).promises = th.promises ∧ Tot' + ownW .own ws ≤ Rf + Rs ∧ EnvShrink (CE η) E1 ∧ ∀ l, (CE η).seen l → E1.seen l := by
  obtain ⟨rb, wsb, R0, Rr, hea, hvb, hlb, hvR, hi1R, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hR0 := VRR_buf_RB rfl hvR
  have hi1 := hi1R.1
  simp only [VRF, VRb2] at hvb
  obtain ⟨hv, hir, -⟩ := hvb
  have hirc : IniR ρ η.rc (.ini k) wsb := by have h := hir; rw [FlatShadowPub.selIni_ownB] at h; exact h
  have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
    rw [hlb.2.1]; rfl
  obtain ⟨μr, nr, ur, ψ, rfl, hμ, hsu⟩ := buf_runtime' hs'
  have hlay : Lay th.σs (.refine (.loc .pub (.array n u)) (.ini k)) (.refine (.loc .pub (.array nr ur)) ψ) wsb := by
    obtain ⟨h1, -, h3, h4⟩ := hlb
    refine ⟨h1, ?_, h3, h4.1, ?_⟩
    · rw [close_refine]
      show etok (rf (skel (.loc .pub (.array nr ur)))) = etok (rf (skel (close th.σs (.loc .pub (.array n u)))))
      rw [skel_close_locArr]
      show rf (.loc (skelM .pub) (.array (.lit 0) (etok (skel ur)))) = _
      rw [hsu]; rfl
    · simp only [close, substTs, lyt, etok, anyB_zero, Bool.false_eq_true, ite_false, idxC, ofMs, modeC]
      rw [(buf_lyt h4.2 rfl).2]; rfl
  have key : tstep g mem pairs th =
      [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
        withS { th with term := e, env := (y, .refine (.loc .pub (.array nr ur)) ψ, wsb) :: th.env }
          (fenceS (stOf mem pairs th) .st))] := by
    simp only [tstep, hterm, evalOp, hea]; rfl
  intro r hr
  rw [key, List.mem_singleton] at hr
  subst hr
  have hleT : Rr + Rs + ownW .own wsb ≤ Rf + Rs := Res.le_def.2 fun k => by
    have h1 := Res.le_def.1 hle k
    have h3 := congrArg (fun R : Res => R k) hR0
    simp only [Res.add_apply] at h1 h3 ⊢; omega
  rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat, hFU, hmode, hini⟩
  · 
    have hvz : VRRB ρ η (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb .zero := by
      simp only [VRRB]; exact ⟨⟨Or.inl ⟨hnull, e0, he0⟩, rfl⟩, IniR_mono (TEnv.selIni_le_ini η _) hir, fun _ => Or.inr hirc⟩
    have hfr := bindRB hb hi1R (RLink_ofB hE.2.1 hE.2.2) hvz hlay
    rw [Res.add_zero] at hfr
    exact ⟨_, wsb, CE η, Rr + Rs, hea, ⟨ρ, η, c', Rr, Rs, rfl, hE, he, htv', hfr, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.letW hterm rfl⟩, MemInv_fenceB hm, rfl, rfl,
      hleT, envShrink_refl _, fun _ h => h⟩
  · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
    have hown : c.owner = some η.tid := hmode
    have hx : ExtB η (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr)) :=
      Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _)
    have hvr : (VRF False) ρ (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr))
        (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
      simp only [VRF, VRb2]
      exact ⟨Or.inr ⟨ad, c, _, hws, hsto, hat, .refl,
        ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP], Or.inr (Or.inr ⟨hown, Or.inr hini⟩)⟩,
        (IniAt_mono (modeIni_le_ini _ _ _) hini)⟩, IniR_mono (TEnv.selIni_le_ini η _) hir, fun _ => Or.inr hirc⟩
    have hE' : EnvOKB p (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr)) :=
      ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    have hvz : VRRB ρ (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr))
        (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb .zero := by
      simp only [VRF, VRb2] at hvr; simp only [VRRB]; exact ⟨⟨hvr.1, rfl⟩, hvr.2.1, hvr.2.2⟩
    have hfr := bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi1R) (RLink_ofB hE'.2.1 hE'.2.2) hvz hlay
    rw [Res.add_zero] at hfr
    have hcu : Ty.coupledOKIn c₁.ke (.array n u) = true := by
      simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
    have htbu : tb c₁.ke.length (.array n u) = true := by
      have h := (use_TvOK hu htv).2.1
      rw [← (use_TvOK hu htv).2.2] at h
      simpa [tb] using h
    have hcp := coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu
    obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
    exact ⟨_, wsb, _, Rr + Rs, hea,
      ⟨ρ, η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr), c', Rr, Rs, rfl, hE',
        he, htv', hfr, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.letW hterm rfl⟩,
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
      rfl, rfl, hleT, FlatShadowPub.envShrink_pubS η ad.label _, fun _ h => h⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:325 pub_step
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem pub_stepS {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {a : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ y (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hsc : PubScope cx a)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, ∃ rt ws E1 Tot', evalAt th.env a = some (rt, ws) ∧ ThInvREB g.lbase g.n g.i p E1 r.2.2 Tot' ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧ (stOf r.1 r.2.1 r.2.2).mem = mem ∧
      (stOf r.1 r.2.1 r.2.2).promises = th.promises ∧ Tot' + ownW .own ws ≤ Rf + Rs ∧ EnvShrink (CE η) E1 ∧ ∀ l, (CE η).seen l → E1.seen l := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu, hsh, hb⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) ∧
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind y (.ptr .pub u) = .ok c' := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨rt, ws, R0, Rr, hea, hv, hl, hvR, hi1R, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    have hR0 := VRR_cell_RB rfl hvR
    have hi1 := hi1R.1
    simp only [VRF, VRb2] at hv
    obtain ⟨⟨lab, off⟩, c, hws, hoff, hsto, hcty, hmode, hacc⟩ := hv
    simp only at hoff; subst hoff
    obtain ⟨pw, rfl, hpw⟩ : ∃ pw, ws = [pw] ∧ pw.val = .loc ⟨lab, 0⟩ 0 := by
      match ws, hws with
      | [pw], h => exact ⟨pw, rfl, by simpa using h⟩
      | [], h => simp at h
      | _ :: _ :: _, h => simp at h
    have hsk := hl.2.1
    rw [close_ptr] at hsk
    obtain ⟨ru, rfl, hsku⟩ : ∃ ru, rt = .ptr .own ru ∧ etok (skel ru) = etok (skel (close th.σs u)) := by
      cases rt <;> simp [skel, etok] at hsk
      case ptr μ ru =>
        cases μ <;> simp [skelM, etok] at hsk
        exact ⟨ru, rfl, hsk⟩
      case refine t ψ => unfold rf at hsk; split at hsk <;> simp [etok] at hsk
    have hown : c.owner = some η.tid := hmode
    have hx : ExtB η (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr)) :=
      Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _)
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (y, .ptr .pub ru, [pw]) :: th.env } (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    intro r hr
    rw [key, List.mem_singleton] at hr
    subst hr
    have hvr : (VRF False) ρ (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr))
        (.ptr .pub u) (shp (.ptr .pub ru)) [pw] := by
      simp only [VRF, VRb2]
      exact ⟨⟨lab, 0⟩, c, hws, rfl, hsto, hcty,
        ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP], Or.inr (Or.inr ⟨hown, Or.inr (fun N e h => hacc (by rw [h]; rfl))⟩)⟩, hacc⟩
    have hlay : Lay th.σs (.ptr .pub u) (.ptr .pub ru) [pw] :=
      ⟨fun us h => by simp [accs] at h; subst h; rfl, by rw [close_ptr]; simp only [skel, etok, hsku],
        by simp [wc, accs], ⟨⟨lab, 0⟩, hws⟩, by
          simp only [close, substTs, lyt, etok]; rw [(cell_lyt hl.2.2.2.2 rfl rfl).2]; rfl⟩
    have hE' : EnvOKB p (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr)) :=
      ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    have hvz : VRRB ρ (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr))
        (.ptr .pub u) (shp (.ptr .pub ru)) [pw] .zero := by
      simp only [VRF, VRb2] at hvr; simp only [VRRB]; exact ⟨hvr, rfl⟩
    have hfr := bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi1R) (RLink_ofB hE'.2.1 hE'.2.2) hvz hlay
    rw [Res.add_zero] at hfr
    have hleT : Rr + Rs + ownW .own [pw] ≤ Rf + Rs := Res.le_def.2 fun k => by
      have h1 := Res.le_def.1 hle k
      have h3 := congrArg (fun R : Res => R k) hR0
      simp only [Res.add_apply] at h1 h3 ⊢; omega
    obtain ⟨s1, s2, s3, s4⟩ := pubCell_sideB hE htv hi1 hu hsh hsc hcty hacc
    exact ⟨_, [pw], _, Rr + Rs, hea,
      ⟨ρ, η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr), c', Rr, Rs, rfl, hE', ⟨he, hck⟩,
        htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      FlatShadowPub.MemInv_publishSB hm hsto hown s1 s2 s3 s4, rfl, rfl, hleT, FlatShadowPub.envShrink_pubS η lab _, fun _ h => h⟩
  | publishBuf hu hsh hb => exact pubBuf_stepS (hDy := hDy) hterm hP hu hsh hb ⟨he, hck⟩ htv' hi hE htv hm hsc hRP
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:411 tgt_publish
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_publishS {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {a : At} {e : Expr} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (hterm : th.term = .let_ y (.publish a) e) (hPS : PwSkel) : TgtB p g x n (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨rt, ws, E1, Tot', -, hT', hm', e1, e2, hle, hx, hsn⟩ := pub_stepS (hDy := hS.dy) hterm hP hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm
    (pubScope_of (by rw [← hterm]; exact hS.sc)) hS.rp hPS r hr
  obtain ⟨HP', hH', hle'⟩ := memHeldP_shrinkB hx e1 e2 hS.hH
  refine ⟨E1, Tot', HP', hT', hm', hH', fun l cl h => hS.nie l cl (by rw [← hx.2.2.2.1]; exact h),
    by rw [hx.2.2.2.1]; exact hS.sto, ?_,
    TermOwnX2.Flat.anchStep_shrinkB (ext_shrinkB hT' hx hsn) hx.2.2.2.1 hx.2.2.2.2.1 e1 e2 hx.2.2.2.2.2.1, hS.tyk hr (fun l c h => by rw [← hx.2.2.2.1]; exact h)⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h2 := hle' (.own x)
  have h3 := hS.le
  simp only [Res.add_apply] at h1 h3
  omega
end
end TermOwnK4.Flat


namespace TermOwnK4.Flat
open TermSound.Flat TermStep.Flat TermOwnX2.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-- The package-4 easy-step target with the publish case discharged by the shadow publish. -/
theorem tgt_easyS {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat}
    {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP) (h : EasyK4 th.term) (hRP : RetPw th.σs th.stack cx.ret)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TgtB p g x n (CE η) mem pairs th :=
  tgt_easyB hP hS h hRP hPS hSub hSig (fun _ _ _ ht => tgt_publishS hP hS ht hPS)
end TermOwnK4.Flat

namespace TermOwnK4.Flat
open TermSound.Flat TermStep.Flat TermOwnX2.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnHeldQ.Flat TermTyped.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-- B6: package 4 (word/pub/cas/ldp/stp/sum ops) with the shadow publish; no window premise. -/
theorem ownXStep_k4S [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {i : Nat} {x : AllocLabel} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ n, TermOwnX2.Flat.OwnXStepPkgB p k arch i x n 4 := by
  intro n E0 c0 c0' th hth hq hsc hvI hI hs hc
  exact ownXLe_of_srcB hth hsc hvI hI hs hc id fun ρ η cx Rf Rs HP hS => tgt_easyS hP hS (easyK4_of_pkg hq) hS.rp hPS hSub hSig

/-- B6: `OwnXLeB` along a certified solo run, with no publish-window premise (W's `run_ind_win`, generic). -/
theorem ownXLe_runS {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n : Nat}
    {c c2 : Cfg} (hT : OwnXStepTB p k arch i x n) (hPr : OwnXStepPB p k arch i x n)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0)
    (hvI : TermViewInv.ViewInv c) (h0 : OwnXLeB p k arch E0 i x n c) (hTA : TermTyped.TidAt i c E0)
    (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) : OwnXLeB p k arch E0 i x n c2 :=
  (TermOwnX2.run_ind_win (Q := fun c0 => ScopeAtB p i c0 ∧ TermViewInv.ViewInv c0)
    (fun c0 h1 h2 _ => ⟨hQ c0 h1 h2, TermViewInv.viewInv_solo hvI h1⟩)
    (fun c0 c0' _ hI hq hs hc => hT E0 c0 c0' hq.1 hq.2 hI hs hc)
    (fun c0 a v w _ hI hw hc => hPr E0 c0 a v w hI hw hc)
    (fun _ _ h1 hI hs => ownXLe_extB hI hs (TermTyped.tidAt_solo h1 hTA)) h0 h hc2).1
end TermOwnK4.Flat

namespace TermOwnK4.Flat
open TermSound.Flat TermStep.Flat TermOwnX2.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnHeldQ.Flat TermTyped.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-- B6: the ♭ resource clause along a certified solo run, all packages (packages 1–3 ported, package 4 with the shadow
publish), no publish-window premise. -/
theorem ownXLe_runAllS [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n : Nat} {c c2 : Cfg} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0)
    (hvI : TermViewInv.ViewInv c) (h0 : OwnXLeB p k arch E0 i x n c) (hTA : TermTyped.TidAt i c E0)
    (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) : OwnXLeB p k arch E0 i x n c2 :=
  ownXLe_runS (ownXStepT_of_pkgsB (ownXStep_k1B hP hPS hSub hSig n) (ownXStep_k2B hP hPS n) (ownXStep_k3B hP hPS n)
    (ownXStep_k4S hP hPS hSub hSig n)) (ownXStepP_allB n) hQ hvI h0 hTA h hc2
end TermOwnK4.Flat
