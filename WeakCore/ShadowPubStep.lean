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
            exact TermC1.drf1_cl_frameR ρ hi1.2.2.2.2.2.2.2.2.2.2 htbu
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

-- g1m7 shadow region / intoRgn (R level)
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-! (route (a), ♭ shadow twins at R level): `region` / `intoRgn` on an own cell at the shadow env
(pfr set at `vWr`, `seen` untouched), consuming the own key as `pub_stepS`; the `.rgn` mode is the `pub` clause, met
by its owner disjunct.  No `NoHold`, no window premise. -/

/-- An own pointer is a `pub` pointer once its cell has a frontier (owner disjunct). -/
theorem own_pub_ptrVRB {ρ : Nat → Nat} {η : TEnv} {u : Ty} {rt : Shp} {ws : List Word}
    (hv : (VRF False) ρ η (.ptr .own u) rt ws) (hpf : ∀ ad, ws.map (·.val) = [.loc ad 0] → η.pfr ad.label ≠ none) :
    (VRF False) ρ η (.ptr .pub u) rt ws := by
  simp only [VRF, VRb2] at hv ⊢
  obtain ⟨a, c, h1, h2, h3, h4, hm, h6⟩ := hv
  obtain ⟨f, hf⟩ := pfrSomeB (hpf a h1)
  exact ⟨a, c, h1, h2, h3, h4, ⟨f, hf, Or.inr (Or.inr ⟨hm, Or.inr (fun N e h => h6 (by rw [h]; rfl))⟩)⟩, h6⟩

/-- An own buffer locative is a `pub` locative once its cell has a frontier (owner disjunct). -/
theorem own_pub_bufVRB {ρ : Nat → Nat} {η : TEnv} {t : Ty} {ψ : Pred} {rt : Shp} {ws : List Word}
    (hv : (VRF False) ρ η (.refine (.loc .own t) ψ) rt ws)
    (hpf : ∀ ad, ws.map (·.val) = [.loc ad 0] → η.pfr ad.label ≠ none) :
    (VRF False) ρ η (.refine (.loc .pub t) ψ) rt ws := by
  simp only [VRF, VRb2] at hv ⊢
  obtain ⟨hv, hir⟩ := hv
  refine ⟨?_, IniR_mono (TEnv.selIni_le_ini η _) hir.1, fun _ => Or.inr hir.1⟩
  rcases hv with h | ⟨a, c, U, hws, hsto, hat, hFU, hmode, hini⟩
  · exact .inl h
  · obtain ⟨f, hf⟩ := pfrSomeB (hpf a hws)
    exact .inr ⟨a, c, U, hws, hsto, hat, hFU, ⟨f, hf, Or.inr (Or.inr ⟨hmode, Or.inr hini⟩)⟩,
      IniAt_mono (modeIni_le_ini _ _ _) hini⟩

/-- `region_stepRTB` with the shadow side condition (frontier set, no `seen`). -/
theorem region_stepRTB_sh {p : Prog} {cx : Cx} {a : At} {rn pn tn : String} {e : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop} {env : Env} {Rf : Res}
    (hT : Typed p cx (.region a rn pn tn e)) (hCk : TermA4.CkW p η.wit cx (.region a rn pn tn e)) (hi : FInvRB glb gnum gi ρ η σs K cx env Rf) (htv : TvOK cx)
    (hL : RLink η) (hcr : CohRB η) (w : Nat)
    (hpf : ∀ rt ws ad, evalAt env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] → η.pfr ad.label ≠ none) :
    ∃ c, TypedK p η c e ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ ∃ Rr ws, ownW .own ws + Rr ≤ Rf ∧
      ((∃ μ u, evalAt env a = some (.ptr μ u, ws) ∧
        FInvRB glb gnum gi (vcons w ρ) η σs K c ((tn, .tok (.lit 0) none, []) :: (pn, .ptr (.rgn (.lit 0)) u, ws) :: env)
          (Rr + (Res.one (.rg w) + Res.one (.wd w)))) ∨
       (∃ μ u ψ, evalAt env a = some (.refine (.loc μ u) ψ, ws) ∧
        FInvRB glb gnum gi (vcons w ρ) η σs K c
          ((tn, .tok (.lit 0) none, []) :: (pn, .refine (.loc (.rgn (.lit 0)) u) ψ, ws) :: env)
          (Rr + (Res.one (.rg w) + Res.one (.wd w))))) := by
  cases hT with
  | region hu _ hb1 hb2 he =>
      obtain ⟨rt, ws, R, Rr, hea, hv, hl, hvR, hi1, hle⟩ := useRB (bkG := False) hu hi hcr
      obtain ⟨μ', u', rfl, -, -⟩ := eskel_eq_ptr (by simpa [close, substTs, skel, etok] using hl.2.1)
      refine ⟨_, ⟨he, TermA4.CkW_region hCk hu hb1 hb2⟩, region_TvOK hu (fun h => by simpa [tb] using h) (fun h => by simpa [mg] using h) hb1 hb2 htv,
        by rw [bind_ret hb2, bind_ret hb1, push_ret, skel_shiftI, use_ret hu], Rr, ws,
        by rw [← VRR_cell_RB rfl hvR]; exact hle, .inl ⟨μ', u', hea, ?_⟩⟩
      rw [show Rr + (Res.one (.rg w) + Res.one (.wd w)) = Rr + Res.zero + (Res.one (.rg w) + Res.one (.wd w)) by
        rw [Res.add_zero]]
      exact bindRB hb2 (bindRB hb1 (pushRB rn w hi1) hL
        (VRR_ofVR_ptrB (region_ptr_VRB_pub (bkG := False) w (own_pub_ptrVRB hv (fun ad h => hpf _ _ ad hea h))))
        (region_ptr_Lay hl)) hL (region_tok_VRRB w) region_tok_Lay
  | regionBuf hu _ hb1 hb2 he =>
      obtain ⟨rt, ws, R, Rr, hea, hv, hl, hvR, hi1, hle⟩ := useRB (bkG := False) hu hi hcr
      obtain ⟨μ', u', ψ', rfl⟩ := eskel_eq_refloc (by simpa [close, substTs, skel, rf, etok] using hl.2.1)
      refine ⟨_, ⟨he, TermA4.CkW_regionBuf hCk hu hb1 hb2⟩, regionBuf_TvOK hu hb1 hb2 htv, by rw [bind_ret hb2, bind_ret hb1, push_ret, skel_shiftI, use_ret hu],
        Rr, ws, by rw [← VRR_buf_RB rfl hvR]; exact hle, .inr ⟨μ', u', ψ', hea, ?_⟩⟩
      rw [show Rr + (Res.one (.rg w) + Res.one (.wd w)) = Rr + Res.zero + (Res.one (.rg w) + Res.one (.wd w)) by
        rw [Res.add_zero]]
      exact bindRB hb2 (bindRB hb1 (pushRB rn w hi1) hL
        (VRR_ofVR_reflocB (region_buf_VRB_pub (bkG := False) w (own_pub_bufVRB hv (fun ad h => hpf _ _ ad hea h))))
        (region_buf_Lay hl)) hL (region_tok_VRRB w) region_tok_Lay

/-- **Shadow `region`** at R level (the `pub_stepS` shape; the fresh region's `rg + wd` minted). -/
theorem rgn_stepS {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {rn pn tn : String} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .region a rn pn tn e)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hcpl : RgnCpl cx a)
    (hsc : PubScope cx a) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, ∃ rt ws E1 Tot', evalAt th.env a = some (rt, ws) ∧ ThInvREB g.lbase g.n g.i p E1 r.2.2 Tot' ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧ (stOf r.1 r.2.1 r.2.2).mem = mem ∧
      (stOf r.1 r.2.1 r.2.2).promises = th.promises ∧
      Tot' + ownW .own ws ≤ Rf + Rs + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) ∧
      EnvShrink (CE η) E1 ∧ ∀ l, (CE η).seen l → E1.seen l := by
  have hT0 := hT
  rw [hterm] at hT0 hCk
  have hT1 := hT0
  have hfe := fence_region (g := g) (mem := mem) (pairs := pairs) hterm
  have hbd : ∀ {Rr : Res} {ws : List Word}, ownW .own ws + Rr ≤ Rf →
      Rr + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) + Rs + ownW .own ws ≤
        Rf + Rs + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) := fun hle =>
    Res.le_def.2 fun k => by
      have h1 := Res.le_def.1 hle k
      simp only [Res.add_apply] at h1 ⊢; omega
  cases hT0 with
  | regionBuf hu hrc _ _ _ =>
    obtain ⟨hi1, μr, nr, ur, ψ, wsb, hea, hvb, -⟩ := ownBuf_invB (bkG := False) hu hi.1
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, -⟩ := hvb
    rcases hv with ⟨hnull, -, -⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, -⟩
    · -- a null handle (an empty buffer): only the fence, at `CE η`
      have hxb := Ext_bumpRB hE.2.1
      have hE1 : EnvOKB p (bumpRB η) := ⟨hE.1, hxb.1, hxb.2.2.2.2.2.2.2.2.2.2.1⟩
      obtain ⟨c, hc, hvc, hk, Rr, ws, hle, hcase⟩ :=
        region_stepRTB_sh hT1 (by rw [hxb.2.1]; exact hCk) (FInvR_extB hE.2.1 hE.2.2 hxb hi) htv
          (RLink_ofB hE1.2.1 hE1.2.2) hE1.2.2 (ridNext η)
          (fun rt' ws' ad' hea' hws' => by rw [hea] at hea'; cases hea'; rw [hnull] at hws'; simp at hws')
      obtain ⟨μ2, u2, ψ2, hea2, hf⟩ : ∃ μ u ψ, evalAt th.env a = some (.refine (.loc μ u) ψ, ws) ∧
          FInvRB g.lbase g.n g.i (vcons (ridNext η) ρ) (bumpRB η) th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c
            ((tn, .tok (.lit 0) none, []) :: (pn, .refine (.loc (.rgn (.lit 0)) u) ψ, ws) :: th.env)
            (Rr + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η)))) := by
        rcases hcase with ⟨μ2, u2, hea2, -⟩ | h
        · rw [hea] at hea2; cases hea2
        · exact h
      rw [hea] at hea2
      cases hea2
      intro r hr
      have hs := hfe r hr
      simp only [tstep, hterm, hea, List.mem_singleton] at hr
      subst hr
      refine ⟨_, wsb, CE (bumpRB η), _, hea, ⟨_, bumpRB η, c, _, Rs, rfl, hE1, hc, hvc,
          by simpa [withS] using hf, rfl, retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0),
          hDy.sameW (fun _ => by rw [hterm]; rfl) hxb.2.1⟩, ?_, by rw [hs]; rfl, by rw [hs]; rfl, hbd hle,
        envShrink_refl _, fun _ h => h⟩
      rw [hs]
      exact MemInv_fenceB hm
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBufB hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat
        (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1 (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      have hx : ExtB η (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (Rd := η.rid + 1)) :=
        Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _) (hR := Nat.le_succ _)
      have hE1 : EnvOKB p (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (Rd := η.rid + 1)) :=
        ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
      obtain ⟨c, hc, hvc, hk, Rr, ws, hle, hcase⟩ :=
        region_stepRTB_sh hT1 (by rw [hx.2.1]; exact hCk) (FInvR_extB hE.2.1 hE.2.2 hx hi) htv
          (RLink_ofB hE1.2.1 hE1.2.2) hE1.2.2 (ridNext η)
          (fun rt' ws' ad' hea' hws' => by
            rw [hea] at hea'; cases hea'; rw [hws] at hws'; cases hws'; simp [TEnv.withStoB, pubP])
      obtain ⟨μ2, u2, ψ2, hea2, hf⟩ : ∃ μ u ψ, evalAt th.env a = some (.refine (.loc μ u) ψ, ws) ∧
          FInvRB g.lbase g.n g.i (vcons (ridNext η) ρ)
            (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (Rd := η.rid + 1)) th.σs
            (ResumeRB g.lbase g.n g.i p th.stack Rs) c
            ((tn, .tok (.lit 0) none, []) :: (pn, .refine (.loc (.rgn (.lit 0)) u) ψ, ws) :: th.env)
            (Rr + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η)))) := by
        rcases hcase with ⟨μ2, u2, hea2, -⟩ | h
        · rw [hea] at hea2; cases hea2
        · exact h
      rw [hea] at hea2
      cases hea2
      intro r hr
      have hs := hfe r hr
      simp only [tstep, hterm, hea, List.mem_singleton] at hr
      subst hr
      refine ⟨_, wsb, _, _, hea, ⟨_, _, c, _, Rs, rfl, hE1, hc, hvc,
          by simpa [withS] using hf, rfl, retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0),
          hDy.sameW (fun _ => by rw [hterm]; rfl) hx.2.1⟩, ?_, by rw [hs]; rfl, by rw [hs]; rfl, hbd hle,
        FlatShadowPub.envShrink_pubS η ad.label _, fun _ h => h⟩
      rw [hs]
      exact FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2
  | region hu hrc _ _ _ =>
    obtain ⟨hi1, lab, c0, pw, μr, ru, hea, hpw, hsto, hcty, hown, hacc, -⟩ := ownPtr_invB hu hi.1
    have hF := pubTyFactsB hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
      (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1)
      (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
    have hx : ExtB η (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (Rd := η.rid + 1)) :=
      Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _) (hR := Nat.le_succ _)
    have hE1 : EnvOKB p (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (Rd := η.rid + 1)) :=
      ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    obtain ⟨c, hc, hvc, hk, Rr, ws, hle, hcase⟩ :=
      region_stepRTB_sh hT1 (by rw [hx.2.1]; exact hCk) (FInvR_extB hE.2.1 hE.2.2 hx hi) htv
        (RLink_ofB hE1.2.1 hE1.2.2) hE1.2.2 (ridNext η)
        (fun rt' ws' ad' hea' hws' => by
          rw [hea] at hea'; cases hea'; rw [TermC1.pwLab hpw hws']; simp [TEnv.withStoB, pubP])
    obtain ⟨μ2, u2, hea2, hf⟩ : ∃ μ u, evalAt th.env a = some (.ptr μ u, ws) ∧
        FInvRB g.lbase g.n g.i (vcons (ridNext η) ρ)
          (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (Rd := η.rid + 1)) th.σs
          (ResumeRB g.lbase g.n g.i p th.stack Rs) c
          ((tn, .tok (.lit 0) none, []) :: (pn, .ptr (.rgn (.lit 0)) u, ws) :: th.env)
          (Rr + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η)))) := by
      rcases hcase with h | ⟨μ2, u2, ψ2, hea2, -⟩
      · exact h
      · rw [hea] at hea2; cases hea2
    rw [hea] at hea2
    cases hea2
    intro r hr
    have hs := hfe r hr
    simp only [tstep, hterm, hea, List.mem_singleton] at hr
    subst hr
    refine ⟨_, [pw], _, _, hea, ⟨_, _, c, _, Rs, rfl, hE1, hc, hvc,
        by simpa [withS] using hf, rfl, retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0),
        hDy.sameW (fun _ => by rw [hterm]; rfl) hx.2.1⟩, ?_, by rw [hs]; rfl, by rw [hs]; rfl, hbd hle,
      FlatShadowPub.envShrink_pubS η lab _, fun _ h => h⟩
    rw [hs]
    exact FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2

/-- **Shadow `intoRgn`** at R level (the `pub_stepS` shape, region-moded result). -/
theorem into_stepS {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {a : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.intoRgn rn a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hcpl : RgnCpl cx a)
    (hsc : PubScope cx a) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, ∃ rt ws E1 Tot', evalAt th.env a = some (rt, ws) ∧ ThInvREB g.lbase g.n g.i p E1 r.2.2 Tot' ∧
      MemInvB g E1 (stOf r.1 r.2.1 r.2.2) ∧ (stOf r.1 r.2.1 r.2.2).mem = mem ∧
      (stOf r.1 r.2.1 r.2.2).promises = th.promises ∧ Tot' + ownW .own ws ≤ Rf + Rs ∧
      EnvShrink (CE η) E1 ∧ ∀ l, (CE η).seen l → E1.seen l := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | intoRgnBuf hr hu hrc hb =>
    rename_i c₁ r n k u
    obtain ⟨rb, wsb, R0, Rr, hea, -, -, hvR, hi1R, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    have hR0 := VRR_buf_RB rfl hvR
    obtain ⟨hi1, μr, nr, ur, ψ, wsb', hea', hvb, hlay⟩ := ownBuf_invB (bkG := False) hu hi.1
    rw [hea] at hea'
    cases hea'
    have hl := hlay (.rgn r) (.rgn (.lit 0)) (by simp [skelM]) (by simp [modeC, idxC, ofMs])
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    have hleT : Rr + Rs + ownW .own wsb ≤ Rf + Rs := Res.le_def.2 fun k => by
      have h1 := Res.le_def.1 hle k
      have h3 := congrArg (fun R : Res => R k) hR0
      simp only [Res.add_apply] at h1 h3 ⊢; omega
    intro r' hr'
    rw [key, List.mem_singleton] at hr'
    subst hr'
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, hir⟩ := hvb
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, hini⟩
    · have hvz : VRRB ρ η (.refine (.loc (.rgn r) (.array n u)) (.ini k))
          (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ)) wsb .zero := by
        simp only [VRRB]; exact ⟨⟨Or.inl ⟨hnull, e0, he0⟩, rfl⟩, IniR_mono (TEnv.selIni_le_ini η _) hir.1,
          fun _ => Or.inl (fun a h => by rw [hnull] at h; simp at h)⟩
      have hfr := bindRB hb hi1R (RLink_ofB hE.2.1 hE.2.2) hvz hl
      rw [Res.add_zero] at hfr
      exact ⟨_, wsb, CE η, Rr + Rs, hea, ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl,
          retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_fenceB hm, rfl, rfl, hleT,
        envShrink_refl _, fun _ h => h⟩
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBufB hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat
        (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1 (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      have hx : ExtB η (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr)) :=
        Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _)
      have hE' : EnvOKB p (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr)) :=
        ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
      have hvz : VRRB ρ (η.withStoB η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr))
          (.refine (.loc (.rgn r) (.array n u)) (.ini k)) (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ))
          wsb .zero := by
        simp only [VRRB]
        exact ⟨⟨Or.inr ⟨ad, c0, _, hws, hsto, hat, .refl,
          ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP],
            Or.inr (Or.inr ⟨hown, Or.inr hini⟩)⟩, IniAt_mono (modeIni_le_ini _ _ _) hini⟩,
          by simp [ownW]⟩, IniR_mono (TEnv.selIni_le_ini η _) hir.1, fun _ => Or.inr hir.1⟩
      have hfr := bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi1R) (RLink_ofB hE'.2.1 hE'.2.2) hvz hl
      rw [Res.add_zero] at hfr
      exact ⟨_, wsb, _, Rr + Rs, hea, ⟨ρ, _, c', Rr, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl,
          retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
        FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2, rfl, rfl, hleT,
        FlatShadowPub.envShrink_pubS η ad.label _, fun _ h => h⟩
  | intoRgn hr hu hrc hb =>
    rename_i c₁ r u
    obtain ⟨rt, ws, R0, Rr, hea, -, -, hvR, hi1R, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    have hR0 := VRR_cell_RB rfl hvR
    obtain ⟨hi1, lab, c0, pw, μr, ru, hea', hpw, hsto, hcty, hown, hacc, hl⟩ := ownPtr_invB hu hi.1
    rw [hea] at hea'
    cases hea'
    have hwsv : [pw].map (·.val) = [.loc ⟨lab, 0⟩ 0] := by simp [hpw]
    have hF := pubTyFactsB hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
      (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1)
      (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .ptr (.rgn (.lit 0)) ru, [pw]) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    have hx : ExtB η (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr)) :=
      Ext_withStoB hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _)
    have hE' : EnvOKB p (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr)) :=
      ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    have hleT : Rr + Rs + ownW .own [pw] ≤ Rf + Rs := Res.le_def.2 fun k => by
      have h1 := Res.le_def.1 hle k
      have h3 := congrArg (fun R : Res => R k) hR0
      simp only [Res.add_apply] at h1 h3 ⊢; omega
    intro r' hr'
    rw [key, List.mem_singleton] at hr'
    subst hr'
    have hvz : VRRB ρ (η.withStoB η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr)) (.ptr (.rgn r) u)
        (shp (.ptr (.rgn (.lit 0)) ru)) [pw] .zero := by
      simp only [VRRB]
      exact ⟨⟨⟨lab, 0⟩, c0, hwsv, rfl, hsto, hcty,
        ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withStoB, pubP],
          Or.inr (Or.inr ⟨hown, Or.inr (fun N e h => hacc (by rw [h]; rfl))⟩)⟩, hacc⟩, by simp [ownW]⟩
    have hlay : Lay th.σs (.ptr (.rgn r) u) (.ptr (.rgn (.lit 0)) ru) [pw] :=
      Lay_ptr_remode hl (by simp [skelM]) (by simp [modeC, idxC, ofMs])
    have hfr := bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi1R) (RLink_ofB hE'.2.1 hE'.2.2) hvz hlay
    rw [Res.add_zero] at hfr
    exact ⟨_, [pw], _, Rr + Rs, hea, ⟨ρ, _, c', Rr, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl,
        retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      FlatShadowPub.MemInv_publishSB hm hsto hown hF.1 hF.2.1 hF.2.2.1 hF.2.2.2, rfl, rfl, hleT,
      FlatShadowPub.envShrink_pubS η lab _, fun _ h => h⟩

/-- `PubScope ∧ RgnCpl` at a `region` from the source scope (`StepScopeR` is `False` there). -/
theorem rgnScope_ofS {σs : List Ty} {cx : Cx} {a : At} {rn pn tn : String} {e : Expr}
    (h : ScopeD σs cx (.region a rn pn tn e)) : PubScope cx a ∧ RgnCpl cx a := by
  rcases h with h | ⟨h, -⟩
  · exact h
  · exact h.elim

/-- `PubScope ∧ RgnCpl` at an `intoRgn` from the source scope. -/
theorem intoScope_ofS {σs : List Ty} {cx : Cx} {y rn : String} {a : At} {e : Expr}
    (h : ScopeD σs cx (.let_ y (.intoRgn rn a) e)) : PubScope cx a ∧ RgnCpl cx a := by
  rcases h with h | ⟨-, x', e', ⟨a, b, h⟩ | ⟨a, h⟩ | ⟨a, h⟩⟩
  · exact h
  all_goals cases h
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

-- g1m7 shadow tgt twins
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- the easy-step target at a shadow `intoRgn` (`tgt_publishS` shape). -/
theorem tgt_intoS {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y rn : String} {a : At} {e : Expr} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (hterm : th.term = .let_ y (.intoRgn rn a) e) (hPS : PwSkel) : TgtB p g x n (CE η) mem pairs th := by
  intro r hr _
  have hsc := intoScope_ofS (by rw [← hterm]; exact hS.sc)
  obtain ⟨rt, ws, E1, Tot', -, hT', hm', e1, e2, hle, hx, hsn⟩ := into_stepS (hDy := hS.dy) hterm hP hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm
    hsc.2 hsc.1 hS.rp hPS r hr
  obtain ⟨HP', hH', hle'⟩ := memHeldP_shrinkB hx e1 e2 hS.hH
  refine ⟨E1, Tot', HP', hT', hm', hH', fun l cl h => hS.nie l cl (by rw [← hx.2.2.2.1]; exact h),
    by rw [hx.2.2.2.1]; exact hS.sto, ?_,
    TermOwnX2.Flat.anchStep_shrinkB (ext_shrinkB hT' hx hsn) hx.2.2.2.1 hx.2.2.2.2.1 e1 e2 hx.2.2.2.2.2.1, hS.tyk hr (fun l c h => by rw [← hx.2.2.2.1]; exact h)⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h2 := hle' (.own x)
  have h3 := hS.le
  simp only [Res.add_apply] at h1 h3
  omega

/-- the step target at a shadow `region` (the minted `rg`/`wd` keys are not `own x`). -/
theorem tgt_regionS {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {a : At} {rn pn tn : String} {e : Expr} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (hterm : th.term = .region a rn pn tn e) (hPS : PwSkel) : TgtB p g x n (CE η) mem pairs th := by
  intro r hr _
  have hsc := rgnScope_ofS (by rw [← hterm]; exact hS.sc)
  obtain ⟨rt, ws, E1, Tot', -, hT', hm', e1, e2, hle, hx, hsn⟩ := rgn_stepS (hDy := hS.dy) hterm hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm
    hsc.2 hsc.1 hS.rp hPS r hr
  obtain ⟨HP', hH', hle'⟩ := memHeldP_shrinkB hx e1 e2 hS.hH
  refine ⟨E1, Tot', HP', hT', hm', hH', fun l cl h => hS.nie l cl (by rw [← hx.2.2.2.1]; exact h),
    by rw [hx.2.2.2.1]; exact hS.sto, ?_,
    TermOwnX2.Flat.anchStep_shrinkB (ext_shrinkB hT' hx hsn) hx.2.2.2.1 hx.2.2.2.2.1 e1 e2 hx.2.2.2.2.2.1, hS.tyk hr (fun l c h => by rw [← hx.2.2.2.1]; exact h)⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h2 := hle' (.own x)
  have h3 := hS.le
  simp only [Res.add_apply, Res.one_apply] at h1 h3
  simp at h1
  omega

/-- (for `EtaFence.TgtRgnS`): `tgt_publish1S` at a shadow `region` of `x` (count 1 → 0). -/
theorem tgt_region1S {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} {a : At} {rn pn tn : String} {e : Expr}
    (hS : SrcB p g x 1 mem pairs th ρ η cx Rf Rs HP) (hterm : th.term = .region a rn pn tn e)
    (hea0 : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hxl : ad.label = x) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ E Tot HP, ThInvREB g.lbase g.n g.i p E r.2.2 Tot ∧
      MemInvB g E (stOf r.1 r.2.1 r.2.2) ∧ MemHeldPB E (stOf r.1 r.2.1 r.2.2) HP ∧ TermOwnX2.StoNIE E ∧
      E.sto x ≠ none ∧ Tot (.own x) + HP (.own x) ≤ 0 ∧
      TermOwnX2.Flat.AnchStepB g th (CE η) E (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧
      TyOKE { g with tys := tysUpd g.tys th r.2.2 } E ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc ∧
      E.ini = (CE η).ini ∧ E.rini = (CE η).rini := by
  intro r hr _
  have hsc := rgnScope_ofS (by rw [← hterm]; exact hS.sc)
  obtain ⟨rt', ws', E1, Tot', hea, hT', hm', e1, e2, hle, hx, hsn⟩ := rgn_stepS (hDy := hS.dy) hterm hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm
    hsc.2 hsc.1 hS.rp hPS r hr
  rw [hea0, Option.some.injEq, Prod.mk.injEq] at hea
  obtain ⟨-, rfl⟩ := hea
  obtain ⟨HP', hH', hle'⟩ := memHeldP_shrinkB hx e1 e2 hS.hH
  refine ⟨E1, Tot', HP', hT', hm', hH', fun l cl h => hS.nie l cl (by rw [← hx.2.2.2.1]; exact h),
    by rw [hx.2.2.2.1]; exact hS.sto, ?_,
    TermOwnX2.Flat.anchStep_shrinkB (ext_shrinkB hT' hx hsn) hx.2.2.2.1 hx.2.2.2.2.1 e1 e2 hx.2.2.2.2.2.1,
    (hS.tyk hr (fun l c h => by rw [← hx.2.2.2.1]; exact h)).1, (hS.tyk hr (fun l c h => by rw [← hx.2.2.2.1]; exact h)).2,
    hx.2.2.2.2.1, hx.2.2.2.2.2.1⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h2 := hle' (.own x)
  have h3 := hS.le
  rw [ownW_own_loc hws, hxl] at h1
  simp only [Res.add_apply, Res.one_apply, ite_true] at h1 h3
  simp at h1
  omega

/-- (for `EtaFence.TgtIntoS`): `tgt_publish1S` at a shadow `intoRgn` of `x` (count 1 → 0). -/
theorem tgt_into1S {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} {y rn : String} {a : At} {e : Expr}
    (hS : SrcB p g x 1 mem pairs th ρ η cx Rf Rs HP) (hterm : th.term = .let_ y (.intoRgn rn a) e)
    (hea0 : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hxl : ad.label = x) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ E Tot HP, ThInvREB g.lbase g.n g.i p E r.2.2 Tot ∧
      MemInvB g E (stOf r.1 r.2.1 r.2.2) ∧ MemHeldPB E (stOf r.1 r.2.1 r.2.2) HP ∧ TermOwnX2.StoNIE E ∧
      E.sto x ≠ none ∧ Tot (.own x) + HP (.own x) ≤ 0 ∧
      TermOwnX2.Flat.AnchStepB g th (CE η) E (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧
      TyOKE { g with tys := tysUpd g.tys th r.2.2 } E ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc ∧
      E.ini = (CE η).ini ∧ E.rini = (CE η).rini := by
  intro r hr _
  have hsc := intoScope_ofS (by rw [← hterm]; exact hS.sc)
  obtain ⟨rt', ws', E1, Tot', hea, hT', hm', e1, e2, hle, hx, hsn⟩ := into_stepS (hDy := hS.dy) hterm hP hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm
    hsc.2 hsc.1 hS.rp hPS r hr
  rw [hea0, Option.some.injEq, Prod.mk.injEq] at hea
  obtain ⟨-, rfl⟩ := hea
  obtain ⟨HP', hH', hle'⟩ := memHeldP_shrinkB hx e1 e2 hS.hH
  refine ⟨E1, Tot', HP', hT', hm', hH', fun l cl h => hS.nie l cl (by rw [← hx.2.2.2.1]; exact h),
    by rw [hx.2.2.2.1]; exact hS.sto, ?_,
    TermOwnX2.Flat.anchStep_shrinkB (ext_shrinkB hT' hx hsn) hx.2.2.2.1 hx.2.2.2.2.1 e1 e2 hx.2.2.2.2.2.1,
    (hS.tyk hr (fun l c h => by rw [← hx.2.2.2.1]; exact h)).1, (hS.tyk hr (fun l c h => by rw [← hx.2.2.2.1]; exact h)).2,
    hx.2.2.2.2.1, hx.2.2.2.2.2.1⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h2 := hle' (.own x)
  have h3 := hS.le
  rw [ownW_own_loc hws, hxl] at h1
  simp only [Res.add_apply, Res.one_apply, ite_true] at h1 h3
  
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
    (fun _ _ _ _ ht => tgt_intoS hP hS ht hPS)
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
  by_cases hr : TermOwnX2.isRegion th.term = true
  · cases ht : th.term with
    | region a rn pn tn e => exact ownXLe_of_srcB hth hsc hvI hI hs hc id fun ρ η cx Rf Rs HP hS => tgt_regionS hP hS ht hPS
    | _ => rw [ht] at hr; simp [TermOwnX2.isRegion] at hr
  · exact ownXLe_of_srcB hth hsc hvI hI hs hc id fun ρ η cx Rf Rs HP hS =>
      tgt_easyS hP hS (easyK4_of_pkg hq (by simpa using hr)) hS.rp hPS hSub hSig

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
