import WeakCore.TermFootBPP
import WeakCore.TermFootNK

/-! # TermFootBPK (FootBP): the credited thread step with `FootNCE` and `FootBP` on the witness

`tstepMCF_stepTKA_zfNB`: `TermFootNK.tstepMCF_stepTKA_zfN` with `FootBP g E' th r` added to the
witness predicate.  At `publish`, from `tstepMR_publishB` (the published label's frontier is set);
at an allocating term, from the `TermFootBPP` producers (clause (1)); elsewhere both clauses are
vacuous (no fresh label, nothing published).
-/

namespace TermFootBPK
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPiece TermPlant TermFootNC
  TermFootNP TermFootNK TermFootBP0 TermFootBPP
open TermOwnG0Defs
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `mcfs_addFoot` with clause (1) of `FootBP`. -/
theorem mcfs_addFootB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {r : Memory × List Ts × TTh} {Tot H : Res} {cr db : Ts → Res}
    (h : ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H cr db)
    (hn : r.2.2.nalloc ≤ th.nalloc) :
    ThInvMCFSQ (fun E' => FootNCE (CE η) E' r ∧ FootB1 g th.nalloc th.env r E') p g (CE η) (stOf mem pairs th) Sp
      r.1 r.2.1 r.2.2 Tot H cr db :=
  let ⟨E', h0, hr⟩ := h
  ⟨E', ⟨footNC_efoot h0 hn, footB1_nalloc hn⟩, h0, hr⟩

/-- `mc_liftSN` from the `QB` producers. -/
theorem mc_liftSNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η)
        (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (fun E' => FootNCE (CE η) E' r ∧ FootB1 g th.nalloc th.env r E') p g (CE η) (stOf mem pairs th) Sp
        r.1 r.2.1 r.2.2 Tot H' cr db ∧
      MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F :=
  ⟨h.1, fun r hr hp => by
    obtain ⟨Tot, H', hK, hle⟩ := h.2 r hr hp
    exact mc_ofKQ hm hC (ThInvMKQ.mono (fun _ hs => ⟨footNC_sto hs.1, hs.2⟩) hK) hle⟩

/-- Adding clause (1), true at every witness, to the `FootNCE` producers (`new`, `newBuf`). -/
theorem addB1 {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    (hB : ∀ r ∈ tstep g mem pairs th, ∀ E', FootB1 g th.nalloc th.env r E')
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧
      MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (fun E' => FootNCE (CE η) E' r ∧ FootB1 g th.nalloc th.env r E') p g (CE η) (stOf mem pairs th) Sp
        r.1 r.2.1 r.2.2 Tot H' cr db ∧
      MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F :=
  ⟨h.1, fun r hr hp => by
    obtain ⟨Tot, H', C, F, h1, h2⟩ := h.2 r hr hp
    exact ⟨Tot, H', C, F, ThInvMCFSQ.mono (fun E' hq => ⟨hq, hB r hr E'⟩) h1, h2⟩⟩

/-- (FootBP) `tstepMR_publish` with the published label's frontier on the witness. -/
theorem tstepMR_publishB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr}
    {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hsc : PubScope cx a)
    {cr db : Ts → Res} (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hwp : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      NoHold (CE η) (stOf mem pairs th) ad.label)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hown1 : PubLe1 th Rf Rs H := by assumption)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' cr' db' rt ws, evalAt th.env a = some (rt, ws) ∧
        (∀ ad g', ws.map (·.val) = [.loc ad g'] → η.sto ad.label ≠ none) ∧
        ThInvMCFSQ (fun E' => (∀ l, E'.sto l = (CE η).sto l ∧ E'.ini l = (CE η).ini l) ∧ ∀ l, PubAt th l → E'.pfr l ≠ none) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + ownW .own ws ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' := by
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
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind x (.ptr .pub u) = .ok c' := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨rt, ws, R0, Rr, hea, hv, hl, hvR, hi1R, hle⟩ := useR hu hi hE.2.2
    have hR0 := VRR_cell_R rfl hvR
    have hi1 := hi1R.1
    simp only [VR] at hv
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
        cases μ <;> simp [skelM] at hsk
        exact ⟨ru, rfl, hsk⟩
      case refine t ψ => unfold rf at hsk; split at hsk <;> simp [etok] at hsk
    have hown : c.owner = some η.tid := hmode
    have hx : Ext η (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)) :=
      Ext_withSto hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _) (fun l h => Or.inr h)
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .ptr .pub ru, [pw]) :: th.env } (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr hpa0 => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    have hvr : VR ρ (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab))
        (.ptr .pub u) (shp (.ptr .pub ru)) [pw] := by
      simp only [VR]
      exact ⟨⟨lab, 0⟩, c, hws, rfl, hsto, hcty,
        ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withSto, pubP], Or.inl (Or.inl rfl)⟩, hacc⟩
    have hlay : Lay th.σs (.ptr .pub u) (.ptr .pub ru) [pw] :=
      ⟨fun us h => by simp [accs] at h; subst h; rfl, by rw [close_ptr]; simp only [skel, etok, hsku],
        by simp [wc, accs], ⟨⟨lab, 0⟩, hws⟩, by
          simp only [close, substTs, lyt, etok]; rw [(cell_lyt hl.2.2.2.2 rfl rfl).2]; rfl⟩
    have hE' : EnvOK p (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)) :=
      ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    have hvz : VRR ρ (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab))
        (.ptr .pub u) (shp (.ptr .pub ru)) [pw] .zero := by
      simp only [VR] at hvr; simp only [VRR]; exact ⟨hvr, rfl⟩
    have hfr := bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1R) (RLink_of hE'.2.1 hE'.2.2) hvz hlay
    rw [Res.add_zero] at hfr
    have hpa : PromAbove (stOf mem pairs th) := fun t ht m hm' => hpa0 t ht m hm'
    obtain ⟨H', cr', db', ⟨S', hH'L, hSK⟩, hC', heq⟩ :=
      MemHeld_pubS (V := (stOf mem pairs th).vs.vWr) (S := pubS η lab) hm hH hC hpa (hwp _ _ ⟨lab, 0⟩ hea (by simp [hpw])) hfo
        ⟨c, hsto, hown⟩
    have hHn : MemHeldK (CE η) (stOf mem pairs th) Sp (CE (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)))
        (fenceS (stOf mem pairs th) .st) H' := ⟨S', MemHeldL_eqs hH'L rfl rfl, hSK.toT _ _⟩
    have hCn : PromCr (CE (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)))
        (fenceS (stOf mem pairs th) .st) cr' db' :=
      PromCr_keep hC' rfl (MemInv_promLt hm) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    have hleT : Rr + Rs + H' + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db + ownW .own [pw] ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' :=
      Res.le_def.2 fun k => by
        have h1 := Res.le_def.1 hle k
        have h2 := congrArg (fun R : Res => R k) heq
        have h3 := congrArg (fun R : Res => R k) hR0
        simp only [Res.add_apply] at h1 h2 h3 ⊢; omega
    exact ⟨Rr + Rs, H', cr', db', _, [pw], hea,
      (fun ad g' h => by simp only [List.map_cons, List.map_nil, hpw] at h; cases h; simp [hsto]), ⟨CE (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)),
      ⟨fun _ => ⟨rfl, rfl⟩, fun l hl => by rw [pubAt_eq hterm hea (ad := ⟨lab, 0⟩) (by simp [hpw]) hl]; simp [CE, TEnv.withSto, pubP]⟩,
      EFoot_pub (hgp := hPb x a e _ _ ⟨lab, 0⟩ hterm hea (by simp [hpw])) rfl rfl rfl rfl rfl ⟨c, hsto, hown⟩ (fun _ => rfl) (fun _ => Iff.rfl) (hwin _ _ ⟨lab, 0⟩ hea (by simp [hpw])).2.2,
      SeenOK_pubS (pub_zero (ad := ⟨lab, 0⟩) hleT (PromCr_own0 hC _).1 (PromCr_own0 hC' _).2
        (g0 := 0) (by simp [hpw]) (hown1 _ _ _ hterm _ _ ⟨lab, 0⟩ 0 hea (by simp [hpw]))),
      (by boxT), ⟨ρ, η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab), c', Rr, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_publish (E := CE η) (hF := PubWin_of_NoHold (E := CE η) hm hsto hown (hwin _ _ ⟨lab, 0⟩ hea (by simp [hpw]))) hm hsto hown rfl rfl rfl rfl rfl rfl rfl (fun b S hseg _ => by
        obtain ⟨-, rfl⟩ := SegOf_lay hacc hseg
        have hcu : Ty.coupledOKIn c₁.ke u = true := by
          simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
        have htbu : tb c₁.ke.length u = true := by
          have h := (use_TvOK hu htv).2.1
          rw [← (use_TvOK hu htv).2.2] at h
          simpa [tb] using h
        exact TearOK_Fd hcty (TearOK_of_cpl
          (coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu)))
        (coupledOK_Fd hcty (by
          have hcu : Ty.coupledOKIn c₁.ke u = true := by
            simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
          have htbu : tb c₁.ke.length u = true := by
            have h := (use_TvOK hu htv).2.1
            rw [← (use_TvOK hu htv).2.2] at h
            simpa [tb] using h
          exact coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu))
        (noOwn_Fd hcty (by
          have hnu : Ty.noOwnIn c₁.ke u = true := by
            simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
          have htbu : tb c₁.ke.length u = true := by
            have h := (use_TvOK hu htv).2.1
            rw [← (use_TvOK hu htv).2.2] at h
            simpa [tb] using h
          exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
            (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) u hnu htbu))
        (rgnFree_Fd hcty (rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk)
          (by simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1)
          (hsc _ (use_cases hu).1 _ _ (Or.inl rfl)))),
      hHn, hCn⟩, hleT⟩
  | publishBuf hu hsh hb =>
    obtain ⟨n, k, u, c₁, hu, hsh, hb⟩ : ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) ∧
        Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true ∧
        c₁.bind x (.refine (.loc .pub (.array n u)) (.ini k)) = .ok c' := ⟨_, _, _, _, hu, hsh, hb⟩
    obtain ⟨rb, wsb, R0, Rr, hea, hvb, hlb, hvR, hi1R, hle⟩ := useR hu hi hE.2.2
    have hR0 := VRR_buf_R rfl hvR
    have hi1 := hi1R.1
    simp only [VR] at hvb
    obtain ⟨hv, hir⟩ := hvb
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
          withS { th with term := e, env := (x, .refine (.loc .pub (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr hpa0 => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat, hFU, hmode, hini⟩
    · -- a null handle (an empty buffer): only the fence
      have hvr : VR ρ η (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VR]; exact ⟨Or.inl ⟨hnull, e0, he0⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      have hvz : VRR ρ η (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb .zero := by
        simp only [VRR]; exact ⟨⟨Or.inl ⟨hnull, e0, he0⟩, rfl⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      have hfr := bindR hb hi1R (RLink_of hE.2.1 hE.2.2) hvz hlay
      rw [Res.add_zero] at hfr
      have hleT : Rr + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db + ownW .own wsb ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db :=
        Res.le_def.2 fun k => by
          have h1 := Res.le_def.1 hle k
          have h3 := congrArg (fun R : Res => R k) hR0
          simp only [Res.add_apply] at h1 h3 ⊢; omega
      exact ⟨Rr + Rs, H, cr, db, _, wsb, hea, (fun ad' g' h => by rw [hnull] at h; cases h), ⟨CE η, ⟨fun _ => ⟨rfl, rfl⟩, fun l hl => absurd hl (pubAt_not hterm hea (fun ad h => by rw [hnull] at h; cases h))⟩, EFoot_refl, (by seenT), (by boxT), ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_fence hm,
        MemHeldK_eqs hH rfl rfl, PromCr_keep hC rfl (MemInv_promLt hm) (fun _ _ => rfl) (fun _ _ _ _ => rfl)⟩, hleT⟩
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c.owner = some η.tid := hmode
      have hx : Ext η (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)) :=
        Ext_withSto hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _) (fun l h => Or.inr h)
      have hvr : VR ρ (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label))
          (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
        simp only [VR]
        exact ⟨Or.inr ⟨ad, c, _, hws, hsto, hat, .refl,
          ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withSto, pubP], Or.inl (Or.inl rfl)⟩,
          (IniAt_mono (modeIni_le_ini _ _ _) hini)⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      have hE' : EnvOK p (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)) :=
        ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
      have hvz : VRR ρ (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label))
          (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb .zero := by
        simp only [VR] at hvr; simp only [VRR]; exact ⟨⟨hvr.1, rfl⟩, hvr.2⟩
      have hfr := bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1R) (RLink_of hE'.2.1 hE'.2.2) hvz hlay
      rw [Res.add_zero] at hfr
      have hpa : PromAbove (stOf mem pairs th) := fun t ht m hm' => hpa0 t ht m hm'
      obtain ⟨H', cr', db', ⟨S', hH'L, hSK⟩, hC', heq⟩ :=
        MemHeld_pubS (V := (stOf mem pairs th).vs.vWr) (S := pubS η ad.label) hm hH hC hpa (hwp _ _ ad hea hws) hfo
          ⟨c, hsto, hown⟩
      have hHn : MemHeldK (CE η) (stOf mem pairs th) Sp (CE (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)))
          (fenceS (stOf mem pairs th) .st) H' := ⟨S', MemHeldL_eqs hH'L rfl rfl, hSK.toT _ _⟩
      have hCn : PromCr (CE (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)))
          (fenceS (stOf mem pairs th) .st) cr' db' :=
        PromCr_keep hC' rfl (MemInv_promLt hm) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      have hleT : Rr + Rs + H' + pSum (stOf mem pairs th) cr' + pSum (stOf mem pairs th) db + ownW .own wsb ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db' :=
        Res.le_def.2 fun k => by
          have h1 := Res.le_def.1 hle k
          have h2 := congrArg (fun R : Res => R k) heq
          have h3 := congrArg (fun R : Res => R k) hR0
          simp only [Res.add_apply] at h1 h2 h3 ⊢; omega
      exact ⟨Rr + Rs, H', cr', db', _, wsb, hea, (fun ad' g' h => by rw [hws] at h; cases h; simp [hsto]), ⟨CE (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)),
        ⟨fun _ => ⟨rfl, rfl⟩, fun l hl => by rw [pubAt_eq hterm hea hws hl]; simp [CE, TEnv.withSto, pubP]⟩,
        EFoot_pub (hgp := hPb x a e _ _ ad hterm hea hws) rfl rfl rfl rfl rfl ⟨c, hsto, hown⟩ (fun _ => rfl) (fun _ => Iff.rfl) (hwin _ _ ad hea hws).2.2,
        SeenOK_pubS (pub_zero (ad := ad) hleT (PromCr_own0 hC _).1 (PromCr_own0 hC' _).2 hws
          (hown1 _ _ _ hterm _ _ _ _ hea hws)),
        (by boxT), ⟨ρ, η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label), c', Rr, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
        MemInv_publish (E := CE η) (hF := PubWin_of_NoHold (E := CE η) hm hsto hown (hwin _ _ ad hea hws)) hm hsto hown rfl rfl rfl rfl rfl rfl rfl
          (fun b S hseg ha => by
            rcases hseg with ⟨-, rfl, -⟩ | ⟨N, usS, j, hT, -, -, -⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · have e1 := AtOff_arr_here hat hT ha (by simp [cl, accs])
              rw [hT] at e1
              simp only [cl, Ty.array.injEq] at e1
              obtain ⟨-, rfl⟩ := e1
              have hcu : Ty.coupledOKIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
              have htbu : tb c₁.ke.length (.array n u) = true := by
                have h := (use_TvOK hu htv).2.1
                rw [← (use_TvOK hu htv).2.2] at h
                simpa [tb] using h
              have := coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk)
                hcu htbu
              simp only [cl, Ty.coupledOK, Ty.coupledOKIn] at this; exact TearOK_of_cpl this)
          (by
            obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
            rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              have hcu : Ty.coupledOKIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
              have htbu : tb c₁.ke.length (.array n u) = true := by
                have h := (use_TvOK hu htv).2.1
                rw [← (use_TvOK hu htv).2.2] at h
                simpa [tb] using h
              exact coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk)
                hcu htbu)
          (by
            obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
            rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              have hnu : Ty.noOwnIn c₁.ke (.array n u) = true := by
                simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
              have htbu : tb c₁.ke.length (.array n u) = true := by
                have h := (use_TvOK hu htv).2.1
                rw [← (use_TvOK hu htv).2.2] at h
                simpa [tb] using h
              exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
                (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) _ hnu htbu)
          (by
            obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
            rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
            · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
            · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
              exact rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk)
                (by simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1)
                (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))),
        hHn, hCn⟩, hleT⟩

/-- (FootBP) `tstepMC_publishP` with the published label's frontier on the witness. -/
theorem tstepMC_publishPB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr}
    {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    {cr db : Ts → Res} (hC : PromCr (CE η) (stOf mem pairs th) cr db) (hsc : PubScope cx a)
    (hwp : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      NoHold (CE η) (stOf mem pairs th) ad.label)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hown1 : PubLe1 th Rf Rs H := by assumption)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F cr' db',
      ThInvMCFSQ (fun E' => (∀ l, E'.sto l = (CE η).sto l ∧ E'.ini l = (CE η).ini l) ∧ ∀ l, PubAt th l → E'.pfr l ≠ none) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      ClaimAtP th C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F := by
  have h := tstepMR_publishB (hDy := hDy) (hPb := hPb) hterm hP hT hCk hi hE htv hm hH hsc hC hwp hwin hfo hRP hPS
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨Tot, H', cr', db', rt, ws, hev, -, h1, h2⟩ := h.2 r hr hpa
  refine ⟨Tot, H', ownW .own ws, .zero, cr', db', h1, .consume .own ws,
    ⟨(MintStepN.consume (g := g) (η := η) (s := stOf mem pairs th) (s' := stOf r.1 r.2.1 r.2.2) .own ws).claimAt _, ?_⟩, ?_⟩
  · intro y a' e' rt' ws' ad ht' hev' hws'
    rw [hterm] at ht'
    cases ht'
    rw [hev] at hev'
    cases hev'
    rw [ownW_own_loc hws']
    simp
  · simp only [Res.add_zero]
    exact h2

/-- (FootBP) `TermFootNK.tstepMCF_stepKN` at an allocating term, with clause (1) of `FootBP`. -/
theorem tstepMCF_stepKAB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (_hia : StoreIall ρ η cx th)
    (_hdw : StoreCrZ η cx (stOf mem pairs th) th) (_hnvp : OwnOpT cx th.term → OwnNVPF (CE η) (stOf mem pairs th))
    (_hnp : ∀ x a e, th.term ≠ .let_ x (.publish a) e)
    (_hfo : FpOK (CE η) (stOf mem pairs th)) (_hRF : OwnFrontierRMWT (CE η) (stOf mem pairs th) th.term) (_hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    (hAl : AllocT th.term) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (_hZ : ZOK g (CE η) th := by exact fun _ _ h => False.elim h) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (fun E' => FootNCE (CE η) E' r ∧ FootB1 g th.nalloc th.env r E') p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAt th.term C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F := by
  by_cases hR : StepScopeR th.σs cx th.term
  · have h0 := tstepMC_frame (hDy := hDy) hP hp hnd hR hT hCk hi hE htv hm hH hC hRP hPS hSub hSig
    have hna := frame_nalloc (g := g) (mem := mem) (pairs := pairs) hAl hR hT hCk hi hE htv
    refine ⟨h0.1, fun r hr _ => ?_⟩
    obtain ⟨Tot, H', C, F, h1, h2⟩ := h0.2 r hr
    exact ⟨Tot, H', C, F, mcfs_addFootB h1 (hna r hr), h2⟩
  have hsc' := hsc.resolve_right hR
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsc' hAl
  cases hT0 with
  | let_ hop _ =>
    cases hop
    case inl => exact cNQ <| mc_liftSNB hm hC <| tstepMR_inlTNB (hDy := hDy) (hbf := hbf) (hpx := hpx) ht hP hn hT hCk hi hE htv hm hH hRP hPS
    case inr => exact cNQ <| mc_liftSNB hm hC <| tstepMR_inrTNB (hDy := hDy) (hbf := hbf) (hpx := hpx) ht hP hn hT hCk hi hE htv hm hH hRP hPS
    case new => exact cNQ <| addB1 (fun r hr _ => footB1_new ht hr) <| mc_liftFN hm hC <| tstepMR_newN (hDy := hDy) ht hsc' hP hn hT hCk hi hE htv hm hH hRP hPS
    case newBuf => exact cNQ <| addB1 (fun r hr _ => footB1_newBuf ht hr) <| mc_liftFN hm hC <| tstepMR_newBufN (hDy := hDy) ht hsc' hP hn hT hCk hi hE htv hm hH hRP hPS
    all_goals exact hAl.elim
  | case => exact cNQ <| mc_liftSNB hm hC <| tstepMR_caseTNB (hDy := hDy) (hbf := hbf) (hpx := hpx) ht hn hT hCk hi hE htv hm hH hRP hPS
  | _ => exact hAl.elim

theorem tstepMCF_stepKABN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (_hia : StoreIall ρ η cx th)
    (_hdw : StoreCrZ η cx (stOf mem pairs th) th) (_hnvp : OwnOpT cx th.term → OwnNVPF (CE η) (stOf mem pairs th))
    (_hnp : ∀ x a e, th.term ≠ .let_ x (.publish a) e)
    (_hfo : FpOK (CE η) (stOf mem pairs th)) (_hRF : OwnFrontierRMWT (CE η) (stOf mem pairs th) th.term) (_hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    (hAl : AllocT th.term) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (_hZ : ZOK g (CE η) th := by exact fun _ _ h => False.elim h) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (fun E' => (FootNCE (CE η) E' r ∧ FootB1 g th.nalloc th.env r E') ∧ NewCellSto g ρ η th E') p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAt th.term C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F  := by
  by_cases hnw : ∃ x a T e, th.term = .let_ x (.new a (some T)) e
  · obtain ⟨x, a, T, e, ht⟩ := hnw
    have hR : ¬ StepScopeR th.σs cx th.term := by
      intro hR
      rw [ht] at hR
      simp only [StepScopeR, OpScopeR] at hR
    have hsc' := hsc.resolve_right hR
    rw [ht] at hsc'
    have h0 := tstepMR_newNS (hDy := hDy) ht hsc' hP hn hT hCk hi hE htv hm hH hRP hPS
    refine ⟨h0.1, fun r hr _ => ?_⟩
    obtain ⟨Tot, H', hK, hf, hle⟩ := h0.2 r hr
    obtain ⟨Tot, H', C, F, h1, h2, h3⟩ := mc_ofKFQ hm hC hK (.alloc hf (FreshIn_sto hm.2.2.2.1 hf)) hle
    exact ⟨Tot, H', C, F, ThInvMCFSQ.mono (fun E' hq => ⟨⟨hq.1, footB1_new ht hr⟩, hq.2⟩) h1, h2.toM, h2.claimAt _, h3⟩
  · have h := tstepMCF_stepKAB (hDy := hDy) (_hZ := _hZ) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC _hia _hdw _hnvp
      _hnp _hfo _hRF _hrmw hbf hAl hRP hPS hSub hSig hTy
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨Tot, H', C, F, h1, h2⟩ := h.2 r hr hpa
    exact ⟨Tot, H', C, F, ThInvMCFSQ.mono (fun E' hq => ⟨hq, NewCellSto_vac fun x a T e he => hnw ⟨x, a, T, e, he⟩⟩) h1, h2⟩

theorem tstepMCF_stepTKA_zfNBCN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    {KP : Memory × List Ts × TTh → TEnv → (Ts → Res) → (Ts → Res) → Prop}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hpx : PAx g mem pairs th) (hC : PromCrK (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    {Ok : Memory × List Ts × TTh → Prop}
    (hbi : ∀ x b i v e, th.term = .let_ x (.bufInit b i v) e →
      (∀ rt w ad rti wi n, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 →
        evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → (CE η).pfr ad.label ≠ none →
        (CE η).rc ad.label ≤ n → n < (CE η).ini ad.label) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∀ o, PredU (CE η) ⟨ad.label, o⟩ → ∃ h, FirstW (stOf mem pairs th).mem ⟨ad.label, o⟩ h ∧
        h ∈ (stOf mem pairs th).promises ∧ ∀ t m, t ∈ (stOf mem pairs th).promises →
          (stOf mem pairs th).mem[t]? = some m → m.loc = ⟨ad.label, o⟩ →
          (stOf mem pairs th).vs.coh ⟨ad.label, o⟩ < t → h ≤ t) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∃ Sp, MemHeldL (CE η) (stOf mem pairs th) H Sp ∧ SlotPayS (CE η) (stOf mem pairs th) Sp cr db ad.label)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hown1 : PubLe1 th Rf Rs H)
    (hlift : ∀ r E' cr' plh, (∀ x b i v e, th.term ≠ .let_ x (.bufInit b i v) e) →
      KeepQRS (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' plh → KP r E' cr' plh)
    (hzf : ¬ AllocT th.term → (∀ x a e, th.term ≠ .let_ x (.publish a) e) →
      tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
        (OwnFrOp (CE η) cx th → r.1 = mem) ∧ Ok r → ∃ Tot H' C F cr' db' Gd plh,
        ThInvMCFQK (fun E' => BiOut th E' ∧ KP r E' cr' plh ∧
            IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
              (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
          p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
        Drop (CE η) (stOf mem pairs th) Gd ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) +
            pSum (stOf r.1 r.2.1 r.2.2) plh ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
        (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) ∧
          (¬ PubShape cx th → Gd = []))
    (hz0 : ∀ l, ¬ g.zf l := by exact fun _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      (OwnFrOp (CE η) cx th → r.1 = mem) ∧ Ok r → ∃ Tot H' C F cr' db' Gd plh,
      ThInvMCFQK (fun E' => BiOut th E' ∧ KP r E' cr' plh ∧
          IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
            (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ FootNCE (CE η) E' r ∧ FootBP g E' th r ∧ NewCellSto g ρ η th E')
        p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
      MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) +
          pSum (stOf r.1 r.2.1 r.2.2) plh ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) ∧
        (¬ PubShape cx th → Gd = []) := by
  by_cases hpub : ∃ x a e, th.term = .let_ x (.publish a) e
  · obtain ⟨x, a, e, ht⟩ := hpub
    have hAl : ¬ AllocT th.term := by rw [ht]; exact id
    have hR : ¬ StepScopeR th.σs cx th.term := by rw [ht]; simp only [StepScopeR, OpScopeR]; exact id
    have hsc' := hsc.resolve_right hR
    rw [ht] at hsc'
    have hnop : opAtomP th.term = none := by rw [ht]; rfl
    have hps : ¬ PubShape cx th := fun ⟨_, _, _, _, _, _, _, h, _⟩ => by rw [ht] at h; cases h
    have hnb : ∀ x b i v e, th.term ≠ .let_ x (.bufInit b i v) e := fun _ _ _ _ _ h => by rw [ht] at h; cases h
    obtain ⟨Sp, hHL⟩ := hH.toS
    have hP0 := tstepMC_publishPB (hDy := hDy) (g := { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l })
      (hPb := hPb) ht hP hT hCk hi hE htv hm hHL (PromCrP_drop hC.toP) hsc' (fun rt ws ad => hwp x a e rt ws ad ht)
      (fun rt ws ad => hwin x a e rt ws ad ht) hfo hRP hPS
    refine ⟨hP0.1, fun r hr hpa _ => ?_⟩
    obtain ⟨Tot, H', C, F, cr', db', h1, h2, hcl, h3⟩ := hP0.2 r hr hpa
    obtain ⟨E', hq, h0, hSK, hBV, hT', hm', hH', hC'⟩ := h1
    obtain ⟨cr'', hK, hPK, hbal⟩ := pubFix (cr := cr) (g := { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l })
      hm (TermLiveProps.tstep_ext _ mem pairs th r hr) h0 hq.1 (MemInv_nodup hm') hC'
    have hle : Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr'' + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F := fun k => by
      have b1 := h3 k; have b2 := hbal k
      simp only [Res.add_apply] at b1 b2 ⊢
      omega
    have hna := Nat.le_of_eq (tstep_nalloc hAl r hr)
    exact ⟨Tot, H', C, F, cr'', db', [], fun _ => .zero,
      ⟨E', ⟨biOut_nb hnb, hlift r E' cr'' (fun _ => .zero) hnb (keepQRS_of_keepQ (fun hnp => (hnp x a e ht).elim)
          (covS_nil (RepinCovU_nop hnop)) (fulP_nop hnop) (rcKeepP_nop hnop) (fun _ => hPK)), h0.iniFixZ, footNC_efoot h0 hna,
          ⟨footB1_nalloc hna, hq.2⟩, NewCellSto_vac fun x' a' T' e' h' => by rw [ht] at h'; cases h'⟩,
        efootDrop hz0 h0, hSK, hBV, hT', hm', hH'.memHeld, hK⟩,
      mintStepDrop h2, hcl, Drop_nil, le_plh0 (G_nil hle), fun h => absurd h hps, fun _ => rfl⟩
  have hnpub : ∀ x a e, th.term ≠ .let_ x (.publish a) e := fun x a e h => hpub ⟨x, a, e, h⟩
  by_cases hAl : AllocT th.term
  rotate_left
  · have h := hzf hAl hnpub
    refine ⟨h.1, fun r hr hpa hok => ?_⟩
    obtain ⟨Tot, H', C, F, cr', db', Gd, plh, ⟨E', hq, hF, hR⟩, hR2⟩ := h.2 r hr hpa hok
    exact ⟨Tot, H', C, F, cr', db', Gd, plh,
      ⟨E', ⟨hq.1, hq.2.1, hq.2.2, footNC_efoot hF (Nat.le_of_eq (tstep_nalloc hAl r hr)),
        ⟨footB1_nalloc (Nat.le_of_eq (tstep_nalloc hAl r hr)), fun l hl => absurd hl (pubAt_nopub hnpub)⟩,
        NewCellSto_vac fun x a T e he => hAl (by rw [he]; simp only [AllocT, AllocOp])⟩, hF, hR⟩, hR2⟩
  have hne : ∀ x op e, th.term = .let_ x op e → AllocOp op := fun x op e h => by rw [h] at hAl; exact hAl
  have hO : ¬ OwnOpT cx th.term := by
    rintro (⟨x, e, ⟨a, v, h⟩ | ⟨b, i, v, h⟩ | ⟨b, i, q, v, h⟩ | ⟨b, wi, jl, v, h⟩ | ⟨b, i, v, h⟩ | ⟨b, i, v, h⟩⟩ |
      ⟨x, rel, a, v, tok, e, u, h, -⟩) <;> exact hne _ _ _ h
  have hps : ¬ PubShape cx th := fun ⟨x, rel, a, v, tok, e, u, h, _⟩ => hne _ _ _ h
  have hnp : ∀ x a e, th.term ≠ .let_ x (.publish a) e := fun x a e h => hne _ _ _ h
  have hnb : ∀ x b i v e, th.term ≠ .let_ x (.bufInit b i v) e := fun x b i v e h => hne _ _ _ h
  have hnopA : opAtomP th.term = none := by
    generalize th.term = t0 at hAl
    cases t0 with
    | let_ x op e => cases op <;> first | rfl | (simp only [AllocT, AllocOp] at hAl)
    | _ => rfl
  have hZ2 : ZOK { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) th := by
    intro l _ hzl x b i v e ht rt w ad rti wi n h1 h2 h3 h4 hl hpf hrc
    subst hl
    have hlo := (hbi x b i v e ht).1 rt w ad rti wi n h1 h2 h3 h4 hpf hrc
    exact ⟨hlo, Nat.lt_of_lt_of_le hlo hzl.2⟩
  obtain ⟨Sp, hHL⟩ := hH.toS
  have hC' := PromCrP_drop hC.toP
  have hK0 := tstepMCF_stepKABN (hDy := hDy) (g := { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l })
    (_hZ := hZ2) hP hp hn hnd hsc hT hCk hi hE htv hm hHL hpx hC' hia hdw (fun h => absurd h hO) hnp hfo
    (fun h => absurd (Or.inl h) hO) hrmw hbf hAl hRP hPS hSub hSig hTy
  have hV := repinCovU_stepK (g := { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l })
    (mem := mem) (pairs := pairs) hsc hT hi hE htv hO hps
  refine ⟨hK0.1, fun r hr hpa _ => ?_⟩
  obtain ⟨Tot, H', C, F, h1, h2, hcl, h3⟩ := hK0.2 r hr hpa
  obtain ⟨cr', hA, hsw, -⟩ := ThInvMCFSQ.toKA (th0 := th) h1
    (TermLiveProps.tstep_ext { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l }
      mem pairs th r hr).prom
  obtain ⟨E', hq, hF, hR⟩ := (ThInvMCFSQK.mono (Q' := fun E' => BiOut th E' ∧
    KP r E' cr' (fun _ => .zero) ∧
      ((FootNCE (CE η) E' r ∧ FootB1 g th.nalloc th.env r E') ∧ NewCellSto g ρ η th E'))
    (fun E' hk => ⟨biOut_nb hnb, hlift r E' cr' (fun _ => .zero) hnb (keepQRS_of_keepQ hk.2 (covS_nil (hV r hr E')) (fulP_nop hnopA) (rcKeepP_nop hnopA) (pubKeep_np hnp)), hk.1⟩) hA).toFQK
  refine ⟨Tot, H', C, F, cr', db, [], fun _ => .zero, ⟨E', ⟨hq.1, hq.2.1, hF.iniFixZ, hq.2.2.1.1, ⟨hq.2.2.1.2, fun l hl => absurd hl (pubAt_nopub hnpub)⟩, hq.2.2.2⟩, efootDrop hz0 hF, hR⟩,
    mintStepDrop h2, ClaimAtP.of_not hcl (fun x a e h => hnp x a e h), Drop_nil,
    le_plh0 (G_nil (Res.le_def.2 fun k => ?_)), fun h => absurd h hps, fun _ => rfl⟩
  have e1 := h3 k
  have e2 := hsw k
  simp only [Res.add_apply] at e1 e2 ⊢
  omega

/-- (BI) **`tstepMCF_stepTKA_zfNB` over a keep predicate `KP`**: the proof of `zfNB` with the
non-allocating, non-`publish` step supplied by `hzf` and `KeepQRS` lifted to `KP` off `bufInit` (`hlift`);
also concludes `¬ PubShape → Gd = []`. -/
theorem tstepMCF_stepTKA_zfNBC {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    {KP : Memory × List Ts × TTh → TEnv → (Ts → Res) → (Ts → Res) → Prop}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hpx : PAx g mem pairs th) (hC : PromCrK (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    {Ok : Memory × List Ts × TTh → Prop}
    (hbi : ∀ x b i v e, th.term = .let_ x (.bufInit b i v) e →
      (∀ rt w ad rti wi n, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 →
        evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → (CE η).pfr ad.label ≠ none →
        (CE η).rc ad.label ≤ n → n < (CE η).ini ad.label) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∀ o, PredU (CE η) ⟨ad.label, o⟩ → ∃ h, FirstW (stOf mem pairs th).mem ⟨ad.label, o⟩ h ∧
        h ∈ (stOf mem pairs th).promises ∧ ∀ t m, t ∈ (stOf mem pairs th).promises →
          (stOf mem pairs th).mem[t]? = some m → m.loc = ⟨ad.label, o⟩ →
          (stOf mem pairs th).vs.coh ⟨ad.label, o⟩ < t → h ≤ t) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∃ Sp, MemHeldL (CE η) (stOf mem pairs th) H Sp ∧ SlotPayS (CE η) (stOf mem pairs th) Sp cr db ad.label)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hown1 : PubLe1 th Rf Rs H)
    (hlift : ∀ r E' cr' plh, (∀ x b i v e, th.term ≠ .let_ x (.bufInit b i v) e) →
      KeepQRS (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' plh → KP r E' cr' plh)
    (hzf : ¬ AllocT th.term → (∀ x a e, th.term ≠ .let_ x (.publish a) e) →
      tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
        (OwnFrOp (CE η) cx th → r.1 = mem) ∧ Ok r → ∃ Tot H' C F cr' db' Gd plh,
        ThInvMCFQK (fun E' => BiOut th E' ∧ KP r E' cr' plh ∧
            IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
              (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
          p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
        Drop (CE η) (stOf mem pairs th) Gd ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) +
            pSum (stOf r.1 r.2.1 r.2.2) plh ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
        (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) ∧
          (¬ PubShape cx th → Gd = []))
    (hz0 : ∀ l, ¬ g.zf l := by exact fun _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      (OwnFrOp (CE η) cx th → r.1 = mem) ∧ Ok r → ∃ Tot H' C F cr' db' Gd plh,
      ThInvMCFQK (fun E' => BiOut th E' ∧ KP r E' cr' plh ∧
          IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
            (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ FootNCE (CE η) E' r ∧ FootBP g E' th r)
        p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
      MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) +
          pSum (stOf r.1 r.2.1 r.2.2) plh ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) ∧
        (¬ PubShape cx th → Gd = [])  := by
  have h := tstepMCF_stepTKA_zfNBCN (hDy := hDy) (KP := KP) (Ok := Ok) (hz0 := hz0) (hPb := hPb) hP hp hn hnd hsc hT hCk hi
    hE htv hm hH hpx hC hia hdw hwp hwin hfo hrmw hbf hbi hPS hSub hSig hTy hRP hown1 hlift hzf
  refine ⟨h.1, fun r hr hpa hok => ?_⟩
  obtain ⟨Tot, H', C, F, cr', db', Gd, plh, ⟨E', hq, hR⟩, hR2⟩ := h.2 r hr hpa hok
  exact ⟨Tot, H', C, F, cr', db', Gd, plh, ⟨E', ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1⟩, hR⟩, hR2⟩

#print axioms tstepMCF_stepTKA_zfNBC

/-- **(FootBP) `tstepMCF_stepTKA_zfN` with `FootBP g E' th r` on the witness.** -/
theorem tstepMCF_stepTKA_zfNB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hpx : PAx g mem pairs th) (hC : PromCrK (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    {Ok : Memory × List Ts × TTh → Prop}
    (hpo : OwnFrOp (CE η) cx th → ∀ lab c, (CE η).sto lab = some c → c.owner = some (CE η).tid →
      (CE η).pfr lab ≠ none → OpTgt th lab → PlantOp g mem pairs th (CE η) cr Ok lab c)
    (hni : OpNI cx th)
    (hclo : ∀ lab c, (CE η).sto lab = some c → Clo c.ty)
    (hbi : ∀ x b i v e, th.term = .let_ x (.bufInit b i v) e →
      (∀ rt w ad rti wi n, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 →
        evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → (CE η).pfr ad.label ≠ none →
        (CE η).rc ad.label ≤ n → n < (CE η).ini ad.label) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∀ o, PredU (CE η) ⟨ad.label, o⟩ → ∃ h, FirstW (stOf mem pairs th).mem ⟨ad.label, o⟩ h ∧
        h ∈ (stOf mem pairs th).promises ∧ ∀ t m, t ∈ (stOf mem pairs th).promises →
          (stOf mem pairs th).mem[t]? = some m → m.loc = ⟨ad.label, o⟩ →
          (stOf mem pairs th).vs.coh ⟨ad.label, o⟩ < t → h ≤ t) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∃ Sp, MemHeldL (CE η) (stOf mem pairs th) H Sp ∧ SlotPayS (CE η) (stOf mem pairs th) Sp cr db ad.label)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hown1 : PubLe1 th Rf Rs H := by assumption)
    (hz0 : ∀ l, ¬ g.zf l := by exact fun _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      (OwnFrOp (CE η) cx th → r.1 = mem) ∧ Ok r → ∃ Tot H' C F cr' db' Gd plh,
      ThInvMCFQK (fun E' => BiOut th E' ∧ KeepQRS (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' plh ∧
          IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
            (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ FootNCE (CE η) E' r ∧ FootBP g E' th r)
        p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
      MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) +
          pSum (stOf r.1 r.2.1 r.2.2) plh ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) := by
  have h := tstepMCF_stepTKA_zfNBC (hDy := hDy) (KP := fun r E' cr' plh =>
      KeepQRS (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' plh) (hz0 := hz0) (hPb := hPb) (Ok := Ok)
    hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia hdw hwp hwin hfo hrmw hbf hbi hPS hSub hSig hTy hRP hown1
    (fun _ _ _ _ _ hK => hK)
    (fun _ _ => tstepMCF_stepTKA_zf (hDy := hDy) (hz0 := hz0) (hPb := hPb) (Ok := Ok) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia
      hdw hwp hwin hfo hrmw hbf hpo hni hclo hbi hRP hPS hSub hSig hTy hown1)
  refine ⟨h.1, fun r hr hpa hok => ?_⟩
  obtain ⟨Tot, H', C, F, cr', db', Gd, plh, hQ, hR2⟩ := h.2 r hr hpa hok
  exact ⟨Tot, H', C, F, cr', db', Gd, plh, hQ, hR2.1, hR2.2.1, hR2.2.2.1, hR2.2.2.2.1, hR2.2.2.2.2.1⟩

#print axioms mcfs_addFootB
#print axioms mc_liftSNB
#print axioms addB1
#print axioms tstepMR_publishB
#print axioms tstepMC_publishPB
#print axioms tstepMCF_stepKAB
#print axioms tstepMCF_stepTKA_zfNB

end TermFootBPK
