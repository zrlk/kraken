import WeakCore.TermC1Rgn

/-! # TermC1RgnR: `region` and `intoRgn` as `publish`, with resources

The resource layer of TermC1Rgn: the step publishes the cell exactly as `tstepMR_publish` does.  The
view change flips the cell's accounting (`MemHeld_pubS`, side condition `hwp : FlipOK`), the credits
move, and the cell's own key leaves the frame (`SeenOK`, from `RgnLe1`).  A `region` also mints the
fresh region's key (`MintStep.fresh`'s `rg + wd`, the bound's `+ F`); an `intoRgn` mints nothing.

New here: `RgnLe1`, the own-key bound at `region` / `intoRgn` (as `PubLe1` at `publish`; both follow
from `OwnLe1`).
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The own-key bound a step needs at `region` and `intoRgn`: of the cell it publishes. -/
def RgnLe1 (th : TTh) (Rf Rs H : Res) : Prop :=
  (∀ a rn pn tn e, th.term = .region a rn pn tn e → ∀ rt ws ad g0, evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad g0] → (Rf + Rs + H) (.own ad.label) ≤ 1) ∧
  (∀ x r a e, th.term = .let_ x (.intoRgn r a) e → ∀ rt ws ad g0, evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad g0] → (Rf + Rs + H) (.own ad.label) ≤ 1)

theorem RgnLe1.of_le1 {th : TTh} {Rf Rs H : Res} (h : OwnLe1 Rf Rs H) : RgnLe1 th Rf Rs H :=
  ⟨fun _ _ _ _ _ _ _ _ ad _ _ _ => h ad.label, fun _ _ _ _ _ _ _ ad _ _ _ => h ad.label⟩

/-- The shared tail of `region` and `intoRgn` on a non-null own cell, with resources:
`pubCellR_post` at `pubEnvAt η lab vWr Rd`, then the frame (`hTh`). -/
theorem pubStepR1 {Sp : AllocLabel → List Res} {p : Prog} {g : G} {η : TEnv} {s : St} {lab : AllocLabel}
    {c : Cell} {Rd : Nat} {Tot H Rf Rs F : Res} {cr db : Ts → Res} {mem' : Memory} {pairs' : List Ts}
    {th' : TTh}
    (hE : EnvOK p η) (hm : MemInv g (CE η) s) (hH : MemHeldL (CE η) s H Sp) (hC : PromCr (CE η) s cr db)
    (hpa : PromAbove s) (hfo : FpOK (CE η) s) (hsto : η.sto lab = some c) (hown : c.owner = some η.tid)
    (hR : η.rid ≤ Rd)
    (hF : (∀ b S, SegOf c.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c.ty = true ∧
      Ty.noOwnIn [] c.ty = true ∧ rgnFree c.ty = true)
    (hnh : NoHold (CE η) s lab) (hgp : g.pf lab) (hwp : FlipOK (CE η) s lab)
    (hT : Tot + Res.one (.own lab) ≤ Rf + Rs + F) (hF0 : F (.own lab) = 0)
    (h1 : (Rf + Rs + H) (.own lab) ≤ 1) (hst : stOf mem' pairs' th' = fenceS s .st)
    (hTh : EnvOK p (pubEnvAt η lab s.vs.vWr Rd) → Ext η (pubEnvAt η lab s.vs.vWr Rd) →
      ThInvRE p (CE (pubEnvAt η lab s.vs.vWr Rd)) th' Tot) :
    ∃ H' cr' db', ThInvMCFS p g (CE η) s Sp mem' pairs' th' Tot H' cr' db' ∧
      Tot + H' + pSum s cr' + pSum s db + Res.one (.own lab) ≤ Rf + Rs + H + pSum s cr + pSum s db' + F := by
  obtain ⟨hx, H', cr', db', hfoot, hseen, hmi, hHn, hCn, hle⟩ :=
    pubCellR_post (Sp := Sp) (Rd := Rd) hE hm hH hC hpa hfo hsto hown hR hF hnh hgp hwp hT hF0 h1
  refine ⟨H', cr', db', ?_, hle⟩
  unfold ThInvMCFS
  rw [hst]
  exact ⟨_, hfoot, hseen, BoxNewV_of_box (fun _ => rfl), hTh ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩ hx, hmi,
    hHn, hCn⟩

section
variable {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
  {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}

/-- **(P4) `region` on an own pointer, with resources**: the step publishes the cell (as
`tstepMR_publish`) and mints the fresh region's key.  The Σ is `pubEnvAt η lab vWr (η.rid + 1)`. -/
theorem tstepMR_region1 {a : At} {rn pn tn : String} {e : Expr}
    (hterm : th.term = .region a rn pn tn e) (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hcpl : ∀ u c₁, (cx.use a = .ok (.ptr .own u, c₁) ∨
      ∃ n k u0, u = .array n u0 ∧ cx.use a = .ok (.refine (.loc .own (.array n u0)) (.ini k), c₁)) →
      Ty.coupledOKIn c₁.ke u = true)
    (hsc : PubScope cx a) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hwp : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      NoHold (CE η) (stOf mem pairs th) ad.label)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hrl : RgnLe1 th Rf Rs H)
    (hPb : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] → g.pf ad.label) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' cr' db' rt ws, evalAt th.env a = some (rt, ws) ∧
        ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + ownW .own ws ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' +
            (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) := by
  have hT0 := hT
  rw [hterm] at hT0 hCk
  obtain ⟨c, hc, hvc, hk, Rr, ws, hle, hcase⟩ :=
    region_stepRT hT0 hCk hi htv (RLink_of hE.2.1 hE.2.2) hE.2.2 (ridNext η)
  have hF0 : ∀ l, (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) (.own l) = 0 := fun l => by
    simp [Res.add_apply, Res.one_apply]
  have hTb : ∀ l, ownW .own ws = Res.one (.own l) →
      Rr + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) + Rs + Res.one (.own l) ≤
        Rf + Rs + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) := fun l hw =>
    Res.le_def.2 fun k => by
      have h1 := Res.le_def.1 hle k
      rw [hw] at h1
      simp only [Res.add_apply] at h1 ⊢; omega
  cases hT0 with
  | regionBuf hu hrc _ _ _ =>
    obtain ⟨hi1, μr, nr, ur, ψ, wsb, hea, hvb, -⟩ := ownBuf_inv hu hi.1
    obtain ⟨μ2, u2, ψ2, hea2, hf⟩ : ∃ μ u ψ, evalAt th.env a = some (.refine (.loc μ u) ψ, ws) ∧
        FInvR (vcons (ridNext η) ρ) η th.σs (ResumeR p th.stack Rs) c
          ((tn, .tok (.lit 0) none, []) :: (pn, .refine (.loc (.rgn (.lit 0)) u) ψ, ws) :: th.env)
          (Rr + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η)))) := by
      rcases hcase with ⟨μ2, u2, hea2, -⟩ | h
      · rw [hea] at hea2; cases hea2
      · exact h
    rw [hea] at hea2
    cases hea2
    simp only [VR] at hvb
    obtain ⟨hv, -⟩ := hvb
    simp only [tstep, hterm, hea]
    refine ⟨by simp, fun r hr hpa0 => ?_⟩
    simp only [List.mem_singleton] at hr
    have hpa : PromAbove (stOf mem pairs th) := by subst hr; exact fun t ht m hm' => hpa0 t ht m hm'
    rcases hv with ⟨hnull, -, -⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, -⟩
    · -- a null handle (an empty buffer): only the fence, as today
      subst hr
      have hxb := Ext_bumpR hE.2.1
      have hb : Rr + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) + Rs + H +
          pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db + ownW .own ws ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db +
            (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) :=
        Res.le_def.2 fun k => by
          have h1 := Res.le_def.1 hle k
          simp only [Res.add_apply] at h1 ⊢; omega
      exact ⟨_, H, cr, db, _, ws, rfl, ⟨CE η, EFoot_refl, (by seenT), (by boxT),
        ⟨_, bumpR η, c, _, Rs, CE_bumpR η, ⟨hE.1, hxb.1, hxb.2.2.2.2.2.2.2.2.2.2.1⟩, hc.ext hxb, hvc,
          FInvR_ext hE.2.1 hE.2.2 hxb (by simpa [withS] using hf), rfl,
          retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_fence hm,
        MemHeldK_eqs hH rfl rfl, PromCr_keep hC rfl (MemInv_promLt hm) (fun _ _ => rfl) (fun _ _ _ _ => rfl)⟩, hb⟩
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBuf hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat
        (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1 (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      obtain ⟨H', cr', db', hI, hb⟩ := pubStepR1 (Sp := Sp) (Rd := η.rid + 1) (mem' := r.1) (pairs' := r.2.1) (th' := r.2.2) hE hm hH hC hpa hfo hsto hown
        (Nat.le_succ _) hF (hwin _ _ ad hea hws) (hPb _ _ ad hea hws) (hwp _ _ ad hea hws)
        (hTb _ (ownW_own_loc hws)) (hF0 _) (hrl.1 _ _ _ _ _ hterm _ _ ad 0 hea hws) (by subst hr; rfl)
        (fun hE' hx => by subst hr; exact ⟨_, _, c, _, Rs, rfl, hE', hc.ext hx, hvc,
          FInvR_ext hE.2.1 hE.2.2 hx (by simpa [withS] using hf), rfl,
          retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩)
      subst hr
      refine ⟨_, H', cr', db', _, ws, rfl, hI, ?_⟩
      rw [ownW_own_loc hws]
      exact hb
  | region hu hrc _ _ _ =>
    obtain ⟨hi1, lab, c0, pw, μr, ru, hea, hpw, hsto, hcty, hown, hacc, -⟩ := ownPtr_inv hu hi.1
    obtain ⟨μ2, u2, hea2, hf⟩ : ∃ μ u, evalAt th.env a = some (.ptr μ u, ws) ∧
        FInvR (vcons (ridNext η) ρ) η th.σs (ResumeR p th.stack Rs) c
          ((tn, .tok (.lit 0) none, []) :: (pn, .ptr (.rgn (.lit 0)) u, ws) :: th.env)
          (Rr + (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η)))) := by
      rcases hcase with h | ⟨μ2, u2, ψ2, hea2, -⟩
      · exact h
      · rw [hea] at hea2; cases hea2
    rw [hea] at hea2
    cases hea2
    have hwsv : [pw].map (·.val) = [.loc ⟨lab, 0⟩ 0] := by simp [hpw]
    have hF := pubTyFacts hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
      (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1)
      (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
    simp only [tstep, hterm, hea]
    refine ⟨by simp, fun r hr hpa0 => ?_⟩
    simp only [List.mem_singleton] at hr
    have hpa : PromAbove (stOf mem pairs th) := by subst hr; exact fun t ht m hm' => hpa0 t ht m hm'
    obtain ⟨H', cr', db', hI, hb⟩ := pubStepR1 (Sp := Sp) (Rd := η.rid + 1) (mem' := r.1) (pairs' := r.2.1) (th' := r.2.2) hE hm hH hC hpa hfo hsto hown
      (Nat.le_succ _) hF (hwin _ _ ⟨lab, 0⟩ hea hwsv) (hPb _ _ ⟨lab, 0⟩ hea hwsv) (hwp _ _ ⟨lab, 0⟩ hea hwsv)
      (hTb _ (ownW_own_loc hwsv)) (hF0 _) (hrl.1 _ _ _ _ _ hterm _ _ ⟨lab, 0⟩ 0 hea hwsv) (by subst hr; rfl)
      (fun hE' hx => by subst hr; exact ⟨_, _, c, _, Rs, rfl, hE', hc.ext hx, hvc,
        FInvR_ext hE.2.1 hE.2.2 hx (by simpa [withS] using hf), rfl,
        retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩)
    subst hr
    refine ⟨_, H', cr', db', _, [pw], rfl, hI, ?_⟩
    rw [ownW_own_loc hwsv]
    exact hb


/-- **(P4) `intoRgn` on an own pointer, with resources**: `tstepMR_publish` with a region result.
The used handle's own key is consumed (the bound's `ownW .own ws`). -/
theorem tstepMR_intoRgn1 {x rn : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.intoRgn rn a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hcpl : ∀ u c₁, (cx.use a = .ok (.ptr .own u, c₁) ∨
      ∃ n k u0, u = .array n u0 ∧ cx.use a = .ok (.refine (.loc .own (.array n u0)) (.ini k), c₁)) →
      Ty.coupledOKIn c₁.ke u = true)
    (hsc : PubScope cx a) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hwp : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      NoHold (CE η) (stOf mem pairs th) ad.label)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hrl : RgnLe1 th Rf Rs H)
    (hPb : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] → g.pf ad.label) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' cr' db' rt ws, evalAt th.env a = some (rt, ws) ∧
        (∀ ad g', ws.map (·.val) = [.loc ad g'] → η.sto ad.label ≠ none) ∧
        ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + ownW .own ws ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  have hTb : ∀ {R0 Rr : Res} (l : AllocLabel), R0 + Rr ≤ Rf → R0 = Res.one (.own l) →
      Rr + Rs + Res.one (.own l) ≤ Rf + Rs + Res.zero := fun l hle h0 =>
    Res.le_def.2 fun k => by
      have h1 := Res.le_def.1 hle k
      rw [h0] at h1
      simp only [Res.add_apply] at h1 ⊢; simp only [Res.zero] at ⊢; omega
  cases hop with
  | intoRgnBuf hr hu hrc hb =>
    rename_i c₁ r n k u
    obtain ⟨rb, wsb, R0, Rr, hea, -, -, hvR, hi1R, hle⟩ := useR hu hi hE.2.2
    have hR0 := VRR_buf_R rfl hvR
    obtain ⟨hi1, μr, nr, ur, ψ, wsb', hea', hvb, hlay⟩ := ownBuf_inv hu hi.1
    rw [hea] at hea'
    cases hea'
    have hl := hlay (.rgn r) (.rgn (.lit 0)) (by simp [skelM]) (by simp [modeC, idxC, ofMs])
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r' hr' hpa0 => ?_⟩
    simp only [List.mem_singleton] at hr'
    have hpa : PromAbove (stOf mem pairs th) := by subst hr'; exact fun t ht m hm' => hpa0 t ht m hm'
    simp only [VR] at hvb
    obtain ⟨hv, hir⟩ := hvb
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, hini⟩
    · -- a null handle (an empty buffer): only the fence
      subst hr'
      have hvz : VRR ρ η (.refine (.loc (.rgn r) (.array n u)) (.ini k))
          (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ)) wsb .zero := by
        simp only [VRR]; exact ⟨⟨Or.inl ⟨hnull, e0, he0⟩, rfl⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      have hfr := bindR hb hi1R (RLink_of hE.2.1 hE.2.2) hvz hl
      rw [Res.add_zero] at hfr
      have hleT : Rr + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db + ownW .own wsb ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem pairs th) db :=
        Res.le_def.2 fun k => by
          have h1 := Res.le_def.1 hle k
          have h3 := congrArg (fun R : Res => R k) hR0
          simp only [Res.add_apply] at h1 h3 ⊢; omega
      exact ⟨Rr + Rs, H, cr, db, _, wsb, hea, (fun ad' g' h => by rw [hnull] at h; cases h),
        ⟨CE η, EFoot_refl, (by seenT), (by boxT), ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl,
          retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_fence hm,
        MemHeldK_eqs hH rfl rfl, PromCr_keep hC rfl (MemInv_promLt hm) (fun _ _ => rfl) (fun _ _ _ _ => rfl)⟩, hleT⟩
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBuf hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat
        (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1 (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      have hvz : VRR ρ (pubEnvAt η ad.label (stOf mem pairs th).vs.vWr η.rid)
          (.refine (.loc (.rgn r) (.array n u)) (.ini k)) (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ))
          wsb .zero := by
        simp only [VRR]
        exact ⟨⟨Or.inr ⟨ad, c0, _, hws, hsto, hat, .refl, trivial, IniAt_mono (modeIni_le_ini _ _ _) hini⟩,
          by simp [ownW]⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      obtain ⟨H', cr', db', hI, hb'⟩ := pubStepR1 (Sp := Sp) (Rd := η.rid) (mem' := r'.1) (pairs' := r'.2.1) (th' := r'.2.2) hE hm hH hC hpa hfo hsto hown
        (Nat.le_refl _) hF (hwin _ _ ad hea hws) (hPb _ _ ad hea hws) (hwp _ _ ad hea hws)
        (hTb _ hle (hR0.trans (ownW_own_loc hws))) rfl (hrl.2 _ _ _ _ hterm _ _ ad 0 hea hws) (by subst hr'; rfl)
        (fun hE' hx => by
          subst hr'
          have hfr := bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1R) (RLink_of hE'.2.1 hE'.2.2) hvz hl
          rw [Res.add_zero] at hfr
          exact ⟨ρ, _, c', Rr, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl,
            retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩)
      subst hr'
      refine ⟨Rr + Rs, H', cr', db', _, wsb, hea, (fun ad' g' h => by rw [hws] at h; cases h; simp [hsto]), hI, ?_⟩
      rw [ownW_own_loc hws]
      rw [Res.add_zero] at hb'
      exact hb'
  | intoRgn hr hu hrc hb =>
    rename_i c₁ r u
    obtain ⟨rt, ws, R0, Rr, hea, -, -, hvR, hi1R, hle⟩ := useR hu hi hE.2.2
    have hR0 := VRR_cell_R rfl hvR
    obtain ⟨hi1, lab, c0, pw, μr, ru, hea', hpw, hsto, hcty, hown, hacc, hl⟩ := ownPtr_inv hu hi.1
    rw [hea] at hea'
    cases hea'
    have hwsv : [pw].map (·.val) = [.loc ⟨lab, 0⟩ 0] := by simp [hpw]
    have hF := pubTyFacts hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
      (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1)
      (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .ptr (.rgn (.lit 0)) ru, [pw]) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r' hr' hpa0 => ?_⟩
    simp only [List.mem_singleton] at hr'
    have hpa : PromAbove (stOf mem pairs th) := by subst hr'; exact fun t ht m hm' => hpa0 t ht m hm'
    have hvz : VRR ρ (pubEnvAt η lab (stOf mem pairs th).vs.vWr η.rid) (.ptr (.rgn r) u)
        (shp (.ptr (.rgn (.lit 0)) ru)) [pw] .zero := by
      simp only [VRR]
      exact ⟨⟨⟨lab, 0⟩, c0, hwsv, rfl, hsto, hcty, trivial, hacc⟩, by simp [ownW]⟩
    have hlay : Lay th.σs (.ptr (.rgn r) u) (.ptr (.rgn (.lit 0)) ru) [pw] :=
      Lay_ptr_remode hl (by simp [skelM]) (by simp [modeC, idxC, ofMs])
    obtain ⟨H', cr', db', hI, hb'⟩ := pubStepR1 (Sp := Sp) (Rd := η.rid) (mem' := r'.1) (pairs' := r'.2.1) (th' := r'.2.2) hE hm hH hC hpa hfo hsto hown
      (Nat.le_refl _) hF (hwin _ _ ⟨lab, 0⟩ hea hwsv) (hPb _ _ ⟨lab, 0⟩ hea hwsv) (hwp _ _ ⟨lab, 0⟩ hea hwsv)
      (hTb _ hle (hR0.trans (ownW_own_loc hwsv))) rfl (hrl.2 _ _ _ _ hterm _ _ ⟨lab, 0⟩ 0 hea hwsv) (by subst hr'; rfl)
      (fun hE' hx => by
        subst hr'
        have hfr := bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1R) (RLink_of hE'.2.1 hE'.2.2) hvz hlay
        rw [Res.add_zero] at hfr
        exact ⟨ρ, _, c', Rr, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl,
          retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩)
    subst hr'
    refine ⟨Rr + Rs, H', cr', db', _, [pw], hea,
      (fun ad g' h => by simp only [List.map_cons, List.map_nil, hpw] at h; cases h; simp [hsto]), hI, ?_⟩
    rw [ownW_own_loc hwsv]
    rw [Res.add_zero] at hb'
    exact hb'


/-- **`region` in the MC form** (as `tstepMC_publishP`): the MR result (`tstepMR_region1`) with the
exchange `MintStep.fresh` (the fresh region's `rg + wd`); the published cell's own key, on the left
of the MR bound, is dropped. -/
theorem tstepMC_region1_of {a : At} {rn pn tn : String} {e : Expr} (hterm : th.term = .region a rn pn tn e)
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' cr' db' rt ws, evalAt th.env a = some (rt, ws) ∧
        ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + ownW .own ws ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' +
            (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η)))) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' C F cr' db', ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F := by
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨Tot, H', cr', db', -, ws, -, hI, hb⟩ := h.2 r hr hpa
  refine ⟨Tot, H', .zero, _, cr', db', hI, .fresh,
    ClaimAtP.of_not (ClaimAt_zero _ _) (fun x a' e' ht => by rw [hterm] at ht; cases ht), ?_⟩
  exact Res.le_def.2 fun k => by
    have h1 := Res.le_def.1 hb k
    simp only [Res.add_apply] at h1 ⊢
    simp only [Res.zero_apply]
    omega

/-- **`intoRgn` in the MC form** (as `tstepMC_publishP`): the MR result (`tstepMR_intoRgn1`) with the
exchange `MintStep.consume` (the cell's own key spent, nothing minted). -/
theorem tstepMC_intoRgn1_of {x rn : String} {a : At} {e : Expr} (hterm : th.term = .let_ x (.intoRgn rn a) e)
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' cr' db' rt ws, evalAt th.env a = some (rt, ws) ∧
        (∀ ad g', ws.map (·.val) = [.loc ad g'] → η.sto ad.label ≠ none) ∧
        ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + ownW .own ws ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db') :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H' C F cr' db', ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
        MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
        Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C ≤
          Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F := by
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨Tot, H', cr', db', -, ws, -, -, hI, hb⟩ := h.2 r hr hpa
  refine ⟨Tot, H', ownW .own ws, .zero, cr', db', hI, .consume .own ws,
    ClaimAtP.of_not ((MintStepN.consume (g := g) (η := η) (s := stOf mem pairs th)
      (s' := stOf r.1 r.2.1 r.2.2) .own ws).claimAt _) (fun x' a' e' ht => by rw [hterm] at ht; cases ht), ?_⟩
  rw [Res.add_zero]
  exact hb

end

end TermC1

#print axioms TermC1.RgnLe1.of_le1
#print axioms TermC1.pubStepR1
#print axioms TermC1.tstepMR_region1
#print axioms TermC1.tstepMR_intoRgn1
#print axioms TermC1.tstepMC_region1_of
#print axioms TermC1.tstepMC_intoRgn1_of
