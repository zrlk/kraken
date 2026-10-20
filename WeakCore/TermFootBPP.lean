import WeakCore.TermFootBP0

/-! # TermFootBPP (FootBP): the sto-keeping producers with clause (1) of `FootBP` on the witness

Copies of the `TermFootNP` producers whose witness predicate `StoEq (CE η)` becomes
`QB (CE η) g n th.env r` (`StoEq` and `FootB1`): a fresh label named by a counted word of the
result environment's new binding is the new box.  Proofs verbatim but for the inserted `FootB1`
proof (`case_armNBRNB` takes the projection's count `hn1`).
-/

namespace TermFootBPP
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPlant TermFootNC
  TermFootNP TermFootBP0
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (FootBP) `liftMRN` with `QB` (clause (1)) on the witness. -/
theorem liftMRNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {η : TEnv} {Rf Rs H : Res}
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs))
    (hs : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H :=
  ⟨h.1, fun r hr => ⟨Rf + Rs, H, ⟨CE η, ⟨fun _ => rfl, footB1_nalloc (Nat.le_of_eq (hs r hr).2.2.2.2)⟩, EFoot_refl, (by seenT), (by boxT), h.2 r hr, MemInv_same hm (hs r hr),
    MemHeldK_eqs hH (hs r hr).1 (hs r hr).2.2.2.1,
    CrKeep_eqs (hs r hr).1 (hs r hr).2.2.2.1⟩, Res.le_refl _⟩⟩

/-- (FootBP) `tstepMR_inlBN` with `QB` (clause (1)) on the witness. -/
theorem tstepMR_inlBNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs H : Res} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hv : VRR ρ η t (shp rt) ws R) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  have hj : j < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  have harmS : (armsOf (.sum rt (close th.σs τ)))[j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed (.sum rt (close th.σs τ)) = true := by simp [isBoxed, sumHead, hS]
  have hRa : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hstoL : η.sto lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).1
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num j) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum rt (close th.σs τ), [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  rw [key]
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := lbl) (us := .one :: us)
      (ws := cst (.num j) :: p0) (s := s) (by simp [nWords, Acc.size] at hnw ⊢; omega)
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    let B : Box := ⟨j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
    have hHb := MemHeldL_box hm hH hal B
    obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm hn hbf hal hnw.symm
    simp only at hpw hHb
    subst hpw
    obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
    have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
    have eqw : VEq ws q' := eq1.symm.trans eq'.vals
    have hv2 : VRR ρ η'.unsee t (shp rt) q' R :=
      VRR_ext hE.2.1.unsee hE.2.2.unsee (Ext_unsee hx) (VRR_store hE.2.1 hE.2.2 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
        (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VRR_up _ _ _ _ _ hwq hv))
    have hvr : VRR ρ η' (.sum t τ) (shp (.sum rt (close th.σs τ))) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
      VRR_boxL (B := B) hS hRa rfl rfl (by simp [η', TEnv.withSto]) (Or.inl hBS) hj hq' hv2
        (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
        (by show ((armsOf (.sum rt (close th.σs τ)))[j]?).bind wc = some (p0.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hnw, List.length_map])
    have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hvr
      (Lay_box ⟨hshape, hsk, hwc, hval, hly⟩ hS)) (res_swap_le hle)
    refine ⟨Rf + Rs, H, ⟨CE η', ⟨fun _ => rfl, footB1_box rfl (Nat.le_of_eq (nalloc_alloc_boxE hm.2.2.1 hal)) (by simp [η', lbl, s, TEnv.withSto, CE, stOf])⟩, by rw [hCE]; exact EFoot_seeBox (nalloc_alloc_box hm.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)), (by seenT), (by rw [hCE]; refine BoxNewV_seeBox hbnone ?_; intro e0 env0 he hs hev; have hev' := envV_tail he hev; exact payV_lt (TermViewInv.asArm_V has (TermViewInv.evalAt_V hev' hea)) hs.2.2.2.2.2 (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))),
      ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, ?_, ?_, ?_⟩,
      Res.le_refl _⟩
    · rw [hCE]; exact hm'
    · rw [hCE]; exact MemHeldK_of (MemHeldL_seeE (lbl := lbl) (F := s'.vs.vWr) hHb hstoL hpfL)
    · rw [hCE]; exact CrKeep_seeE (lbl := lbl) (F := s'.vs.vWr) (CrKeep_box hm hal B) hstoL

/-- (FootBP) `tstepMR_inrBN` with `QB` (clause (1)) on the witness. -/
theorem tstepMR_inrBNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs H : Res} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hv : VRR ρ η t (shp rt) ws R) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  let τc := close th.σs τ
  let n := (armsOf τc).length
  have harmS : (armsOf (.sum τc rt))[n + j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed (.sum τc rt) = true := by simp [isBoxed, sumHead, τc, hS]
  have hRb : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hstoL : η.sto lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).1
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num (n + j)) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum τc rt, [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box (t := Ty.sum (close th.σs τ) rt) (j := (armsOf (close th.σs τ)).length + j) hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  rw [key]
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := lbl) (us := .one :: us)
      (ws := cst (.num (n + j)) :: p0) (s := s) (by simp [nWords, Acc.size] at hnw ⊢; omega)
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    let B : Box := ⟨n + j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
    have hHb := MemHeldL_box hm hH hal B
    obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm hn hbf hal hnw.symm
    simp only at hpw hHb
    subst hpw
    obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
    have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
    have eqw : VEq ws q' := eq1.symm.trans eq'.vals
    have hv2 : VRR ρ η'.unsee t (shp rt) q' R :=
      VRR_ext hE.2.1.unsee hE.2.2.unsee (Ext_unsee hx) (VRR_store hE.2.1 hE.2.2 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
        (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VRR_up _ _ _ _ _ hwq hv))
    have hvr : VRR ρ η' (.sum τ t) (shp (.sum τc rt)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
      VRR_boxR (B := B) hS hRb rfl rfl (by simp [η', TEnv.withSto]) (Or.inl hBS) (Nat.le_add_right _ _)
        (by show ofArm rt (n + j - n) _ = _; rw [Nat.add_sub_cancel_left]; exact hq') hv2
        (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
        (by show ((armsOf (.sum τc rt))[n + j]?).bind wc = some (p0.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hnw, List.length_map])
    have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hvr
      (TermSound.Lay_boxR ⟨hshape, hsk, hwc, hval, hly⟩ hS)) (res_swap_le hle)
    refine ⟨Rf + Rs, H, ⟨CE η', ⟨fun _ => rfl, footB1_box rfl (Nat.le_of_eq (nalloc_alloc_boxE hm.2.2.1 hal)) (by simp [η', lbl, s, TEnv.withSto, CE, stOf])⟩, by rw [hCE]; exact EFoot_seeBox (nalloc_alloc_box hm.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)), (by seenT), (by rw [hCE]; refine BoxNewV_seeBox hbnone ?_; intro e0 env0 he hs hev; have hev' := envV_tail he hev; exact payV_lt (TermViewInv.asArm_V has (TermViewInv.evalAt_V hev' hea)) hs.2.2.2.2.2 (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))),
      ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, ?_, ?_, ?_⟩,
      Res.le_refl _⟩
    · rw [hCE]; exact hm'
    · rw [hCE]; exact MemHeldK_of (MemHeldL_seeE (lbl := lbl) (F := s'.vs.vWr) hHb hstoL hpfL)
    · rw [hCE]; exact CrKeep_seeE (lbl := lbl) (F := s'.vs.vWr) (CrKeep_box hm hal B) hstoL

/-- (FootBP) `tstepMR_inlBBN` with `QB` (clause (1)) on the witness. -/
theorem tstepMR_inlBBNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs H : Res} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hvV : VR ρ η t (shp rt) ws) (hv : VRR ρ η t (shp rt) ws R)
    (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operand hE.2.1 hbi hrb hsg hvV
  have hj : B0.tag < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  let S := Ty.sum rt (close th.σs τ)
  have harmS : (armsOf S)[B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨hne, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S r1.2.1 r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S r1.2.1 r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num B0.tag) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  unfold PAx at hpx
  rw [key] at hpx
  rw [key]
  refine ⟨?_, ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨r1, h1, hp1⟩ := hne h0
    have hlen : r1.2.2.length = nWords us := by rw [← ((hpr r1 h1).2 hp1).2.1.length, hnw]
    obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch)
      (lbl := freshLabel g.lbase g.n g.i r1.1.nalloc) (us := .one :: us)
      (ws := cst (.num B0.tag) :: r1.2.2) (s := r1.1) (by simp [nWords, Acc.size] at hlen ⊢; omega)
    have hmem : ((injM g r1.1 S r1.2.1 r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1)) ≠ [] := by
      rw [hinj r1 h1 hp1, List.map_map]; exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
    intro hnil; rw [List.flatMap_eq_nil_iff] at hnil; exact hmem (hnil r1 h1)
  · intro r hr hpr0
    rw [List.mem_flatMap] at hr
    obtain ⟨r1, h1, hr⟩ := hr
    have hp1 : PromAbove r1.1 := by
      obtain ⟨f1, f2⟩ := (hpr r1 h1).1
      have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
      have hpa' := hpr0
      obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
      exact injM_pa hpl1 hr2 hpa'
    obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
    rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    obtain ⟨s1, j1, p1⟩ := r1
    simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
    have hm1 : MemInv g (CE η) s1 := MemInv_load hm e1 e2 (LoadCoh_rd hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
    have hH1 : MemHeldL (CE η) s1 H Sp := MemHeldL_eqs hH e1 e4
    have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
    let lbl := freshLabel g.lbase g.n g.i s1.nalloc
    let V := s1.vs.vRelSt
    let B : Box := ⟨B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    have hHb := MemHeldL_box hm1 hH1 hal B
    obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm1 hn hbf hal hlen
    simp only at hpw hHb
    subst hpw
    have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
    have hstoL : η.sto lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).1
    have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2
    have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
    let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
    have hv0 : VRR ρ η' t (vsh 0 (shp rt)) [w] R := by rw [vsh_zero rt hrb]; exact VRR_ext hE.2.1 hE.2.2 hx hv
    have hv1 : VRR ρ η' t (vsh 0 (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
      VRR_ren (B1 := B0) (B2 := B) hx.1 hcr' hw rfl rfl
        (by simp [η', TEnv.withSto, hne0, hB0]) (by simp [η', TEnv.withSto])
        (by simpa [η', TEnv.withSto] using hsto0)
        (by simp [η', TEnv.withSto, hini0]) rfl (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
        (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
        (by simp [η', TEnv.withSto, hini0])
    have hvr : VRR ρ η' (.sum t τ) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
      VRR_boxLB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withSto]) (Or.inl hBS) hj hv1
        (by show ((armsOf S)[B0.tag]?).bind wc = some (p1.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hlen, List.length_map])
    have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hvr
      (Lay_box hl hS)) (res_swap_le hle)
    refine ⟨Rf + Rs, H, ⟨CE η', ⟨fun _ => rfl, footB1_box rfl (Nat.le_of_eq ((nalloc_alloc_boxE hm1.2.2.1 hal).trans (by rw [e5]))) (by simp [η', lbl, s, TEnv.withSto, CE, stOf, e5])⟩, EFoot_congr (s1 := s1) (by rw [hCE]; exact EFoot_seeBox (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))) e5 e7 (congrArg Array.size e1) e4 e1, (by seenT), (by rw [hCE]; refine BoxNewV_seeBox hbnone ?_; intro e0 env0 he hs hev; have hev' := envV_tail he hev; obtain ⟨hp1, hV1⟩ := pV_of_proj h1 hea hs hev'; exact payV_lt hp1 hV1 (alloc_size_len _ hal hlen)),
      ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, ?_, ?_, ?_⟩,
      Res.le_refl _⟩
    · rw [hCE]; exact hm'
    · rw [hCE]; exact MemHeldK_of (MemHeldL_seeE (lbl := lbl) (F := s'.vs.vWr) hHb hstoL hpfL)
    · rw [hCE]; exact CrKeep_trans (CrKeep_eqs e1 e4) (CrKeep_seeE (lbl := lbl) (F := s'.vs.vWr) (CrKeep_box hm1 hal B) hstoL)

/-- (FootBP) `tstepMR_inrBBN` with `QB` (clause (1)) on the witness. -/
theorem tstepMR_inrBBNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs H : Res} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hvV : VR ρ η t (shp rt) ws) (hv : VRR ρ η t (shp rt) ws R)
    (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operand hE.2.1 hbi hrb hsg hvV
  have hj : B0.tag < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  let n := (armsOf (close th.σs τ)).length
  let S := Ty.sum (close th.σs τ) rt
  have harmS : (armsOf S)[n + B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨hne, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S (n + r1.2.1) r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S (n + r1.2.1) r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num (n + B0.tag)) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  unfold PAx at hpx
  rw [key] at hpx
  rw [key]
  refine ⟨?_, ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨r1, h1, hp1⟩ := hne h0
    have hlen : r1.2.2.length = nWords us := by rw [← ((hpr r1 h1).2 hp1).2.1.length, hnw]
    obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch)
      (lbl := freshLabel g.lbase g.n g.i r1.1.nalloc) (us := .one :: us)
      (ws := cst (.num (n + B0.tag)) :: r1.2.2) (s := r1.1) (by simp [nWords, Acc.size] at hlen ⊢; omega)
    have hmem : ((injM g r1.1 S (n + r1.2.1) r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1)) ≠ [] := by
      rw [hinj r1 h1 hp1, List.map_map]; exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
    intro hnil; rw [List.flatMap_eq_nil_iff] at hnil; exact hmem (hnil r1 h1)
  · intro r hr hpr0
    rw [List.mem_flatMap] at hr
    obtain ⟨r1, h1, hr⟩ := hr
    have hp1 : PromAbove r1.1 := by
      obtain ⟨f1, f2⟩ := (hpr r1 h1).1
      have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
      have hpa' := hpr0
      obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
      exact injM_pa hpl1 hr2 hpa'
    obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
    rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    obtain ⟨s1, j1, p1⟩ := r1
    simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
    have hm1 : MemInv g (CE η) s1 := MemInv_load hm e1 e2 (LoadCoh_rd hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
    have hH1 : MemHeldL (CE η) s1 H Sp := MemHeldL_eqs hH e1 e4
    have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
    let lbl := freshLabel g.lbase g.n g.i s1.nalloc
    let V := s1.vs.vRelSt
    let B : Box := ⟨n + B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    have hHb := MemHeldL_box hm1 hH1 hal B
    obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm1 hn hbf hal hlen
    simp only at hpw hHb
    subst hpw
    have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
    have hstoL : η.sto lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).1
    have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2
    have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
    let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
    have hv0 : VRR ρ η' t (vsh 0 (shp rt)) [w] R := by rw [vsh_zero rt hrb]; exact VRR_ext hE.2.1 hE.2.2 hx hv
    have hv1 : VRR ρ η' t (vsh n (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
      VRR_ren (B1 := B0) (B2 := B) hx.1 hcr' hw rfl rfl
        (by simp [η', TEnv.withSto, hne0, hB0]) (by simp [η', TEnv.withSto])
        (by simpa [η', TEnv.withSto] using hsto0)
        (by simp [η', TEnv.withSto, hini0]) (show B0.tag + n = (n + B0.tag) + 0 by omega) (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
        (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
        (by simp [η', TEnv.withSto, hini0])
    have hvr : VRR ρ η' (.sum τ t) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
      VRR_boxRB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withSto]) (Or.inl hBS) (Nat.le_add_right _ _) hv1
        (by show ((armsOf S)[n + B0.tag]?).bind wc = some (p1.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hlen, List.length_map])
    have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hvr
      (TermSound.Lay_boxR hl hS)) (res_swap_le hle)
    refine ⟨Rf + Rs, H, ⟨CE η', ⟨fun _ => rfl, footB1_box rfl (Nat.le_of_eq ((nalloc_alloc_boxE hm1.2.2.1 hal).trans (by rw [e5]))) (by simp [η', lbl, s, TEnv.withSto, CE, stOf, e5])⟩, EFoot_congr (s1 := s1) (by rw [hCE]; exact EFoot_seeBox (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))) e5 e7 (congrArg Array.size e1) e4 e1, (by seenT), (by rw [hCE]; refine BoxNewV_seeBox hbnone ?_; intro e0 env0 he hs hev; have hev' := envV_tail he hev; obtain ⟨hp1, hV1⟩ := pV_of_proj h1 hea hs hev'; exact payV_lt hp1 hV1 (alloc_size_len _ hal hlen)),
      ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, ?_, ?_, ?_⟩,
      Res.le_refl _⟩
    · rw [hCE]; exact hm'
    · rw [hCE]; exact MemHeldK_of (MemHeldL_seeE (lbl := lbl) (F := s'.vs.vWr) hHb hstoL hpfL)
    · rw [hCE]; exact CrKeep_trans (CrKeep_eqs e1 e4) (CrKeep_seeE (lbl := lbl) (F := s'.vs.vWr) (CrKeep_box hm1 hal B) hstoL)

/-- (FootBP) `case_armNBRN` with `QB` (clause (1)) on the witness. -/
theorem case_armNBRNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 q1 : List Word} {R Rr Rf Rs H : Res}
    (hb : c₁.bind xv u = .ok c') (he : TypedK p η c' e') (htv : TvOK c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf) (hE : EnvOK p η)
    (hm1 : MemInv g (CE η) s1) (hH1 : MemHeldL (CE η) s1 H Sp) {S0 : St}
    (hk1 : CrKeep (CE η) (CE η) S0 s1) (hn1 : s1.nalloc = S0.nalloc)
    (hty : isBoxed ty = false) (hq : ofArm ty j p1 = some q1) (hlay : Lay th.σs u ty q1)
    (hvr : VRR ρ η u (shp ty) q1 R) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    injM g s1 ty j p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ty j p1, ∃ Tot H',
      ThInvMKQ (QB (CE η) g S0.nalloc th.env r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1)) p g (CE η) S0 Sp r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) Tot H' ∧
      Tot + H' ≤ Rf + Rs + H := by
  rw [injM_nbB hty, hq]
  refine ⟨by simp [ol], fun r2 hr2 => ?_⟩
  simp [ol] at hr2; subst hr2
  have hf := FInvR_mono (bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvr hlay) (res_swap_le hle)
  exact ⟨Rf + Rs, H, ⟨CE η, ⟨fun _ => rfl, footB1_nalloc (Nat.le_of_eq hn1)⟩, EFoot_refl, (by seenT), (by boxT), ⟨ρ, η, c', Rf, Rs, rfl, hE, he, htv, by simpa [withS] using hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, hm1, MemHeldK_of hH1, hk1⟩,
    Res.le_refl _⟩

/-- (FootBP) `case_armBRN` with `QB` (clause (1)) on the witness. -/
theorem case_armBRNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 : List Word} {us : List Acc} {w : Word}
    {x0 : Address} {B0 : Box} {s0 : Nat} {R Rr Rf Rs H : Res}
    (hb : c₁.bind xv u = .ok c') (he : TypedK p η c' e') (htv : TvOK c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf) (hE : EnvOK p η)
    (hm1 : MemInv g (CE η) s1) (hH1 : MemHeldL (CE η) s1 H Sp)
    {S0 : St}
    (hk1 : CrKeep (CE η) (CE η) S0 s1) (hn1 : s1.nalloc = S0.nalloc)
    (hn : 0 < g.n) (hbf : g.boxFence = true) (hty : isBoxed ty = true) (hus : (armsOf ty)[j]?.bind accs = some us)
    (hlen : p1.length = nWords us) (hw : w.val = .loc x0 0) (hB0 : η.box x0.label = some B0)
    (hsto0 : η.sto x0.label = none) (hini0 : η.ini x0.label = 0) (ht : B0.tag = j + s0)
    (hWp : WLe B0.pay p1) (hv : VRR ρ η u (vsh s0 (shp ty)) [w] R) (hlay : ∀ pw, Lay th.σs u ty [pw])
    (hpV : TermViewInv.StV S0 → TermViewInv.EnvV S0.mem.size th.env →
      TermViewInv.WsV s1.mem.size p1 ∧ s1.vs.vRelSt ≤ s1.mem.size) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    injM g s1 ty j p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ty j p1, ∃ Tot H',
      ThInvMKQ (QB (CE η) g S0.nalloc th.env r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1)) p g (CE η) S0 Sp r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) Tot H' ∧
      Tot + H' ≤ Rf + Rs + H := by
  rw [injM_box hty hus]
  refine ⟨?_, fun r2 hr2 => ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch)
      (lbl := freshLabel g.lbase g.n g.i s1.nalloc) (us := .one :: us)
      (ws := cst (.num j) :: p1) (s := s1) (by simp [nWords, Acc.size] at hlen ⊢; omega)
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · rw [List.mem_map] at hr2
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr2
    let lbl := freshLabel g.lbase g.n g.i s1.nalloc
    let V := s1.vs.vRelSt
    let B : Box := ⟨j, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    have hHb := MemHeldL_box hm1 hH1 hal B
    obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm1 hn hbf hal hlen
    simp only at hpw hHb
    subst hpw
    have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
    have hstoL : η.sto lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).1
    have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2
    have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
    let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
    have hv0 : VRR ρ η' u (vsh s0 (shp ty)) [w] R := VRR_ext hE.2.1 hE.2.2 hx hv
    have hv1 : VRR ρ η' u (vsh 0 (shp ty)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
      VRR_ren (B1 := B0) (B2 := B) hx.1 hcr' hw rfl rfl
        (by simp [η', TEnv.withSto, hne0, hB0]) (by simp [η', TEnv.withSto])
        (by simpa [η', TEnv.withSto] using hsto0)
        (by simp [η', TEnv.withSto, hini0]) (by show B0.tag + 0 = j + s0; omega)
        (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS) (bh_shp ty hty) hv0
        (by simp [η', TEnv.withSto, hini0])
    rw [vsh_zero ty hty] at hv1
    have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hv1 (hlay _))
      (res_swap_le hle)
    refine ⟨Rf + Rs, H, ⟨CE η', ⟨fun _ => rfl, footB1_box rfl (Nat.le_of_eq ((nalloc_alloc_boxE hm1.2.2.1 hal).trans (by rw [hn1]))) (by simp [η', lbl, TEnv.withSto, CE, hn1])⟩, by
        rw [hCE]
        show EFoot g (CE η) (seeBoxE (CE η) (freshLabel g.lbase g.n g.i s1.nalloc) B s'.vs.vWr) S0 _
        rw [hn1]
        exact EFoot_seeBox (by rw [← hn1]; exact nalloc_alloc_box hm1.2.2.1 hal) rfl (by rw [← hn1]; exact hpfL)
          (by rw [← hn1]; exact hstoL) (Nat.le_trans hk1.2.1 (alloc_size_fr hal)) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (Nat.le_trans (Nat.add_le_add_right hk1.2.1 _) (alloc_size_len _ hal hlen)), (by seenT), (by rw [hCE]; refine BoxNewV_seeBox hbnone ?_; intro e0 env0 he hs hev; have hev' := envV_tail he hev; obtain ⟨hp1, hV1⟩ := hpV hs hev'; exact payV_lt hp1 hV1 (alloc_size_len _ hal hlen)),
      ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he, htv,
      by simpa [withS] using hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, ?_, ?_, ?_⟩, Res.le_refl _⟩
    · rw [hCE]; exact hm'
    · rw [hCE]; exact MemHeldK_of (MemHeldL_seeE (lbl := lbl) (F := s'.vs.vWr) hHb hstoL hpfL)
    · rw [hCE]; exact CrKeep_trans hk1 (CrKeep_seeE (lbl := lbl) (F := s'.vs.vWr) (CrKeep_box hm1 hal B) hstoL)

section
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}

/-- (FootBP) `tstepMR_inlTN` with `QB` (clause (1)) on the witness. -/
theorem tstepMR_inlTNB {Sp : AllocLabel → List Res} {x : String} {τ : Ty} {a : At} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  have hT0 := hT
  have hCkL := hCk
  rw [hterm] at hT0 hCkL
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
    have htv' := OpT_TvOK hP hop htv
    cases hop with
    | inl _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum t τ) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useR hu hi hE.2.2
      have hsk : (Ty.sum rt (close th.σs τ)).tier = (close th.σs (.sum _ τ)).tier :=
        tier_of_eskel (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum t τ) = .ok c'' → TypedK p η c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨⟨he, hck⟩, htv'⟩
      by_cases hS : (Ty.sum rt (close th.σs τ)).tier = .boxed
      · cases hrb : isBoxed rt with
        | false => exact paW <| tstepMR_inlBNB (hbf := hbf) hterm hn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hE hm hH (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu htv).2.1
            exact tstepMR_inlBBNB (hbf := hbf) hterm hn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hi.1.2.2.2.1 hi.1.2.2.2.2.1 ho htb hl) hE hm hH hpx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
      · refine paW <| liftMRNB hm hH (tstep_inlR hterm hP (fun t' c₁' hu' => ?_) hT hCk hi hE htv hRP hPS)
          (same_inl hterm fun t0 ws0 hea0 => ?_)
        · rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
          rw [← hsk]; exact hS
        · rw [hea, Option.some.injEq, Prod.mk.injEq] at hea0; obtain ⟨rfl, rfl⟩ := hea0
          exact hS

/-- (FootBP) `tstepMR_inrTN` with `QB` (clause (1)) on the witness. -/
theorem tstepMR_inrTNB {Sp : AllocLabel → List Res} {x : String} {τ : Ty} {a : At} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  have hT0 := hT
  have hCkL := hCk
  rw [hterm] at hT0 hCkL
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
    have htv' := OpT_TvOK hP hop htv
    cases hop with
    | inr _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum τ t) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useR hu hi hE.2.2
      have hsk : (Ty.sum (close th.σs τ) rt).tier = (close th.σs (.sum τ _)).tier :=
        tier_of_eskel (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum τ t) = .ok c'' → TypedK p η c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨⟨he, hck⟩, htv'⟩
      by_cases hS : (Ty.sum (close th.σs τ) rt).tier = .boxed
      · cases hrb : isBoxed rt with
        | false => exact paW <| tstepMR_inrBNB (hbf := hbf) hterm hn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hE hm hH (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu htv).2.1
            exact tstepMR_inrBBNB (hbf := hbf) hterm hn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hi.1.2.2.2.1 hi.1.2.2.2.2.1 ho htb hl) hE hm hH hpx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
      · refine paW <| liftMRNB hm hH (tstep_inrR hterm hP (fun t' c₁' hu' => ?_) hT hCk hi hE htv hRP hPS)
          (same_inr hterm fun t0 ws0 hea0 => ?_)
        · rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
          rw [← hsk]; exact hS
        · rw [hea, Option.some.injEq, Prod.mk.injEq] at hea0; obtain ⟨rfl, rfl⟩ := hea0
          exact hS

end

/-- (FootBP) `tstepMR_caseBN` with `QB` (clause (1)) on the witness. -/
theorem tstepMR_caseBNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr} {u v : Ty} {c₁ c₂ c₃ : Cx}
    {ra rb : Ty} {ws : List Word} {R Rr Rf Rs H : Res} (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hb1 : c₁.bind x u = .ok c₂) (he1 : TypedK p η c₂ e₁) (htv1 : TvOK c₂)
    (hb2 : c₁.bind y v = .ok c₃) (he2 : TypedK p η c₃ e₂) (htv2 : TvOK c₃)
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (.sum ra rb, ws)) (hvV : VR ρ η (.sum u v) (shp (.sum ra rb)) ws)
    (hvR : VRR ρ η (.sum u v) (shp (.sum ra rb)) ws R)
    (hl : Lay th.σs (.sum u v) (.sum ra rb) ws) (hS : (Ty.sum ra rb).tier = .boxed)
    (hsg : sig (.sum ra rb) = sig (cl ρ η.wit 0 0 (.sum u v)))
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  have hrb : isBoxed (.sum ra rb) = true := by simp [isBoxed, sumHead, hS]
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operand hE.2.1 hbi hrb hsg hvV
  -- the box clause, at offset 0
  have hv' := hvR
  simp only [VRR, shp] at hv'
  obtain ⟨n0, Ra, Rb, hR, hv'⟩ := hv'
  simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at hR
  obtain ⟨rfl, rfl, rfl⟩ := hR
  have htl : (Ty.sum (lnorm ra) (lnorm rb)).tier = .boxed := by
    rw [← hS]; exact tier_lnorm (.sum ra rb)
  have hv3 := hv'.resolve_right (fun ⟨j, p, hd, _, _⟩ => by rw [htl] at hd; simp [decodeArm] at hd)
  obtain ⟨-, x1, s0, B, hx1, -, hB, hn1, -, -, hA, hB'⟩ := hv3
  rw [wc_boxed hS] at hn1
  have hs0 : s0 = 0 := by simp at hn1; omega
  subst hs0
  simp only [List.map_cons, List.map_nil, hw, List.cons.injEq, and_true] at hx1
  cases hx1
  rw [hB0, Option.some.injEq] at hB
  subst hB
  have la : (armsOf (lnorm ra)).length = (armsOf ra).length := by rw [armsOf_lnorm, List.length_map]
  simp only [Nat.sub_zero, Nat.zero_add, la, isBoxed_lnorm, shp_lnorm] at hA hB'
  -- the summands
  have hsg2 : Ty.sum (sig ra) (sig rb) = Ty.sum (sig (cl ρ η.wit 0 0 u)) (sig (cl ρ η.wit 0 0 v)) := hsg
  simp only [Ty.sum.injEq] at hsg2
  have hs := hl.2.1
  simp only [close, substTs, skel, etok, Ty.sum.injEq] at hs
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨-, -, -, -, hly⟩ := hl
  simp only [close, substTs, lyt, etok, Ty.sum.injEq] at hly
  have layB : ∀ (ty : Ty) (t : Ty), isBoxed ty = true → etok (skel ty) = etok (skel (close th.σs t)) →
      etok (lyt 0 ty) = etok (lyt 0 (close th.σs t)) → ∀ pw, Lay th.σs t ty [pw] := by
    intro ty t hty hk hy pw
    refine ⟨fun us hu => ?_, hk, by rw [wc_isBoxed ty hty]; simp, Valid_boxed ty _ hty, hy⟩
    have h1 := wc_isBoxed ty hty
    simp only [wc, hu, Option.map_some, Option.some.injEq] at h1
    simp [h1]
  let s := stOf mem pairs th
  obtain ⟨hne, hpr⟩ := projM_own (g := g) (s := s) (t := .sum ra rb) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have hlen : ∀ p1 : List Word, WLe B0.pay p1 → p1.length = nWords us := fun p1 h => h.length.symm.trans hnw.symm
  by_cases hj : B0.tag < (armsOf ra).length
  · have hArm : ∀ s1 p1, MemInv g (CE η) s1 → MemHeldL (CE η) s1 H Sp →
        CrKeep (CE η) (CE η) (stOf mem pairs th) s1 → s1.nalloc = (stOf mem pairs th).nalloc → WLe B0.pay p1 →
        (TermViewInv.StV (stOf mem pairs th) → TermViewInv.EnvV (stOf mem pairs th).mem.size th.env →
          TermViewInv.WsV s1.mem.size p1 ∧ s1.vs.vRelSt ≤ s1.mem.size) →
        injM g s1 ra B0.tag p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ra B0.tag p1, ∃ Tot H',
          ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r2.1.mem r2.1.pairs (withS { th with term := e₁, env := (x, ra, r2.2) :: th.env } r2.1)) p g (CE η) (stOf mem pairs th) Sp r2.1.mem r2.1.pairs (withS { th with term := e₁, env := (x, ra, r2.2) :: th.env } r2.1) Tot H' ∧
          Tot + H' ≤ Rf + Rs + H := by
      intro s1 p1 hm1 hH1 hk1 hn1 hWp hpV
      cases hty : isBoxed ra with
      | false =>
          obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hA hj).2 hty
          obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ :=
            case_arm_nbR hE.2.1 hE.2.2 hty hsg2.1 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
          exact case_armNBRNB hb1 he1 htv1 hi1 hle hE hm1 hH1 hk1 hn1 hty hq1 ⟨hs1, hsa, hw1, hv1, hly.1⟩ hvr1 hRP1
      | true =>
          have harmA : (armsOf ra)[B0.tag]? = some arm := by
            rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_left hj]
          exact case_armBRNB (hbf := hbf) (s0 := 0) hb1 he1 htv1 hi1 hle hE hm1 hH1 hk1 hn1 hn hty (by rw [harmA]; exact hus)
            (hlen p1 hWp) hw hB0 hsto0 hini0 (by omega) hWp ((hA hj).1 hty) (layB ra u hty hsa hly.1) hpV hRP1
    simp only [PAx, tstep, hterm, hea] at hpx ⊢
    refine ⟨?_, fun r hr hpr0 => ?_⟩
    · rcases hpx with h0 | ⟨r, hr, -⟩
      rotate_left
      · exact List.ne_nil_of_mem hr
      obtain ⟨r1, h1, hp1⟩ := hne h0
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_load hm e1 e2 (LoadCoh_rd hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      have hH1 := MemHeldL_eqs hH e1 e4
      have hk1 := CrKeep_eqs (E := CE η) (s := s) e1 e4
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1 hH1 hk1
      subst htag
      intro hnil
      rw [List.flatMap_eq_nil_iff] at hnil
      have h2 := hnil _ h1
      simp only [hj, ite_true, List.map_eq_nil_iff] at h2
      exact (hArm s1 p1 hm1 hH1 hk1 e5 hWp (pV_of_proj h1 hea)).1 h2
    · rw [List.mem_flatMap] at hr
      obtain ⟨r1, h1, hr⟩ := hr
      have hp1 : PromAbove r1.1 := by
        obtain ⟨f1, f2⟩ := (hpr r1 h1).1
        have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
        have hpa' := hpr0
        try simp only at hr
        split at hr
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_load hm e1 e2 (LoadCoh_rd hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      have hH1 := MemHeldL_eqs hH e1 e4
      have hk1 := CrKeep_eqs (E := CE η) (s := s) e1 e4
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1 hH1 hk1
      subst htag
      simp only [hj, ite_true, List.mem_map] at hr
      obtain ⟨r2, hr2, rfl⟩ := hr
      exact (hArm s1 p1 hm1 hH1 hk1 e5 hWp (pV_of_proj h1 hea)).2 r2 hr2
  · have hj' : (armsOf ra).length ≤ B0.tag := by omega
    have hArm : ∀ s1 p1, MemInv g (CE η) s1 → MemHeldL (CE η) s1 H Sp →
        CrKeep (CE η) (CE η) (stOf mem pairs th) s1 → s1.nalloc = (stOf mem pairs th).nalloc → WLe B0.pay p1 →
        (TermViewInv.StV (stOf mem pairs th) → TermViewInv.EnvV (stOf mem pairs th).mem.size th.env →
          TermViewInv.WsV s1.mem.size p1 ∧ s1.vs.vRelSt ≤ s1.mem.size) →
        injM g s1 rb (B0.tag - (armsOf ra).length) p1 ≠ [] ∧
          ∀ r2 ∈ injM g s1 rb (B0.tag - (armsOf ra).length) p1, ∃ Tot H',
          ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r2.1.mem r2.1.pairs (withS { th with term := e₂, env := (y, rb, r2.2) :: th.env } r2.1)) p g (CE η) (stOf mem pairs th) Sp r2.1.mem r2.1.pairs (withS { th with term := e₂, env := (y, rb, r2.2) :: th.env } r2.1) Tot H' ∧
          Tot + H' ≤ Rf + Rs + H := by
      intro s1 p1 hm1 hH1 hk1 hn1 hWp hpV
      cases hty : isBoxed rb with
      | false =>
          obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hB' hj').2 hty
          obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ :=
            case_arm_nbR hE.2.1 hE.2.2 hty hsg2.2 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
          exact case_armNBRNB hb2 he2 htv2 hi1 hle hE hm1 hH1 hk1 hn1 hty hq1 ⟨hs1, hsb, hw1, hv1, hly.2⟩ hvr1 hRP1
      | true =>
          have harmB : (armsOf rb)[B0.tag - (armsOf ra).length]? = some arm := by
            rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_right hj']
          exact case_armBRNB (hbf := hbf) (s0 := (armsOf ra).length) hb2 he2 htv2 hi1 hle hE hm1 hH1 hk1 hn1 hn hty
            (by rw [harmB]; exact hus) (hlen p1 hWp)
            hw hB0 hsto0 hini0 (by omega) hWp ((hB' hj').1 hty) (layB rb v hty hsb hly.2) hpV hRP1
    simp only [PAx, tstep, hterm, hea] at hpx ⊢
    refine ⟨?_, fun r hr hpr0 => ?_⟩
    · rcases hpx with h0 | ⟨r, hr, -⟩
      rotate_left
      · exact List.ne_nil_of_mem hr
      obtain ⟨r1, h1, hp1⟩ := hne h0
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_load hm e1 e2 (LoadCoh_rd hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      have hH1 := MemHeldL_eqs hH e1 e4
      have hk1 := CrKeep_eqs (E := CE η) (s := s) e1 e4
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1 hH1 hk1
      subst htag
      intro hnil
      rw [List.flatMap_eq_nil_iff] at hnil
      have h2 := hnil _ h1
      simp only [hj, ite_false, List.map_eq_nil_iff] at h2
      exact (hArm s1 p1 hm1 hH1 hk1 e5 hWp (pV_of_proj h1 hea)).1 h2
    · rw [List.mem_flatMap] at hr
      obtain ⟨r1, h1, hr⟩ := hr
      have hp1 : PromAbove r1.1 := by
        obtain ⟨f1, f2⟩ := (hpr r1 h1).1
        have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
        have hpa' := hpr0
        try simp only at hr
        split at hr
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_load hm e1 e2 (LoadCoh_rd hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      have hH1 := MemHeldL_eqs hH e1 e4
      have hk1 := CrKeep_eqs (E := CE η) (s := s) e1 e4
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1 hH1 hk1
      subst htag
      simp only [hj, ite_false, List.mem_map] at hr
      obtain ⟨r2, hr2, rfl⟩ := hr
      exact (hArm s1 p1 hm1 hH1 hk1 e5 hWp (pV_of_proj h1 hea)).2 r2 hr2

/-- (FootBP) `tstepMR_caseTN` with `QB` (clause (1)) on the witness. -/
theorem tstepMR_caseTNB {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr} {Rf Rs H : Res}
    (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (QB (CE η) g (stOf mem pairs th).nalloc th.env r.1 r.2.1 r.2.2) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  have hT0 := hT
  have hCkC := hCk
  rw [hterm] at hT0 hCkC
  cases hT0 with
  | case hu hb1 he1 hb2 he2 =>
    obtain ⟨u, v, c₁, c₂, c₃, hu, hb1, he1, hb2, he2⟩ : ∃ u v c₁ c₂ c₃,
        cx.use a = .ok (.sum u v, c₁) ∧ c₁.bind x u = .ok c₂ ∧ Typed p c₂ e₁ ∧
        c₁.bind y v = .ok c₃ ∧ Typed p c₃ e₂ := ⟨_, _, _, _, _, hu, hb1, he1, hb2, he2⟩
    have hck12 := TermA4.CkW_case hCkC hu hb1 hb2
    obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useR hu hi hE.2.2
    have hs := hl.2.1
    simp only [close, substTs, skel, etok] at hs
    obtain ⟨ra, rb, rfl, -, -⟩ := eskel_eq_sum hs
    by_cases hS : (Ty.sum ra rb).tier = .boxed
    · have htv12 := case_TvOK hu hb1 hb2 htv
      have ho : cx.opaqueOK _ = true :=
        peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      have htb := (use_TvOK hu htv).2.1
      have hsg := lay_closed (ρ := ρ) hi.1.2.2.2.1 hi.1.2.2.2.2.1 ho htb hl
      exact tstepMR_caseBNB (hbf := hbf) hterm hn hb1 ⟨he1, hck12.1⟩ htv12.1 hb2 ⟨he2, hck12.2⟩ htv12.2 hi1 hle hea hvV hv hl hS hsg hE hm hH hpx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    · have hnb : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs t').tier ≠ .boxed := fun t' c₁' hu' => by
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
        rw [← tier_of_eskel hl.2.1]; exact hS
      refine paW <| liftMRNB hm hH (tstep_caseR hterm hnb hT hCk hi hE htv hRP hPS) ?_
      have hT' := hT
      rw [hterm] at hT'
      obtain ⟨ra', rb', ws', j, p', hea', hS', has, -, -⟩ := case_step hT' hi.1 hnb htv
      obtain ⟨hta, htb⟩ := tier_sum hS'
      intro r hr
      by_cases hj : j < (armsOf ra').length
      · simp only [tstep, hterm, hea', projM_nb hS', has, ol, Option.map_some, Option.toList_some,
          List.flatMap_cons, List.flatMap_nil, hj, ite_true, injM_nb hta, List.append_nil, List.mem_map,
          Option.mem_toList, Option.map_eq_some_iff] at hr
        obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hr
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · simp only [tstep, hterm, hea', projM_nb hS', has, ol, Option.map_some, Option.toList_some,
          List.flatMap_cons, List.flatMap_nil, hj, ite_false, injM_nb htb, List.append_nil, List.mem_map,
          Option.mem_toList, Option.map_eq_some_iff] at hr
        obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hr
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### (P4) Components of a cell, with resources (names suffixed `S`) -/

#print axioms liftMRNB
#print axioms tstepMR_inlBNB
#print axioms tstepMR_inrBNB
#print axioms tstepMR_inlBBNB
#print axioms tstepMR_inrBBNB
#print axioms case_armNBRNB
#print axioms case_armBRNB
#print axioms tstepMR_inlTNB
#print axioms tstepMR_inrTNB
#print axioms tstepMR_caseBNB
#print axioms tstepMR_caseTNB

end TermFootBPP
