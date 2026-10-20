import WeakCore.TermFootNC
import WeakCore.TermBNamed

/-! # TermFootNP ((X) FootNC): the allocating producers with `FootNCE` on the witness

New copies of the allocating step lemmas of `TermStep` (`tstepMR_new`, …) whose `ThInvMK` carries
`FootNCE (CE η) E' r` (`ThInvMKQ`); proofs verbatim but for the inserted `FootNCE` proof.
-/

namespace TermFootNP
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPlant TermFootNC
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (`newBuf`) `allocBuf` writes no pointer (the zero names no label) and keeps pairs and promises,
so `LocNC` holds at the fresh label from its messages being own promises before. -/
theorem locNC_allocBuf {lbl : AllocLabel} {T : Ty} {n : Nat} {z : Option (List WeakMem.Val)} {s : St}
    (hz : ∀ zs, z = some zs → ∀ v ∈ zs, TermBNamed.NV (fun _ => False) v)
    (hfresh : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label = lbl → t ∈ s.promises) (hpo : PromOK s)
    (hlt : ∀ t, t ∈ s.pairs → t + 1 < s.mem.size) :
    LocNC lbl T (allocBuf lbl n z s).1.mem (allocBuf lbl n z s).1.pairs (allocBuf lbl n z s).1.promises := by
  have hw := TermBNamed.allocBuf_wrV (L := fun _ => False) lbl n z s hz
  have hg := (allocBuf_grows lbl n z s).1
  refine ⟨fun q hq => Nat.lt_of_lt_of_le (hlt q hq) hg.1, fun q hq m0 h0 hl => ?_,
    fun v mv o hv hP hl ho hT => ?_⟩
  · rw [hg.2.1 q (Nat.lt_of_succ_lt (hlt q hq))] at h0
    exact absurd hq (hpo.2.1 q (hfresh q m0 h0 hl))
  · rcases hw v mv hv hP with ⟨h1, h2⟩ | h1
    · exact absurd (hfresh v mv h1 hl) h2
    · exact Or.inl fun a g h => h1 a g h

/-- `footNC_ofLoc` at `allocE E0` with `E0` keeping `E.sto`. -/
theorem footNC_ofLocS {E E0 : TEnv} {lbl : AllocLabel} {T : Ty} {mem : Memory} {pairs : List Ts} {th' : TTh}
    (hs : ∀ l, E0.sto l = E.sto l) (h : LocNC lbl T mem pairs th'.promises) :
    FootNCE E (allocE E0 lbl T) (mem, pairs, th') := by
  refine ⟨fun q hq m0 cl h0 hc hn => ?_, fun v mv cl o hv hP hc hn ho hT => ?_⟩
  · by_cases hl : m0.loc.label = lbl
    · rw [hl, allocE_eq] at hc; cases hc; exact h.2.1 q hq m0 h0 hl
    · rw [allocE_ne hl, hs, hn] at hc; cases hc
  · by_cases hl : mv.loc.label = lbl
    · rw [hl, allocE_eq] at hc; cases hc; exact h.2.2 v mv o hv hP hl ho hT
    · rw [allocE_ne hl, hs, hn] at hc; cases hc

/-- (X) `tstepMR_new` with `FootNCE` on the witness. -/
theorem tstepMR_newN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.new a) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H', ThInvMKQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧
        FreshIn g (stOf mem pairs th).nalloc (stOf r.1 r.2.1 r.2.2).nalloc (freshLabel g.lbase g.n g.i th.nalloc) ∧
        Tot + H' ≤ Rf + Rs + H + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | new hu _ hb =>
  obtain ⟨tv, c₁, hu, hb⟩ : ∃ tv c₁, cx.use a = .ok (tv, c₁) ∧ c₁.bind x (.ptr .own tv) = .ok c' :=
    ⟨_, _, hu, hb⟩
  have hi0 := hi.1
  obtain ⟨rt, ws, Rv, Rr, hea, hv, hl, hvr, hiR, hle⟩ := useR hu hi hE.2.2
  have ho : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have htb := (use_TvOK hu htv).2.1
  have hsig : sig rt = sig (cl ρ η.wit 0 0 tv) := lay_closed hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb hl
  obtain ⟨us, hus⟩ : ∃ us, accs rt = some us := by
    cases h : accs rt with
    | none => exact absurd (by simp [wc, h]) hl.2.2.1
    | some us => exact ⟨us, rfl⟩
  have hlen : ws.length = nWords us := hl.1 us hus
  have hwcT : wc (cl ρ η.wit 0 0 tv) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvc : VR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 tv) (shp (cl ρ η.wit 0 0 tv)) ws := by
    rw [← shp_of_sig hsig]
    exact (VR_close hE.2.1 ρ tv [] 0 ρ (fun _ => 0) (shp rt) ws (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  have hvcR : VRR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 tv) (shp (cl ρ η.wit 0 0 tv)) ws Rv := by
    rw [← shp_of_sig hsig]
    exact (VRR_close hE.2.1 hE.2.2 ρ tv [] 0 ρ (fun _ => 0) (shp rt) ws Rv (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvr
  obtain ⟨R0, H0, hHe, hent0, hX⟩ := MemHeldL_focusE hH (freshLabel g.lbase g.n g.i th.nalloc)
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  obtain ⟨hnone, hfresh, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hR0 : R0 = .zero := hent0.1 hnone
  have hval : ValOf (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) (cl ρ η.wit 0 0 tv)
      (ws.map (bumpW (stOf mem pairs th).vs.vRelSt)) :=
    ValOf_mono (η₁ := CE η) (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      rfl rfl (fun l c h => allocE_sub hnone h) (fun _ => Nat.le_refl _)
      (EnvVal.store (η := CE η) ⟨hvc, Valid_of_sig hsig hl.2.2.2.1⟩ hsn)
  have hvalR : ValOfR (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      (cl ρ η.wit 0 0 tv) (ws.map (bumpW (stOf mem pairs th).vs.vRelSt)) Rv :=
    ValOfR_mono (η₁ := CE η) (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      rfl rfl (fun l c h => allocE_sub hnone h) (fun _ => Nat.le_refl _)
      (EnvValR.store (η := CE η) ⟨hvcR, Valid_of_sig hsig hl.2.2.2.1⟩ hsn)
  have hx : Ext η (η.withSto (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto) :=
    Ext_withSto hE.2.1 (fun l c h => allocE_sub (η := CE η) hnone h) (fun _ => Nat.le_refl _)
  have key : tstep g mem pairs th =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i th.nalloc) us ws (stOf mem pairs th)).map fun (s', pw) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .ptr .own rt, [pw]) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hus, List.map_map]; rfl
  rw [key]
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := freshLabel g.lbase g.n g.i th.nalloc)
      (s := stOf mem pairs th) hlen
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    obtain ⟨hmo', hoo', hpw⟩ := alloc_okP hwcT hlen hval hfresh hnone hpl hpo.1 hpo.2.1 hpf0 hmo hoo ⟨s', pw⟩ hal
    obtain ⟨hg, hsubl, hna, hpl', hful⟩ := alloc_growsP hpl ⟨s', pw⟩ hal
    obtain ⟨hla1, -⟩ := alloc_latP (k := g.k) (arch := g.arch) (us := us) (ws := ws) hpl (MemInv_nodup hm)
      ⟨s', pw⟩ hal
    obtain ⟨hwr, hhid⟩ := alloc_hidP (s := stOf mem pairs th) hval
      (ShapeC_of_wc hwcT (by rw [List.length_map]; exact hlen))
      (by obtain ⟨_, h, -⟩ := wc_some hwcT; simp [h]) hfresh hpl ⟨s', pw⟩ hal
    simp only at hmo' hoo' hpw hg hsubl hna hwr hhid hla1 hpl' hful
    subst hpw
    have hwA : ∀ T o w, WordOK (CE η) T o w →
        WordOK (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) T o w :=
      fun T o w h => WordOK_mono (η₁ := CE η)
        (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
        rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _)
        (fun _ _ h' => h') (fun _ h' => h') h
    have hoh' : OwnHidP (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem s'.vs
        s'.promises := by
      refine ⟨fun l c hc ho o hi => ?_, fun l c hc ho hlt => ?_⟩
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          rw [allocE_eq] at hc; cases hc; exact hhid o
        · rw [allocE_ne hl] at hc
          exact HiddenP_growsAt (hoh.1 l c hc ho o hi) (hwA _ _) hwr hg hl hful
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
            (Nat.not_lt_zero _)
        · rw [allocE_ne hl] at hc
          obtain ⟨f, hf, hs, hH⟩ := hoh.2 l c hc ho hlt
          exact ⟨f, hf, fun hz => hs (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
            fun o hi => HiddenP_growsAt (hH o hi) (hwA _ _) (Nat.le_refl _) hg hl hful⟩
    have hpd' : PubDefP (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem
        s'.promises := by
      intro l c f hc hown hf o hi
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at hc; cases hc; exact (hown rfl).elim
      · rw [allocE_ne hl] at hc
        exact HiddenP_growsAt (hpd l c f hc hown hf o hi) (hwA _ _) (Nat.le_refl _) hg hl hful
    have hpi' : PubInv (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      refine PubInv_grow (hbs := fun l hb h => by
          by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
          · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
          · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (alloc_pairs _ hal) hful rfl rfl (fun l c h => allocE_sub hnone h)
        (fun _ => Nat.le_refl _) rfl rfl (fun c h => by rw [allocE_eq] at h; rw [← Option.some.inj h]; rfl)
        (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
          (Nat.not_lt_zero _)) (hrcg := fun _ h => ⟨h, Nat.le_refl _⟩)
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl; exact Or.inr hpf0
        · rw [allocE_ne hl] at h; exact Or.inl h
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at h
        cases h
        refine Or.inr ?_
        rcases hseg with ⟨-, rfl, -⟩ | ⟨N, us0, j0, hT, -, -, -⟩
        · obtain ⟨vals, hcell, -⟩ := hoo' _ _ allocE_eq rfl
          rcases hcell with ⟨hwc, hv⟩ | hb
          · exact ⟨vals, hv, Option.some.inj (hwc.symm.trans (wc_of_accs hu'))⟩
          · obtain ⟨N, e0, us0, hT, -⟩ := hb
            exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
        · exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
      · rw [allocE_ne hl] at h; exact Or.inl ⟨h, hini⟩
    have hopub' : OwnPubV (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      intro l c f hc ho hf
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
      · rw [allocE_ne hl] at hc
        exact ((hopub.alloc hpl hal) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
          fun a ha hi c1 N1 e1 us1 h1 => hi c1 N1 e1 us1 (by rw [allocE_ne (fun e => hl (ha.symm.trans e))]; exact h1))
    -- the frame: the value is gone, the own pointer carries nothing
    have hfr' : FInvR ρ (η.withSto (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto)
        th.σs (ResumeR p th.stack Rs) c'
        ((x, .ptr .own rt, [cst (.loc ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩ 0)]) :: th.env) (Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc))) := by
      refine bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hiR) (RLink_of hx.1 hx.2.2.2.2.2.2.2.2.2.2.1) ?_ ?_
      · simp only [VRR]
        exact ⟨⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, ⟨cl ρ η.wit 0 0 tv, some η.tid⟩, by simp [cst, Promises.TVal.mk0], rfl,
          by simp [TEnv.withSto, allocE, CE], .refl, by first | rfl | trivial,
          show accs (cl ρ η.wit 0 0 tv) ≠ none from fun h => by simp [wc, h] at hwcT⟩,
          (ownW_own_loc (a := ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩) (g := 0)
            (by simp [cst, Promises.TVal.mk0])).symm⟩
      · refine ⟨fun us h => by simp [accs] at h; subst h; rfl, ?_, by simp [wc, accs],
          ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, by simp [cst, Promises.TVal.mk0]⟩, ?_⟩
        · show Ty.ptr (skelM .own) (etok (skel rt)) = Ty.ptr _ _
          rw [hl.2.1]; rfl
        · show Ty.ptr (modeC 0 .own) (etok (lyt 0 rt)) = Ty.ptr _ _
          rw [hl.2.2.2.2]; rfl
    -- memory: the new cell holds the value's resources
    have hent : HeldEntry (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'
        (freshLabel g.lbase g.n g.i th.nalloc) Rv := by
      refine HeldEntry_ownP allocE_eq (PromAt_privL (Priv_of allocE_eq rfl hpf0)) (fun o v hov => ?_)
        (Or.inl ⟨by rw [List.length_map, hlen]; exact hwcT, hvalR⟩)
      rw [List.getElem?_map] at hov
      cases hw : ws[o]? with
      | none => rw [hw] at hov; cases hov
      | some w =>
        rw [hw] at hov
        simp only [Option.map_some, Option.some.injEq] at hov
        subst hov
        have ho' : o < ws.length := (List.getElem?_eq_some_iff.1 hw).1
        exact hla1 o w (by rw [← hlen]; exact ho') hw
    have hX' : MemHeldXL (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'
        (freshLabel g.lbase g.n g.i th.nalloc) H0 Sp :=
      MemHeldXL_tr hX (fun l' hl' => allocE_ne hl') (fun _ _ => rfl)
        (fun l' hl' o w h => LatestNP_growsAtF hg (fun t h => hsubl.subset h) hful hl' h)
        (fun h => ValOfR_mono (η₁ := CE η)
          (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _) h)
    refine ⟨Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs, Rv + H0,
      ⟨allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv),
        footNC_alloc hal ((accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb hl.2.2.2.2).symm.trans hus) hfresh hpo
          hmo.2.2 rfl,
        EFoot_fresh rfl rfl rfl rfl (lt_of_eq_succ hna) (fun l => allocE_sto_cases ⟨Clo_cl (fun k => (hE.2.1 k).1) ρ tv,
          mg_cl (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.1.2.2.2.2.2.2.1) tv 0 0 (use_mg hu htv),
          noIallV_cl (WitAF.ni hi.1.2.2.2.2.2.2.1) tv 0 0 (hniA tv _ hu),
          TermA4.CkW_newCell hCk (fun k => (hE.2.1 k).1.1) (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1 htb ho⟩ (alloc_newT hal hwcT) (alloc_undefT hal hwcT) l) (fun _ => .inl rfl)
          (fun _ => ⟨Nat.le_refl _, .inl rfl⟩), (by seenT), (by boxT),
        ⟨ρ, η.withSto (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto, c',
          Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)), Rs, rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨he, hck⟩, htv', hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩, ?_,
        MemHeldK_unfocus hX' hent (fun _ h => h.1 hpf0), CrKeep_alloc hg
          hsubl hful (fun _ hl => allocE_ne hl) hnone
          (Or.inr ⟨⟨_, by simp [allocE]; rfl, rfl⟩, hpf0⟩)⟩,
      ⟨th.nalloc, Nat.le_refl _, by show th.nalloc < s'.nalloc; have : (stOf mem pairs th).nalloc = th.nalloc := rfl; omega, rfl⟩, ?_⟩
    · refine ⟨hmo', hoo', hpl', ⟨fun j hj => ?_, PrivCoh_growsAt hfr.2
          (fun a hu hl => by
            obtain ⟨c, N, e, us, hc, rest⟩ := hu
            exact ⟨c, N, e, us, by rw [allocE_ne hl] at hc; exact hc, rest⟩)
          hoo' hg hful (fun t m _ _ hu hl => by
            obtain ⟨c, N, e, us, hc, -, -, hT, -⟩ := hu
            rw [hl, allocE_eq] at hc; cases hc
            simp only at hT; rw [hT] at hwcT; simp [wc, accs] at hwcT)⟩, ?_, hoh', hpd', hopub', hpi',
        BoxInv_alloc hbi rfl hpl hpo.1 hal rfl rfl (fun _ hl => allocE_ne hl) (fun _ _ => rfl),
        PromOK_alloc hpo hpl hal⟩
      rotate_left 1
      · have e : s'.vs.vRelSt = (stOf mem pairs th).vs.vRelSt := alloc_relSt _ hal
        exact (SeenLE.mono hsn (Nat.le_of_eq e.symm) : SeenLE (CE η) s'.vs.vRelSt)
      · have hj' : th.nalloc ≤ j := by
          have : s'.nalloc ≤ j := hj
          rw [hna] at this; exact Nat.le_of_succ_le this
        obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
        have hne : freshLabel g.lbase g.n g.i j ≠ freshLabel g.lbase g.n g.i th.nalloc := fun h => by
          have := freshLabel_inj_k hn h; subst this
          have : s'.nalloc ≤ th.nalloc := hj
          rw [hna] at this; exact absurd this (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
        refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, f4, f5⟩
        change s'.mem[t]? = some m at ht
        by_cases hlt : t < (stOf mem pairs th).mem.size
        · rw [hg.2.1 t hlt] at ht
          have hp := f2 t m ht hl
          refine (Classical.em _).elim id fun hn' => (?_ : False).elim
          obtain ⟨m', hm', e⟩ := hful t hp hn'
          rw [ht] at hm'; cases hm'
          exact hne (hl.symm.trans e)
        · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
    · rw [hHe, hR0]
      intro k
      have := hle k
      simp only [Res.add_apply, Res.zero_apply] at *
      omega

/-- (X) `tstepMR_newBuf` with `FootNCE` on the witness. -/
theorem tstepMR_newBufN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {n : At} {τ : Ty} {e : Expr}
    {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.newBuf n τ) e) (hniA : noIallV τ = true) (hP : ProgT p)
    (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H', ThInvMKQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧
        FreshIn g (stOf mem pairs th).nalloc (stOf r.1 r.2.1 r.2.2).nalloc (freshLabel g.lbase g.n g.i th.nalloc) ∧
        Tot + H' ≤ Rf + Rs + H + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | newBuf hwf hsc hop haf hint hb =>
  rename_i k
  have hiF := hi.1
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VR hiF.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intS hti hvi)
  have hlay : accs (close th.σs τ) ≠ none := accs_close hwf hiF.2.2.2.2.1 haf hiF.2.2.2.2.2.1.2.2
  obtain ⟨us, hus⟩ : ∃ us, accs (close th.σs τ) = some us := Option.ne_none_iff_exists'.1 hlay
  -- the two renditions of the element type
  have hr : ∀ k, τ.guardT k = false → k < th.σs.length := lt_of_guardT (tb_of_wf τ hwf) hiF.2.2.2.2.1
  have hsig : sig (close th.σs τ) = sig (cl ρ η.wit 0 0 τ) := sig_WitL hiF.2.2.2.1 ρ hop hr
  have hwT : wc (cl ρ η.wit 0 0 τ) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨usT, husT⟩ : ∃ usT, accs (cl ρ η.wit 0 0 τ) = some usT := by
    cases h : accs (cl ρ η.wit 0 0 τ) with
    | none => simp [wc, h] at hwT
    | some usT => exact ⟨usT, rfl⟩
  have hnw : nWords usT = nWords us := by rw [wc_of_accs husT] at hwT; exact Option.some.inj hwT
  have hafT : (cl ρ η.wit 0 0 τ).arrFree = true := arrFree_cl hiF.2.2.2.2.2.2.1.af τ 0 0 haf
  have hafR : (close th.σs τ).arrFree = true := by rw [← arrFree_sig, hsig, arrFree_sig]; exact hafT
  -- the zero
  let z : Option (List WeakMem.Val) := if zeroableIn [] [] (close th.σs τ) = true then zeroWords (close th.σs τ) else none
  have hzv : ∀ zs, z = some zs → ValOf η (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ wc (cl ρ η.wit 0 0 τ) = some zs.length := by
    intro zs h
    simp only [z] at h
    split at h
    · exact zero_valOf hiF.2.2.2.1 (fun k => (hE.2.1 k).1) hiF.2.2.2.2.2.2.1 ρ hop hr haf ‹_› h
    · cases h
  have hstat : zeroableIn [] cx.ke τ = true → z.isSome = true := by
    intro h
    have hR := KindSound.zero_close cx.ke th.σs τ hiF.2.2.2.2.2.1.2.1 h
    obtain ⟨zs, hzs, -⟩ := zp _ _ (Nat.lt_succ_self _) [] [] hafR knone_nil hR
    simp [z, hR, hzs]
  -- the new view
  let K := ev ρ k
  let lbl := freshLabel g.lbase g.n g.i th.nalloc
  let iv : Nat := if z.isSome then K else 0
  let ini' := bumpIni η.ini lbl iv
  let rini' := bumpIni η.rini lbl iv
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  let E0 := CE (η.withSto η.sto ini' (Ri := rini'))
  let T := Ty.array (.lit K) (cl ρ η.wit 0 0 τ)
  let E' := allocE E0 lbl T
  let η' := η.withSto E'.sto ini' (Ri := rini')
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  obtain ⟨hnone, hfresh, hi0, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  obtain ⟨R0, H0, hHe, hent0, hX⟩ := MemHeldL_focusE hH lbl
  have hR0 : R0 = .zero := hent0.1 hnone
  have hnone0 : E0.sto lbl = none := hnone
  have hx : Ext η η' := Ext_withSto hE.2.1 (fun l c h => allocE_sub (η := E0) hnone0 h) (bumpIni_le _ _ _)
    (Ri := rini') (hRi := hri')
  let rtR : Ty := .refine (.loc .own (.array (.lit K) (close th.σs τ))) (.ini (.lit iv))
  let R := allocBuf lbl (K * nWords us) z (stOf mem pairs th)
  have key : tstep g mem pairs th =
      [(R.1.mem, R.1.pairs, withS { th with term := e, env := (x, rtR, [R.2]) :: th.env } R.1)] := by
    simp only [tstep, hterm, evalOp, hei, numOf, hus, Option.bind_eq_bind, Option.bind_some, hwi]; rfl
  rw [key]
  refine ⟨by simp, fun r hr' => ?_⟩
  simp only [List.mem_singleton] at hr'
  subst hr'
  have hpw : R.2 = cst (.loc ⟨lbl, 0⟩ 0) := rfl
  -- memory, at the view with the raised count (the label is fresh)
  have hsub0 : ∀ l c, (CE η).sto l = some c → E0.sto l = some c := fun l c h => h
  have hile0 : ∀ l, (CE η).ini l ≤ E0.ini l := bumpIni_le η.ini lbl iv
  have hmo0 : MemOKP E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).promises :=
    MemOKP_mono hmo rfl rfl hsub0 hile0 (fun t m c h hc => hc)
  have hmono0 : ∀ {U : Ty} {vs : List Word}, ValOf (CE η) U vs → ValOf E0 U vs :=
    fun h => ValOf_mono (η₁ := CE η) (η₂ := E0) rfl rfl hsub0 hile0 h
  have hoo0 : OwnOKPF E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).vs
      (stOf mem pairs th).promises := by
    intro l c hc ho
    have hne : l ≠ lbl := fun h => by rw [h] at hc; rw [hnone0] at hc; cases hc
    exact OwnCellF_env (hoo l c hc ho) hmono0 (bumpIni_other _ _ _ _ hne) rfl hmo.2.2 (bumpIni_other _ _ _ _ hne)
  have hi0' : η.ini lbl = 0 := hi0
  have hini : E0.ini lbl ≤ K := by
    show bumpIni η.ini lbl iv lbl ≤ K
    rw [bumpIni_self, hi0']
    refine Nat.max_le.2 ⟨Nat.zero_le _, ?_⟩
    simp only [iv]; split <;> omega
  have hini0 : 0 < E0.ini lbl → z ≠ none := by
    intro h hz0
    have : E0.ini lbl = 0 := by
      show bumpIni η.ini lbl iv lbl = 0
      rw [bumpIni_self, hi0']; simp [iv, hz0]
    omega
  have hzE : ∀ zs, z = some zs → ValOf E' (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ zs.length = nWords usT :=
    fun zs h => ⟨ValOf_mono (η₁ := η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (hzv zs h).1,
      by have := (hzv zs h).2; rw [hwT] at this; rw [hnw]; exact (Option.some.inj this).symm⟩
  have hab := allocBuf_okP (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
    (s := stOf mem pairs th) (η := E0) husT hzE
    hini hini0 hfresh hnone0 hpl hpo.2.1 hmo0 hoo0 hpf0
  rw [hnw] at hab
  obtain ⟨hmo', hoo', -⟩ := hab
  obtain ⟨hg, hpr, hna⟩ := allocBuf_grows lbl (K * nWords us) z (stOf mem pairs th)
  have hwE : ∀ T o w, WordOK (CE η) T o w → WordOK E' T o w := fun T o w h =>
    WordOK_mono (η₁ := CE η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (fun _ _ h' => h') (fun _ h' => h') h
  have hiniE : ∀ l c o, l ≠ lbl → InitR E' c l o → InitR (CE η) c l o := fun l c o hl hi N1 e1 us1 h1 h2 => by
    have := hi N1 e1 us1 h1 h2
    rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  have hoh' : OwnHidP E' R.1.mem R.1.vs R.1.promises := by
    refine ⟨?_, ?_⟩
    · intro l c hc ho o hi
      by_cases hl : l = lbl
      · rw [hl] at hc hi
        have hcT : c = ⟨T, some η.tid⟩ := by
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at hc; exact (Option.some.inj hc).symm
        subst hcT
        rw [hl]
        unfold HiddenP
        intro t m hP hm hloc hnok
        exfalso
        rcases Option.eq_none_or_eq_some z with hzc | ⟨zs, hzc⟩
        · -- no zero: no slot is initialised
          have h0 : E'.ini lbl = 0 := by
            show bumpIni η.ini lbl iv lbl = 0
            rw [bumpIni_self, hi0']; simp [iv, hzc]
          have := hi K (cl ρ η.wit 0 0 τ) usT rfl husT
          rw [show E'.rc lbl = 0 by have := E'.rc_le_ini lbl; omega, Nat.zero_mul] at this; exact Nat.not_lt_zero _ this
        · -- a zero: no placeholder
          apply hnok
          by_cases hlt : t < (stOf mem pairs th).mem.size
          · rw [hg.2.1 t hlt] at hm
            exact (hP (hfresh t m hm (by rw [hloc]))).elim
          · have hw := allocBuf_newOK (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
              (s := stOf mem pairs th) (η := E0) husT hzE zs hzc t m (by omega) (by rw [hnw]; exact hm)
            rw [hloc] at hw; exact hw
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        exact HiddenP_growsAt (hoh.1 l c hc ho o (fun N1 e1 us1 h1 h2 => by
            have := hi N1 e1 us1 h1 h2; rw [hrc] at this; exact this))
          (hwE _ _) (allocBuf_vWr_le _ _ _ _) hg hl
          (fun t h1 h2 => absurd h1 h2)
    · intro l c hc ho hlt
      by_cases hl : l = lbl
      · exfalso
        have h1 : E'.ini lbl ≤ E'.rini lbl := by
          show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl
          rw [bumpIni_self, bumpIni_self, hi0']; omega
        have h2 : E'.rc lbl = E'.ini lbl := Nat.min_eq_left h1
        rw [hl] at hlt; omega
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        have hie : E'.ini l = (CE η).ini l := bumpIni_other _ _ _ _ hl
        obtain ⟨f, hf, hsn', hH⟩ := hoh.2 l c hc ho (by rw [hrc, hie] at hlt; exact hlt)
        exact ⟨f, hf, fun hz => hsn' (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
          fun o hi => HiddenP_growsAt (hH o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
          (fun t h1 h2 => absurd h1 h2)⟩
  have hpd' : PubDefP E' R.1.mem R.1.promises := by
    intro l c f hc hown hf o hi
    by_cases hl : l = lbl
    · rw [hl] at hc
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at hc; cases hc; exact (hown rfl).elim
    · rw [allocE_ne hl] at hc
      exact HiddenP_growsAt (hpd l c f hc hown hf o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
        (fun t h1 h2 => absurd h1 h2)
  have hopub' : OwnPubV E' R.1 := by
    intro l c f hc ho hf
    by_cases hl : l = lbl
    · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
    · rw [allocE_ne hl] at hc
      exact ((hopub.allocBuf hpl lbl (K * nWords us) z) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
        fun a ha hi c1 N1 e1 us1 h1 h2 h3 => by
          have hne : a.label ≠ lbl := fun e => hl (ha.symm.trans e)
          have := hi c1 N1 e1 us1 (by rw [allocE_ne hne]; exact h1) h2 h3
          rwa [show E'.rc a.label = (CE η).rc a.label from
            TEnv.rc_congr (bumpIni_other _ _ _ _ hne) (bumpIni_other _ _ _ _ hne)] at this)
  have hrcl : E'.rc lbl = E'.ini lbl := Nat.min_eq_left (show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl by
    rw [bumpIni_self, bumpIni_self, hi0']; omega)
  have hpi' : PubInv E' R.1 := by
    refine PubInv_grow (E := CE η) (hbs := fun l hb h => by
        by_cases hl : l = lbl
        · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
        · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (fun _ h => h) (fun t h1 h2 => absurd h1 h2) rfl rfl
      (fun l c h => allocE_sub (η := E0) hnone0 (hsub0 l c h)) hile0 rfl rfl
      (fun c h => by
        have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
        rw [h2] at h; rw [← Option.some.inj h]; rfl)
      (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd hlt (by rw [hrcl]; exact Nat.lt_irrefl _))
      (hrcg := fun l h => by
        by_cases hl : l = lbl
        · rw [hl, hrcl] at h; exact absurd h (Nat.lt_irrefl _)
        · exact ⟨by rwa [TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl),
            show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl] at h,
            Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl)⟩)
      (hfi := fun l c h ho => by
        by_cases hl : l = lbl
        · rw [hl] at h
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at h; rw [← Option.some.inj h] at ho; exact absurd rfl ho
        · exact Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl))
    · by_cases hl : l = lbl
      · exact Or.inr (by rw [hl]; exact hpf0)
      · rw [allocE_ne hl] at h; exact Or.inl h
    by_cases hl : l = lbl
    · rw [hl] at h
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at h; cases h
      refine Or.inr ?_
      rcases hseg with ⟨-, rfl, -⟩ | ⟨N1, us1, j1, hT1, -, -, -⟩
      · simp [T, accs] at hu'
      · have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N1) S := hT1
        simp only [Ty.array.injEq, Idx.lit.injEq] at hT2
        obtain ⟨-, rfl⟩ := hT2
        rw [husT] at hu'; obtain rfl := Option.some.inj hu'
        obtain ⟨-, jb, -, hjb, -⟩ := hini K (cl ρ η.wit 0 0 τ) rfl
        have hpos : 0 < E0.ini lbl := by
          rw [hl] at hjb; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hjb
        obtain ⟨zs, hzs⟩ := Option.ne_none_iff_exists'.1 (hini0 hpos)
        obtain ⟨h1, h2⟩ := hzE zs hzs
        exact ⟨zs.map cst, h1, by rw [List.length_map]; exact h2⟩
    · rw [allocE_ne hl] at h
      refine Or.inl ⟨h, fun N1 e1 h1 => ?_⟩
      have := hini N1 e1 h1
      rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  -- the zero carries nothing
  have hzR : ∀ zs, z = some zs → ValOfR E' (cl ρ η.wit 0 0 τ) (zs.map cst) Res.zero := by
    intro zs h
    simp only [z] at h
    split at h
    · rename_i hR
      have hZ := zrel_WitL hiF.2.2.2.1 (fun k => (hE.2.1 k).1) ρ hop hr
      have hTz := (zrel_zero _ _ [] [] hZ hsig knone_nil).1 hR
      have hwT' := zrel_words _ _ _ [] zs (Nat.lt_succ_self _) hZ hsig h
      obtain ⟨zs', hzw', -, hv⟩ := zpR _ _ (Nat.lt_succ_self _) [] [] hafT knone_nil hTz
      obtain rfl : zs = zs' := Option.some.inj (hwT'.symm.trans hzw')
      obtain ⟨hV0, hvr0⟩ := hv _ (map_val_cst zs)
      exact ⟨hvr0 _ _ (agree_nil _), hV0⟩
    · cases h
  -- the frame: the handle carries nothing
  have hfr' : FInvR ρ η' th.σs (ResumeR p th.stack Rs) c' ((x, rtR, [R.2]) :: th.env) (Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc))) := by
    refine bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi) (RLink_of hx.1 hx.2.2.2.2.2.2.2.2.2.2.1) ?_ ?_
    · -- the handle: a locative to the whole new buffer, `K` slots initialised when zeroed
      simp only [VRR]
      refine ⟨⟨Or.inr ⟨⟨lbl, 0⟩, ⟨T, some η.tid⟩, _, by simp [hpw, cst, Promises.TVal.mk0],
        (show E'.sto lbl = _ from allocE_eq), ?_, .refl, by first | rfl | trivial, ?_⟩,
        (ownW_own_loc (a := ⟨lbl, 0⟩) (g := 0) (by simp [hpw, cst, Promises.TVal.mk0])).symm⟩, ?_⟩
      · simp only [cl, clI_zero]; exact AtOff.here (Or.inr ⟨K, _, rfl, by simp [husT]⟩)
      · intro N' e' h; left; exact ⟨by simp only [cl, clI_zero]; rfl, rfl⟩
      · intro a ha
        have hav : a = ⟨lbl, 0⟩ := by simp [hpw, cst, Promises.TVal.mk0] at ha; exact ha.symm
        subst hav
        show ev ρ _ ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
        refine Nat.le_min.2 ⟨?_, ?_⟩
        · rw [bumpIni_self]
          split
          · rename_i hzs
            have h1 := hstat hzs
            have h2 : iv = K := by simp only [iv, h1, ite_true]
            rw [h2]; exact Nat.le_max_right _ _
          · exact Nat.zero_le _
        · rw [bumpIni_self]
          split
          · rename_i hzs
            have h1 := hstat hzs
            have h2 : iv = K := by simp only [iv, h1, ite_true]
            rw [h2]; exact Nat.le_max_right _ _
          · exact Nat.zero_le _
    · refine ⟨fun us' h => by simp [rtR, accs] at h; subst h; rfl, ?_, by simp [rtR, wc, accs], ?_, ?_⟩
      · simp [rtR, skel, close, substTs, skelM, rf]
      · simp only [rtR, Valid]; exact Or.inr ⟨⟨lbl, 0⟩, by simp [hpw, cst, Promises.TVal.mk0]⟩
      · simp [rtR, close, substTs, lyt, anyB_zero, idxC, ofMs, modeC]
  -- memory: the new buffer's entry holds nothing
  let f : Nat → Msg := fun j => ⟨offs ⟨lbl, 0⟩ j, bufVal z j, 0⟩
  have hget : ∀ t : Nat, R.1.mem[t]? = if t < (stOf mem pairs th).mem.size then (stOf mem pairs th).mem[t]?
      else if t < (stOf mem pairs th).mem.size + K * nWords us then some (f (t - (stOf mem pairs th).mem.size))
      else none := by
    intro t
    show (allocBuf lbl (K * nWords us) z (stOf mem pairs th)).1.mem[t]? = _
    rw [allocBuf_mem]; exact fold_get f _ _ t
  have hV : R.1.vs.coh = fun b => if b.label = lbl ∧ b.offset < K * nWords us
      then (stOf mem pairs th).mem.size + b.offset else (stOf mem pairs th).vs.coh b := rfl
  have hent : HeldEntry E' R.1 lbl Res.zero := by
    refine HeldEntry_ownP (vals := (List.range (K * nWords us)).map (fun j => cst (bufVal z j)))
      allocE_eq (PromAt_privL (Priv_of allocE_eq rfl hpf0)) (fun o v hov => ?_) (Or.inr ?_)
    · obtain ⟨o, rfl⟩ : ∃ o' : Nat, o' = o := ⟨o, rfl⟩
      have ho' : o < K * nWords us := by
        have := (List.getElem?_eq_some_iff.1 hov).1; simpa using this
      rw [List.getElem?_map, List.getElem?_range ho'] at hov
      simp only [Option.map_some, Option.some.injEq] at hov; subst hov
      refine LatestS_of_latest ⟨⟨f o, ?_, by simp [f, offs], rfl, fun _ _ _ => Nat.zero_le _⟩,
        fun t m ht hm' => ?_⟩ ?_
      rotate_left 2
      · intro hp
        have hp' : R.1.vs.coh ⟨lbl, o⟩ ∈ (stOf mem pairs th).promises := by rw [← hpr]; exact hp
        have h1 := hpl _ hp'
        have e : R.1.vs.coh ⟨lbl, o⟩ = (stOf mem pairs th).mem.size + o := by rw [hV]; simp [ho']
        rw [e] at h1; exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h1)
      · rw [hV, hget]; simp [ho']
      · obtain ⟨t, rfl⟩ : ∃ t' : Nat, t' = t := ⟨t, rfl⟩
        rw [hV] at ht; simp [ho'] at ht
        replace ht : (stOf mem pairs th).mem.size + o < (t : Nat) := ht
        rw [hget t] at hm'
        have h0 : ¬ t < (stOf mem pairs th).mem.size := by omega
        simp only [h0, ite_false] at hm'
        split at hm'
        · simp only [Option.some.injEq] at hm'; subst hm'
          simp [f, offs]; intro h; replace h : (t : Nat) - (stOf mem pairs th).mem.size = o := h; omega
        · cases hm'
    · refine ⟨K, cl ρ η.wit 0 0 τ, usT, (List.range (E'.ini lbl)).map (fun _ => Res.zero), rfl, husT, hini,
        by rw [List.length_map, List.length_range, hnw], by simp, (sum_map_zero _).symm, fun j Rj hj hRj => ?_⟩
      rw [List.getElem?_map, List.getElem?_range hj] at hRj
      simp only [Option.map_some, Option.some.injEq] at hRj; subst hRj
      have hjK : j < K := Nat.lt_of_lt_of_le hj hini
      obtain ⟨zs, hzc⟩ := Option.ne_none_iff_exists'.1 (hini0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hj))
      have hzl : zs.length = nWords us := by rw [← hnw]; exact (hzE zs hzc).2
      have e1 : ((((List.range (K * nWords us)).map (fun j => cst (bufVal z j))).drop (j * nWords usT)).take
          (nWords usT)) = zs.map cst := by
        rw [hnw]
        apply List.ext_getElem?; intro i
        rw [slice_get]
        by_cases hi : i < nWords us
        · simp only [hi, ↓reduceIte]
          have hjN : j * nWords us + i < K * nWords us := by
            have := Nat.mul_le_mul_right (nWords us) (show j + 1 ≤ K by omega); rw [Nat.succ_mul] at this
            omega
          rw [List.getElem?_map, List.getElem?_range hjN]
          have hg' : zs[(j * nWords us + i) % nWords us]? = some (bufVal z (j * nWords us + i)) := by
            rw [hzc, ← hzl]; exact bufVal_some (by omega)
          have hmod : (j * nWords us + i) % nWords us = i := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
          rw [hmod] at hg'
          rw [List.getElem?_map, hg']; rfl
        · simp only [hi, ↓reduceIte]; symm; exact List.getElem?_eq_none (by simp only [List.length_map]; omega)
      rw [e1]; exact ⟨fun _ _ => rfl, fun _ => hzR zs hzc⟩
  have hX' : MemHeldXL E' R.1 lbl H0 Sp :=
    MemHeldXL_tr hX (fun l' hl' => allocE_ne hl') (fun l' hl' => bumpIni_other _ _ _ _ hl')
      (fun l' hl' o w h => LatestNP_growsAtA hg hpr hl' h)
      (fun h => ValOfR_mono (η₁ := CE η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
        (bumpIni_le _ _ _) h)
  refine ⟨Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs, Res.zero + H0,
    ⟨E', footNC_ofLocS (fun _ => rfl) (locNC_allocBuf (fun zs h => by
        simp only [z] at h
        split at h
        · exact TermBNamed.zeroWords_nv _ _ zs h
        · cases h) hfresh hpo hmo.2.2), EFoot_fresh rfl rfl rfl rfl (lt_of_eq_succ hna) (fun l => allocE_sto_cases (T := T) ⟨Clo_cl (fun k => (hE.2.1 k).1) ρ (.array (.lit K) τ),
      mg_cl (fun k => (hE.2.1 k).1.1) (WitAF.mg hiF.2.2.2.2.2.2.1) (.array (.lit K) τ) 0 0 (by simpa [mg] using mg_of_wf τ hwf),
      noIallV_cl (WitAF.ni hiF.2.2.2.2.2.2.1) (.array (.lit K) τ) 0 0 (by simpa [noIallV] using hniA),
      CkW_newBufCell hCk (fun k => (hE.2.1 k).1.1) hwf hop⟩
        (allocBuf_newT (lbl := lbl) (K := K) (z := z) (s := stOf mem pairs th) (e := cl ρ η.wit 0 0 τ) husT hnw)
        (allocBuf_undefT (lbl := lbl) (K := K) (z := z) (s := stOf mem pairs th) (e := cl ρ η.wit 0 0 τ) husT hnw
          (fun h0 => by
            cases hzz : zeroableIn [] [] (close th.σs τ) with
            | false =>
              show (if zeroableIn [] [] (close th.σs τ) = true then zeroWords (close th.σs τ) else none) = none
              simp [hzz]
            | true =>
              exact absurd ((zrel_zero _ _ [] [] (zrel_WitL hiF.2.2.2.1 (fun k => (hE.2.1 k).1) ρ hop hr) hsig
                knone_nil).1 hzz) (by rw [h0]; simp))) l) (fun _ => .inl rfl)
      (fun l => ite_ini_cases _ _ _ l)
      (hrw := RiniW_of_ne fun l c h => bumpIni_other _ _ _ _ fun e => by
        subst e; cases h.symm.trans hnone0), (by seenT), (by boxT), ⟨ρ, η', c', Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)), Rs, rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨he, hck⟩, htv', hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      ⟨hmo', hoo', fun t ht => by
        have ht' : t ∈ R.1.promises := ht
        rw [hpr] at ht'; exact Nat.lt_of_lt_of_le (hpl t ht') hg.1,
      ⟨fun j hj => ?_, PrivCoh_allocBuf hfr.2
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, ho, hp, hT, hus1, hle, hlt⟩ := hu
          refine ⟨c, N, e, us1, by rw [allocE_ne hl] at hc; exact hc, ho, hp, hT, hus1, ?_, hlt⟩
          rwa [TEnv.rc_congr (η' := E') (η := CE η) (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)] at hle)
        hoo' hfresh
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, -, -, hT, hus1, hle, hlt⟩ := hu
          rw [hl, show E'.sto lbl = some ⟨T, some η.tid⟩ from allocE_eq] at hc; cases hc
          have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N) e := hT
          simp only [Ty.array.injEq, Idx.lit.injEq] at hT2; obtain ⟨rfl, rfl⟩ := hT2
          refine (Classical.em _).elim id fun hz => (?_ : False).elim
          have hs : z.isSome = true := Option.ne_none_iff_isSome.1 hz
          have hrc : K ≤ E'.rc lbl := by
            show K ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
            have hiv : iv = K := by simp only [iv, hs, ↓reduceIte]
            rw [bumpIni_self, bumpIni_self, hiv]
            exact Nat.le_min.2 ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
          rw [hl] at hle
          have := Nat.mul_le_mul_right (nWords us1) hrc
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_trans this hle)) (Nat.lt_irrefl _))⟩, hsn,
        hoh', hpd', hopub', hpi', BoxInv_allocBuf hbi rfl rfl rfl (fun l hl => by rw [allocE_ne hl]; rfl) (fun l hl => bumpIni_other _ _ _ _ hl),
        PromOK_eq hpo rfl rfl⟩,
      MemHeldK_unfocus hX' hent (fun _ h => h.1 hpf0), CrKeep_alloc (hini := fun l hl => bumpIni_other _ _ _ _ hl)
        (hrc := fun l hl => TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)) hg
        (by show (allocBuf lbl (K * nWords us) z (stOf mem pairs th)).1.promises.Sublist (stOf mem pairs th).promises
            rw [hpr]; exact List.Sublist.refl _)
        (fun t ht hn => absurd (by show t ∈ (allocBuf lbl (K * nWords us) z (stOf mem pairs th)).1.promises
                                   rw [hpr]; exact ht) hn) (fun _ hl => allocE_ne hl) hnone0
        (Or.inr ⟨⟨_, by simp [E', allocE]; rfl, rfl⟩, hpf0⟩)⟩,
    ⟨th.nalloc, Nat.le_refl _, by show th.nalloc < R.1.nalloc; have : R.1.nalloc = th.nalloc + 1 := hna; omega, rfl⟩, ?_⟩
  · have hj' : th.nalloc ≤ j := by
      have h1 : R.1.nalloc ≤ j := hj
      rw [hna] at h1; exact Nat.le_of_succ_le h1
    obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
    have hne : freshLabel g.lbase g.n g.i j ≠ lbl := fun h => by
      have := freshLabel_inj_k hn h; subst this
      have h1 : R.1.nalloc ≤ th.nalloc := hj
      rw [hna] at h1; exact absurd h1 (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
    refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, ?_, f5⟩
    · change R.1.mem[t]? = some m at ht
      by_cases hlt : t < (stOf mem pairs th).mem.size
      · rw [hg.2.1 t hlt] at ht; exact f2 t m ht hl
      · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
    · show bumpIni η.ini lbl iv (freshLabel g.lbase g.n g.i j) = 0
      rw [bumpIni_other _ _ _ _ hne]; exact f4
  · rw [hHe, hR0]
    intro k
    simp only [Res.add_apply, Res.zero_apply]
    omega

/-- The witness keeps `E.sto`. -/
def StoEq (E : TEnv) (E' : TEnv) : Prop := ∀ l, E'.sto l = E.sto l

theorem ThInvMKQ.mono {Q Q' : TEnv → Prop} {p : Prog} {g : G} {E0 : TEnv} {s : St} {S0 : AllocLabel → List Res}
    {mem : Memory} {pairs : List Ts} {th : TTh} {Tot H : Res} (hQ : ∀ E, Q E → Q' E)
    (h : ThInvMKQ Q p g E0 s S0 mem pairs th Tot H) : ThInvMKQ Q' p g E0 s S0 mem pairs th Tot H :=
  let ⟨E, hq, h0⟩ := h
  ⟨E, hQ E hq, h0⟩

/-- (X) `liftMR` keeping `E.sto` on the witness. -/
theorem liftMRN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {η : TEnv} {Rf Rs H : Res}
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvRE p (CE η) r.2.2 (Rf + Rs))
    (hs : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H :=
  ⟨h.1, fun r hr => ⟨Rf + Rs, H, ⟨CE η, fun _ => rfl, EFoot_refl, (by seenT), (by boxT), h.2 r hr, MemInv_same hm (hs r hr),
    MemHeldK_eqs hH (hs r hr).1 (hs r hr).2.2.2.1,
    CrKeep_eqs (hs r hr).1 (hs r hr).2.2.2.1⟩, Res.le_refl _⟩⟩

/-- (X) `tstepMR_inlB` keeping `E.sto` on the witness. -/
theorem tstepMR_inlBN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs H : Res} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hv : VRR ρ η t (shp rt) ws R) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
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
    refine ⟨Rf + Rs, H, ⟨CE η', fun _ => rfl, by rw [hCE]; exact EFoot_seeBox (nalloc_alloc_box hm.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)), (by seenT), (by rw [hCE]; refine BoxNewV_seeBox hbnone ?_; intro e0 env0 he hs hev; have hev' := envV_tail he hev; exact payV_lt (TermViewInv.asArm_V has (TermViewInv.evalAt_V hev' hea)) hs.2.2.2.2.2 (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))),
      ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, ?_, ?_, ?_⟩,
      Res.le_refl _⟩
    · rw [hCE]; exact hm'
    · rw [hCE]; exact MemHeldK_of (MemHeldL_seeE (lbl := lbl) (F := s'.vs.vWr) hHb hstoL hpfL)
    · rw [hCE]; exact CrKeep_seeE (lbl := lbl) (F := s'.vs.vWr) (CrKeep_box hm hal B) hstoL

/-- (X) `tstepMR_inrB` keeping `E.sto` on the witness. -/
theorem tstepMR_inrBN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs H : Res} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hv : VRR ρ η t (shp rt) ws R) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
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
    refine ⟨Rf + Rs, H, ⟨CE η', fun _ => rfl, by rw [hCE]; exact EFoot_seeBox (nalloc_alloc_box hm.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)), (by seenT), (by rw [hCE]; refine BoxNewV_seeBox hbnone ?_; intro e0 env0 he hs hev; have hev' := envV_tail he hev; exact payV_lt (TermViewInv.asArm_V has (TermViewInv.evalAt_V hev' hea)) hs.2.2.2.2.2 (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))),
      ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, ?_, ?_, ?_⟩,
      Res.le_refl _⟩
    · rw [hCE]; exact hm'
    · rw [hCE]; exact MemHeldK_of (MemHeldL_seeE (lbl := lbl) (F := s'.vs.vWr) hHb hstoL hpfL)
    · rw [hCE]; exact CrKeep_seeE (lbl := lbl) (F := s'.vs.vWr) (CrKeep_box hm hal B) hstoL

/-- (X) `tstepMR_inlBB` keeping `E.sto` on the witness. -/
theorem tstepMR_inlBBN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
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
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
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
    refine ⟨Rf + Rs, H, ⟨CE η', fun _ => rfl, EFoot_congr (s1 := s1) (by rw [hCE]; exact EFoot_seeBox (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))) e5 e7 (congrArg Array.size e1) e4 e1, (by seenT), (by rw [hCE]; refine BoxNewV_seeBox hbnone ?_; intro e0 env0 he hs hev; have hev' := envV_tail he hev; obtain ⟨hp1, hV1⟩ := pV_of_proj h1 hea hs hev'; exact payV_lt hp1 hV1 (alloc_size_len _ hal hlen)),
      ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, ?_, ?_, ?_⟩,
      Res.le_refl _⟩
    · rw [hCE]; exact hm'
    · rw [hCE]; exact MemHeldK_of (MemHeldL_seeE (lbl := lbl) (F := s'.vs.vWr) hHb hstoL hpfL)
    · rw [hCE]; exact CrKeep_trans (CrKeep_eqs e1 e4) (CrKeep_seeE (lbl := lbl) (F := s'.vs.vWr) (CrKeep_box hm1 hal B) hstoL)

/-- (X) `tstepMR_inrBB` keeping `E.sto` on the witness. -/
theorem tstepMR_inrBBN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
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
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
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
    refine ⟨Rf + Rs, H, ⟨CE η', fun _ => rfl, EFoot_congr (s1 := s1) (by rw [hCE]; exact EFoot_seeBox (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))) e5 e7 (congrArg Array.size e1) e4 e1, (by seenT), (by rw [hCE]; refine BoxNewV_seeBox hbnone ?_; intro e0 env0 he hs hev; have hev' := envV_tail he hev; obtain ⟨hp1, hV1⟩ := pV_of_proj h1 hea hs hev'; exact payV_lt hp1 hV1 (alloc_size_len _ hal hlen)),
      ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, ?_, ?_, ?_⟩,
      Res.le_refl _⟩
    · rw [hCE]; exact hm'
    · rw [hCE]; exact MemHeldK_of (MemHeldL_seeE (lbl := lbl) (F := s'.vs.vWr) hHb hstoL hpfL)
    · rw [hCE]; exact CrKeep_trans (CrKeep_eqs e1 e4) (CrKeep_seeE (lbl := lbl) (F := s'.vs.vWr) (CrKeep_box hm1 hal B) hstoL)

section
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}

/-- (X) `tstepMR_inlT` keeping `E.sto` on the witness. -/
theorem tstepMR_inlTN {Sp : AllocLabel → List Res} {x : String} {τ : Ty} {a : At} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
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
        | false => exact paW <| tstepMR_inlBN (hbf := hbf) hterm hn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hE hm hH (retPw_eq hRP (use_ret hu))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu htv).2.1
            exact tstepMR_inlBBN (hbf := hbf) hterm hn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hi.1.2.2.2.1 hi.1.2.2.2.2.1 ho htb hl) hE hm hH hpx (retPw_eq hRP (use_ret hu))
      · refine paW <| liftMRN hm hH (tstep_inlR hterm hP (fun t' c₁' hu' => ?_) hT hCk hi hE htv hRP hPS)
          (same_inl hterm fun t0 ws0 hea0 => ?_)
        · rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
          rw [← hsk]; exact hS
        · rw [hea, Option.some.injEq, Prod.mk.injEq] at hea0; obtain ⟨rfl, rfl⟩ := hea0
          exact hS

/-- (X) `tstepMR_inrT` keeping `E.sto` on the witness. -/
theorem tstepMR_inrTN {Sp : AllocLabel → List Res} {x : String} {τ : Ty} {a : At} {e : Expr} {Rf Rs H : Res}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
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
        | false => exact paW <| tstepMR_inrBN (hbf := hbf) hterm hn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hE hm hH (retPw_eq hRP (use_ret hu))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu htv).2.1
            exact tstepMR_inrBBN (hbf := hbf) hterm hn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hi.1.2.2.2.1 hi.1.2.2.2.2.1 ho htb hl) hE hm hH hpx (retPw_eq hRP (use_ret hu))
      · refine paW <| liftMRN hm hH (tstep_inrR hterm hP (fun t' c₁' hu' => ?_) hT hCk hi hE htv hRP hPS)
          (same_inr hterm fun t0 ws0 hea0 => ?_)
        · rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
          rw [← hsk]; exact hS
        · rw [hea, Option.some.injEq, Prod.mk.injEq] at hea0; obtain ⟨rfl, rfl⟩ := hea0
          exact hS

end

/-- (X) `case_armNBR` keeping `E.sto` on the witness. -/
theorem case_armNBRN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 q1 : List Word} {R Rr Rf Rs H : Res}
    (hb : c₁.bind xv u = .ok c') (he : TypedK p η c' e') (htv : TvOK c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf) (hE : EnvOK p η)
    (hm1 : MemInv g (CE η) s1) (hH1 : MemHeldL (CE η) s1 H Sp) {S0 : St}
    (hk1 : CrKeep (CE η) (CE η) S0 s1)
    (hty : isBoxed ty = false) (hq : ofArm ty j p1 = some q1) (hlay : Lay th.σs u ty q1)
    (hvr : VRR ρ η u (shp ty) q1 R) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    injM g s1 ty j p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ty j p1, ∃ Tot H',
      ThInvMKQ (StoEq (CE η)) p g (CE η) S0 Sp r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) Tot H' ∧
      Tot + H' ≤ Rf + Rs + H := by
  rw [injM_nbB hty, hq]
  refine ⟨by simp [ol], fun r2 hr2 => ?_⟩
  simp [ol] at hr2; subst hr2
  have hf := FInvR_mono (bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvr hlay) (res_swap_le hle)
  exact ⟨Rf + Rs, H, ⟨CE η, fun _ => rfl, EFoot_refl, (by seenT), (by boxT), ⟨ρ, η, c', Rf, Rs, rfl, hE, he, htv, by simpa [withS] using hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, hm1, MemHeldK_of hH1, hk1⟩,
    Res.le_refl _⟩

/-- (X) `case_armBR` keeping `E.sto` on the witness. -/
theorem case_armBRN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
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
      ThInvMKQ (StoEq (CE η)) p g (CE η) S0 Sp r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) Tot H' ∧
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
    refine ⟨Rf + Rs, H, ⟨CE η', fun _ => rfl, by
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

/-- (X) `tstepMR_caseB` keeping `E.sto` on the witness. -/
theorem tstepMR_caseBN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
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
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
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
          ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r2.1.mem r2.1.pairs (withS { th with term := e₁, env := (x, ra, r2.2) :: th.env } r2.1) Tot H' ∧
          Tot + H' ≤ Rf + Rs + H := by
      intro s1 p1 hm1 hH1 hk1 hn1 hWp hpV
      cases hty : isBoxed ra with
      | false =>
          obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hA hj).2 hty
          obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ :=
            case_arm_nbR hE.2.1 hE.2.2 hty hsg2.1 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
          exact case_armNBRN hb1 he1 htv1 hi1 hle hE hm1 hH1 hk1 hty hq1 ⟨hs1, hsa, hw1, hv1, hly.1⟩ hvr1 hRP1
      | true =>
          have harmA : (armsOf ra)[B0.tag]? = some arm := by
            rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_left hj]
          exact case_armBRN (hbf := hbf) (s0 := 0) hb1 he1 htv1 hi1 hle hE hm1 hH1 hk1 hn1 hn hty (by rw [harmA]; exact hus)
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
          ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r2.1.mem r2.1.pairs (withS { th with term := e₂, env := (y, rb, r2.2) :: th.env } r2.1) Tot H' ∧
          Tot + H' ≤ Rf + Rs + H := by
      intro s1 p1 hm1 hH1 hk1 hn1 hWp hpV
      cases hty : isBoxed rb with
      | false =>
          obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hB' hj').2 hty
          obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ :=
            case_arm_nbR hE.2.1 hE.2.2 hty hsg2.2 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
          exact case_armNBRN hb2 he2 htv2 hi1 hle hE hm1 hH1 hk1 hty hq1 ⟨hs1, hsb, hw1, hv1, hly.2⟩ hvr1 hRP1
      | true =>
          have harmB : (armsOf rb)[B0.tag - (armsOf ra).length]? = some arm := by
            rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_right hj']
          exact case_armBRN (hbf := hbf) (s0 := (armsOf ra).length) hb2 he2 htv2 hi1 hle hE hm1 hH1 hk1 hn1 hn hty
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

/-- (X) `tstepMR_caseT` keeping `E.sto` on the witness. -/
theorem tstepMR_caseTN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr} {Rf Rs H : Res}
    (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
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
      exact tstepMR_caseBN (hbf := hbf) hterm hn hb1 ⟨he1, hck12.1⟩ htv12.1 hb2 ⟨he2, hck12.2⟩ htv12.2 hi1 hle hea hvV hv hl hS hsg hE hm hH hpx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    · have hnb : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs t').tier ≠ .boxed := fun t' c₁' hu' => by
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
        rw [← tier_of_eskel hl.2.1]; exact hS
      refine paW <| liftMRN hm hH (tstep_caseR hterm hnb hT hCk hi hE htv hRP hPS) ?_
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

#print axioms tstepMR_newN
#print axioms tstepMR_newBufN
#print axioms liftMRN
#print axioms tstepMR_inlBN
#print axioms tstepMR_inrBN
#print axioms tstepMR_inlBBN
#print axioms tstepMR_inrBBN
#print axioms tstepMR_inlTN
#print axioms tstepMR_inrTN
#print axioms case_armNBRN
#print axioms case_armBRN
#print axioms tstepMR_caseBN
#print axioms tstepMR_caseTN

#print axioms locNC_allocBuf
#print axioms footNC_ofLocS
#print axioms ThInvMKQ.mono

end TermFootNP
