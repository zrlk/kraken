import WeakCore.EtaP
import WeakCore.ContIV
import WeakCore.WinPremises
import WeakCore.TermPtrKey
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! **EtaFD** (droppable port): the x-free lineage EtaF on the
♭ layer `ThInvEB` (RetPw + DyFr, W's layer-free defs) with W's record conjuncts `TyOKE`/`RecFresh`, so the
NLayer `hTy` premise is carried by the lineage.  Seeded at a `SysInvN` base from `base_shape` and
`SysInvN.tyRec` (O1).  No new hypothesis on any discharge statement; no edit to EtaR/EtaN/EtaF/EtaW. -/
namespace EtaDyFr
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open CertWinProof (shE ext_shE shE_sto FInvB_monoK cap_presB)
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

-- PART newNCB
section
open WeakMem (Val)
theorem tstepM_newNCB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {T : Option Ty} {e : Expr}
    (hterm : th.term = .let_ x (.new a T) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ E', NewCellSto g ρ η th E' ∧ FreshArr g ρ η th E' r ∧ EFootPB g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧
      ThInvEB g.lbase g.n g.i p E' r.2.2 ∧ MemInvB g E' (stOf r.1 r.2.1 r.2.2) := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | new hu _ hb =>
  obtain ⟨tv, c₁, hu, hb, htvT⟩ : ∃ tv c₁, cx.use a = .ok (tv, c₁) ∧ c₁.bind x (.ptr .own tv) = .ok c' ∧ some tv = _ :=
    ⟨_, _, hu, hb, rfl⟩
  obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
  have ho : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have htb := (use_TvOK hu htv).2.1
  have hsig : sig rt = sig (cl ρ η.wit 0 0 tv) := lay_closed hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl
  obtain ⟨us, hus⟩ : ∃ us, accs rt = some us := by
    cases h : accs rt with
    | none => exact absurd (by simp [wc, h]) hl.2.2.1
    | some us => exact ⟨us, rfl⟩
  have hlen : ws.length = nWords us := hl.1 us hus
  have hwcT : wc (cl ρ η.wit 0 0 tv) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvc : (VRF False) (fun _ => 0) (CE η) (cl ρ η.wit 0 0 tv) (shp (cl ρ η.wit 0 0 tv)) ws := by
    rw [← shp_of_sig hsig]
    exact (VR_closeB hE.2.1 ρ tv [] 0 ρ (fun _ => 0) (shp rt) ws (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := hm
  obtain ⟨hnone, hfresh, -, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hval : ValOfB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) (cl ρ η.wit 0 0 tv)
      (ws.map (bumpW (stOf mem pairs th).vs.vRelSt)) :=
    ValOf_monoB (η₁ := CE η) (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      rfl rfl (fun l c h => allocE_sub hnone h) (fun _ => Nat.le_refl _)
      (EnvValB.store (η := CE η) ⟨hvc, Valid_of_sig hsig hl.2.2.2.1⟩ hsn)
  have hx : ExtB η (η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto) :=
    Ext_withStoB hE.2.1 (fun l c h => allocE_sub (η := CE η) hnone h) (fun _ => Nat.le_refl _)
  have key : ∀ r ∈ tstep g mem pairs th, ∃ s' pw,
      (s', pw) ∈ alloc g.k g.arch (freshLabel g.lbase g.n g.i th.nalloc) us ws (stOf mem pairs th) ∧
      ∃ tys, r = (s'.mem, s'.pairs,
        { withS { th with term := e, env := (x, .ptr .own rt, [pw]) :: th.env } s' with tys := tys }) := by
    intro r hr
    obtain ⟨s1, t1, ws1, hm1, tys, rfl⟩ := TermRun.tstep_new_mem hterm hr
    simp only [evalOp, hea, hus, List.mem_map] at hm1
    obtain ⟨⟨s2, pw⟩, hal, he⟩ := hm1
    cases he
    exact ⟨_, _, hal, tys, rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := freshLabel g.lbase g.n g.i th.nalloc)
      (s := stOf mem pairs th) hlen
    simp only [tstep, hterm, evalOp, hea, hus, ne_eq, List.map_eq_nil_iff]
    exact List.ne_nil_of_mem hr
  · intro r hr
    obtain ⟨s', pw, hal, tys, rfl⟩ := key r hr
    obtain ⟨hmo', hoo', hpw⟩ := alloc_okPB hwcT hlen hval hfresh hnone hpl hpo.1 hpo.2.1 hpf0 hmo hoo ⟨s', pw⟩ hal
    obtain ⟨hg, -, hna, hpl', hful⟩ := alloc_growsP hpl ⟨s', pw⟩ hal
    obtain ⟨hwr, hhid⟩ := alloc_hidPB (s := stOf mem pairs th) hval
      (ShapeC_of_wc hwcT (by rw [List.length_map]; exact hlen))
      (by obtain ⟨_, h, -⟩ := wc_some hwcT; simp [h]) hfresh hpl ⟨s', pw⟩ hal
    simp only at hmo' hoo' hpw hg hna hwr hhid hpl' hful
    subst hpw
    have hwA : ∀ T o w, WordOKB (CE η) T o w →
        WordOKB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) T o w :=
      fun T o w h => WordOK_monoB (η₁ := CE η)
        (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
        rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _)
        (fun _ _ h' => h') (fun _ h' => h') h
    have hoh' : OwnHidPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem s'.vs
        s'.promises := by
      refine ⟨fun l c hc ho o hi => ?_, fun l c hc ho hlt => ?_⟩
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          rw [allocE_eq] at hc; cases hc; exact hhid o
        · rw [allocE_ne hl] at hc
          exact HiddenP_growsAtB (hoh.1 l c hc ho o hi) (hwA _ _) hwr hg hl hful
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
            (Nat.not_lt_zero _)
        · rw [allocE_ne hl] at hc
          obtain ⟨f, hf, hs, hH⟩ := hoh.2 l c hc ho hlt
          exact ⟨f, hf, fun hz => hs (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
            fun o hi => HiddenP_growsAtB (hH o hi) (hwA _ _) (Nat.le_refl _) hg hl hful⟩
    have hpd' : PubDefPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem
        s'.promises := by
      intro l c f hc hown hf o hi
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at hc; cases hc; exact (hown rfl).elim
      · rw [allocE_ne hl] at hc
        exact HiddenP_growsAtB (hpd l c f hc hown hf o hi) (hwA _ _) (Nat.le_refl _) hg hl hful
    have hpi' : PubInvB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      refine PubInv_growB (hbs := fun l hb h => by
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
    have hNC : NewCellSto g ρ η th (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) := by
      intro x' a' T' e' h'
      rw [hterm] at h'
      obtain ⟨-, ⟨-, hT'⟩, -⟩ := (by simpa using h' : x = x' ∧ (a = a' ∧ _ = T') ∧ e = e')
      refine ⟨_, allocE_eq, ?_⟩
      show cl ρ η.wit 0 0 tv = cl ρ η.wit 0 0 T'
      rw [Option.some.inj htvT, hT']
    refine ⟨allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv), hNC,
      (by
        intro l c N u hf hc hty
        obtain ⟨j, hj, -, rfl⟩ := hf
        by_cases hl : freshLabel g.lbase g.n g.i j = freshLabel g.lbase g.n g.i th.nalloc
        · rw [hl, allocE_eq] at hc
          cases hc
          have h2 : cl ρ η.wit 0 0 tv = .array (.lit N) u := hty
          exact absurd hwcT (by rw [h2]; simp [wc, accs])
        · rw [allocE_ne hl] at hc
          have h0 : (CE η).sto (freshLabel g.lbase g.n g.i j) = none := (hfr.1 j hj).1
          rw [h0] at hc
          cases hc),
      EFoot_freshB rfl rfl rfl rfl (lt_of_eq_succ hna) (fun l => allocE_sto_cases ⟨Clo_cl (fun k => (hE.2.1 k).1) ρ tv,
        mg_cl (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.2.2.2.2.2.2.1) tv 0 0 (use_mg hu htv),
        noIallV_cl (WitAF.ni hi.2.2.2.2.2.2.1) tv 0 0 (hniA tv _ hu), trivial⟩ (alloc_newT hal hwcT) (alloc_undefT hal hwcT) l) (fun _ => .inl rfl)
        (fun _ => ⟨Nat.le_refl _, .inl rfl⟩),
      ⟨ρ, η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto, c', rfl,
        ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, ?_⟩
    · refine bind_FInvB hb (FInv_extB hE.2.1 hx hi1) ?_ ?_
      · simp only [VRF, VRb2]
        exact ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, ⟨cl ρ η.wit 0 0 tv, some η.tid⟩, by simp [cst, Promises.TVal.mk0], rfl,
          by simp [TEnv.withStoB, allocE, CE], .refl, rfl,
          show accs (cl ρ η.wit 0 0 tv) ≠ none from fun h => by simp [wc, h] at hwcT⟩
      · refine ⟨fun us h => by simp [accs] at h; subst h; rfl, ?_, by simp [wc, accs],
          ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, by simp [cst, Promises.TVal.mk0]⟩, ?_⟩
        · show Ty.ptr (skelM .own) (etok (skel rt)) = Ty.ptr _ _
          rw [hl.2.1]; rfl
        · show Ty.ptr (modeC 0 .own) (etok (lyt 0 rt)) = Ty.ptr _ _
          rw [hl.2.2.2.2]; rfl
    have hopub' : OwnPubV (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      intro l c f hc ho hf
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
      · rw [allocE_ne hl] at hc
        exact ((hopub.alloc hpl hal) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
          fun a ha hi c1 N1 e1 us1 h1 => hi c1 N1 e1 us1 (by rw [allocE_ne (fun e => hl (ha.symm.trans e))]; exact h1))
    · refine ⟨hmo', hoo', hpl', ⟨fun j hj => ?_, PrivCoh_growsAtB hfr.2
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
          refine Classical.byContradiction fun hn' => ?_
          obtain ⟨m', hm', e⟩ := hful t hp hn'
          rw [ht] at hm'; cases hm'
          exact hne (hl.symm.trans e)
        · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
end

theorem ThInvEB_extD {p : Prog} {E : TEnv} {th : TTh} {x : String} {n : ExtName} {a : At} {e : Expr}
    {rt : Ty} {ws rs : List Word} {i : Nat} {tr : List Event} {vv : VState} {pm : Option Ts} (hn : n ≠ .current)
    (hterm : th.term = .let_ x (.ext n a) e) (hev : evalAt th.env a = some (rt, ws)) (hrs : rs ∈ n.resultsL i ws tr)
    (hR : ThInvEB glb gnum gi p E th) :
    ThInvEB glb gnum gi p E { th with term := e, env := (x, n.sig.2, rs) :: th.env, vs := vv, permit := pm } := by
  obtain ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hpw, hDy⟩ := hR
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | ext hu _ hsub hb =>
    have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
    have htv1 := use_TvOK hu htv
    have htv' := (bind_TvOK hb htv1.1 (TermTv.extSig_tb _ _) (TermTv.extSig_mg _)).1
    obtain ⟨hi1, rt1, ws1, hev1, hvr1, hl1⟩ := use_FInvB (bkG := False) hu hi
    rw [hev] at hev1; cases hev1
    obtain ⟨hz, hl⟩ := ext_resB (bkG := False) (σs := th.σs) hn (VR_subB (bkG := False) hi1.1 hsub _ _ hvr1)
      hl1.2.2.1 hrs
    refine ⟨ρ, η, c', hCE, hE, he, htv', bind_FInvB hb hi1 (VRR_VRB _ (RLink_ofB hE.2.1 hE.2.2) hz) hl, ?_, hDy.letW hterm rfl⟩
    show RetPw th.σs th.stack c'.ret
    rw [hret]; exact hpw

theorem ThInvEB_curD {p : Prog} {E : TEnv} {th : TTh} {x : String} {a : At} {e : Expr}
    {l : AllocLabel} (hterm : th.term = .let_ x (.ext .current a) e) (hs : E.sto l = some ⟨.unit, none⟩)
    (hp : E.pfr l = some 0) (hR : ThInvEB glb gnum gi p E th) :
    ThInvEB glb gnum gi p E { th with term := e, env := (x, .tid, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env } := by
  obtain ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hpw, hDy⟩ := hR
  subst hCE
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  cases hop with
  | ext hu _ hsub hb =>
    have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
    have htv1 := use_TvOK hu htv
    have htv' := (bind_TvOK hb htv1.1 (by simp [ExtName.sig, tb]) (by simp [ExtName.sig, mg])).1
    obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
    have hvr : (VRF False) ρ η .tid (shp .tid) [cst (.loc ⟨l, 0⟩ 0)] :=
      ⟨l, ⟨.unit, none⟩, rfl, hs, rfl, 0, hp, .inr (.inl fun _ _ => Nat.zero_le _)⟩
    have hlay : Lay th.σs .tid .tid [cst (.loc ⟨l, 0⟩ 0)] :=
      ⟨fun us h => by simp [accs] at h; subst h; rfl, by first | rfl | simp [etok, close, substTs, skel],
        by simp [wc, accs], trivial, by first | rfl | simp [etok, close, substTs, lyt]⟩
    refine ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, ?_, hDy.letW hterm rfl⟩
    show RetPw th.σs th.stack c'.ret
    rw [hret]; exact hpw


theorem tstep_capBD {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} (hP : ProgT p) (hc : CapT th.term)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ThInvEB g.lbase g.n g.i p (CE η) r.2.2 ∧ Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  obtain ⟨x, op, e, hterm, hA, hncl⟩ := capT_inv hc
  have hsame := same_let (g := g) (mem := mem) (pairs := pairs) hterm
    (fun f is a ts h => by subst h; simp [CapOp] at hA) (fun f a h => by subst h; simp [CapOp] at hA)
    (fun r hr => same_of_eq (cap_state hA r hr))
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c₁
      have key := tstep_capOp (g := g) (mem := mem) (pairs := pairs) hterm hA
      refine ⟨?_, fun r hr => ⟨?_, hsame r hr⟩⟩
      · rw [key]; cases op <;> simp only [CapOp] at hA <;> simp [evalOp]
      · rw [key] at hr
        simp only [List.mem_map] at hr
        obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := hr
        exact ⟨ρ, η, c₁, rfl, hE, he, OpT_TvOK hP hop htv, cap_presB hop hA hncl hi hm,
          retPw_skel hPS hRP (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0), hDy.letW hterm rfl⟩


theorem pub_stepD {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ y (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hsc : PubScope cx a)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ E1, ThInvEB g.lbase g.n g.i p E1 r.2.2 ∧
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
        retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
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
        retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_fenceB hm, Or.inl rfl⟩
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
          bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr hl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
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


/-! ### The record conjuncts across a ♭ step -/

theorem TyOKE_stoD {g : G} {E E' : TEnv} (e : E'.sto = E.sto) (h : TyOKE g E) : TyOKE g E' :=
  fun l t c ht hc => h l t c ht (by rw [← e]; exact hc)

/-- W `tyOKE_tstep` against the ♭ footprint `EFootBB`. -/
theorem tyOKE_tstepB {W : Ty → Prop} {g : G} {E E' : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (hn : 0 < g.n) (hr : r ∈ tstep g mem pairs th)
    (hF : EFootBB W g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hT : TyOKE g E) (hR : RecFresh g g.i th.nalloc)
    (hnew : ∀ c t, E'.sto (freshLabel g.lbase g.n g.i th.nalloc) = some c →
      tysUpd g.tys th r.2.2 (freshLabel g.lbase g.n g.i th.nalloc) = some (t, true) → c.ty = clD t) :
    TyOKE { g with tys := tysUpd g.tys th r.2.2 } E' ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc := by
  have hT' : TyOKE g E' := TyOKE_footB hF hT hR
  have hR' : RecFresh g g.i r.2.2.nalloc := RecFresh_mono hR (TermNallocF.tstep_nallocLe hr)
  refine ⟨fun l t c ht hc => ?_, fun j hj t ht => ?_⟩
  · rcases tysUpd_tstep hr l with h | ⟨rfl, -, -⟩
    · have ht' : tysUpd g.tys th r.2.2 l = some (t, true) := ht
      rw [h] at ht'
      exact hT' l t c ht' hc
    · exact hnew c t hc ht
  · have ht' : tysUpd g.tys th r.2.2 (freshLabel g.lbase g.n g.i j) = some (t, true) := ht
    rcases tysUpd_tstep hr (freshLabel g.lbase g.n g.i j) with h | ⟨he, hlt, -⟩
    · rw [h] at ht'
      exact hR' j hj t ht'
    · have := freshLabel_inj_k hn he
      omega

/-- Off `new` terms the step leaves no record at the fresh label. -/
theorem hnew_none {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh} {E' : TEnv}
    (hr : r ∈ tstep g mem pairs th) (hR : RecFresh g g.i th.nalloc)
    (hnn : ∀ x a T e, th.term ≠ .let_ x (.new a T) e) :
    ∀ c t, E'.sto (freshLabel g.lbase g.n g.i th.nalloc) = some c →
      tysUpd g.tys th r.2.2 (freshLabel g.lbase g.n g.i th.nalloc) = some (t, true) → c.ty = clD t := by
  intro c t _ ht
  rcases tysUpd_tstep hr (freshLabel g.lbase g.n g.i th.nalloc) with h | ⟨-, -, x, a, T, e, hte⟩
  · rw [h] at ht; exact absurd ht (hR th.nalloc (Nat.le_refl _) t)
  · exact absurd hte (hnn x a T e)

/-! ### The x-free lineage with footprint and records -/

/-- The labels of `E` beyond the anchor `E0` are fresh labels of thread `i` (geometry `lb`, `nn`) at indices `≥ n0`. -/
def FootInD (lb nn i n0 : Nat) (E0 E : TEnv) : Prop :=
  ∀ l, E.sto l = E0.sto l ∨ ∃ j, n0 ≤ j ∧ l = freshLabel lb nn i j

theorem footInD_refl {lb nn i n0 : Nat} {E : TEnv} : FootInD lb nn i n0 E E := fun _ => .inl rfl

theorem footInD_sto {lb nn i n0 : Nat} {E0 E E' : TEnv} (h : FootInD lb nn i n0 E0 E) (e : E'.sto = E.sto) :
    FootInD lb nn i n0 E0 E' := fun l => by rw [e]; exact h l

/-- **EtaFD**: EtaF on the ♭ layer (`ThInvEB`, RetPw + DyFr) with W's record conjuncts `TyOKE`/`RecFresh`. -/
def EtaFD (p : Prog) (k : Promises.Knobs) (arch : Arch) (lb nn : Nat) (E0 : TEnv) (n0 : Nat) (i : Nat) (c : Cfg) :
    Prop :=
  ∃ th E, c.ths[i]? = some th ∧ ThInvEB c.lbase c.n i p E th ∧ MemInvB (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    (gOf p k arch c i).boxFence = true ∧ ExtB E0 E ∧ c.lbase = lb ∧ c.n = nn ∧ n0 ≤ th.nalloc ∧
    FootInD lb nn i n0 E0 E ∧ TyOKE (gOf p k arch c i) E ∧ RecFresh (gOf p k arch c i) i th.nalloc

theorem eta_promFD {p : Prog} {k : Promises.Knobs} {arch : Arch} {lb nn : Nat} {E0 : TEnv} {n0 i : Nat}
    {c : Cfg} {a : Address} {v : WeakMem.Val} {w : Ts} (hI : EtaFD p k arch lb nn E0 n0 i c) :
    EtaFD p k arch lb nn E0 n0 i (promise c i a v w) := by
  obtain ⟨th, E, hth, hT, hm, hb, hx, hl, hnn, hn, hf, hTy, hRc⟩ := hI
  obtain ⟨-, h2, h3⟩ := promise_inv (a := a) (v := v) (w := w) hth
  have hlb : (promise c i a v w).lbase = c.lbase := congrArg G.lbase (gOf_promise (p := p) (k := k) (arch := arch))
  exact ⟨_, E, h2, (by rw [hlb, promise_n]; exact hT), by rw [gOf_promise, h3]; exact MemInv_promStB hm,
    by rw [gOf_promise]; exact hb, hx, by rw [hlb]; exact hl, by rw [promise_n]; exact hnn, hn, hf,
    by rw [gOf_promise]; exact hTy, by rw [gOf_promise]; exact hRc⟩

theorem eta_extFD {p : Prog} {k : Promises.Knobs} {arch : Arch} {lb nn : Nat} {E0 : TEnv} {n0 i : Nat}
    {c c' : Cfg} (hI : EtaFD p k arch lb nn E0 n0 i c) (hs : c' ∈ extSteps c i) (hTA : TermTyped.TidAt i c E0) :
    EtaFD p k arch lb nn E0 n0 i c' := by
  obtain ⟨th, E, hth, hT, hm, hb, hx, hl, hnn, hn, hf, hTy, hRc⟩ := hI
  have hlb : c'.lbase = c.lbase := congrArg G.lbase (gOf_ext (p := p) (k := k) (arch := arch) (j := i) hs)
  rcases TermTyped.extSteps_res hs hth with ⟨x1, n1, a1, e1, rt1, ws1, rs1, hterm, hn1, hev1, hrs1, rfl⟩ |
      ⟨x1, a1, e1, lb1, hterm, htl, rfl⟩
  · exact ⟨_, E, set_self hth, (by rw [extSteps_n hs]; exact ThInvEB_extD hn1 hterm hev1 hrs1 hT),
      by rw [gOf_ext hs]; exact hm, by rw [gOf_ext hs]; exact hb, hx, by rw [hlb]; exact hl,
      by rw [extSteps_n hs]; exact hnn, hn, hf, by rw [gOf_ext hs]; exact hTy, by rw [gOf_ext hs]; exact hRc⟩
  · obtain ⟨hbs, hbp⟩ := TermTyped.Flat.tidBox_extB hx (hTA th hth lb1 htl)
    exact ⟨_, E, set_self (tr := c.trace) hth, (by rw [extSteps_n hs]; exact ThInvEB_curD hterm hbs hbp hT),
      by rw [gOf_ext hs]; exact hm, by rw [gOf_ext hs]; exact hb, hx, by rw [hlb]; exact hl,
      by rw [extSteps_n hs]; exact hnn, hn, hf, by rw [gOf_ext hs]; exact hTy, by rw [gOf_ext hs]; exact hRc⟩

theorem eta_stepFD {p : Prog} [ProgRetIall p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    {k : Promises.Knobs} {arch : Arch} {lb nn : Nat} {E0 : TEnv} {n0 i : Nat} {c c' : Cfg}
    (hrs : TermScope.RunScope c) (hI : EtaFD p k arch lb nn E0 n0 i c) (hs : c' ∈ threadSteps p k arch c i)
    (hc : Certified p k arch c' i) : EtaFD p k arch lb nn E0 n0 i c' := by
  obtain ⟨th, E, hth, ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hRP, hDy⟩, hm, hbf, hx0, hlb, hnn0, hn0, hf0, hTy, hRc⟩ := hI
  subst hCE hlb hnn0
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  have hg := TermTyped.gOf_thread hs
  have hn : 0 < (gOf p k arch c i).n := Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth))
  have hnl : th.nalloc ≤ r.2.2.nalloc := TermPtrKey.tstep_nalloc hr
  have hnd : isDone th = false := by
    cases hd : isDone th
    · rfl
    · rw [TermStep.tstep_done hd] at hr; cases hr
  have hns := TermTyped.not_spawnT_of_steps hth hs
  have hsD : ScopeD th.σs cx th.term := by
    have h := hrs i th hth
    exact TermCertScope.scopeD_of h.ok (TermScope.Flat.scope_termVB hT hi.2.1 h.ok h.env hns)
  have hnone : (CE η).sto (freshLabel (gOf p k arch c i).lbase (gOf p k arch c i).n (gOf p k arch c i).i th.nalloc) = none :=
    (hm.2.2.2.1.1 th.nalloc (Nat.le_refl _)).1
  have hsub := TermTyped.tysOf_thread hs hth e3 hRc
  have fin : ∀ E', ThInvEB c.lbase c.n i p E' r.2.2 → MemInvB (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2) →
      ExtB (CE η) E' → FootInD c.lbase c.n i n0 E0 E' →
      TyOKE { gOf p k arch c i with tys := tysUpd (gOf p k arch c i).tys th r.2.2 } E' →
      RecFresh { gOf p k arch c i with tys := tysUpd (gOf p k arch c i).tys th r.2.2 } i r.2.2.nalloc →
      EtaFD p k arch c.lbase c.n E0 n0 i c' := by
    intro E' h1 h2 h3 h4 h5 h6
    refine ⟨r.2.2, E', e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact h1), ?_, by rw [hg]; exact hbf,
      Ext_transB hx0 h3, (threadSteps_lbase hs).1, threadSteps_n hs, Nat.le_trans hn0 hnl, h4, ?_, ?_⟩
    · rw [hg, e1, e2, MemInvB_tys]; exact h2
    · rw [hg]; exact TyOKE_mono hsub h5
    · rw [hg]
      exact RecFresh_sub (g := { gOf p k arch c i with tys := tysUpd (gOf p k arch c i).tys th r.2.2 })
        (g' := { gOf p k arch c i with tys := tysOf c' }) hsub rfl rfl h6
  -- the footprint of an `EFootPB` step on the lineage
  have footStep : ∀ η', EFootPB (gOf p k arch c i) (CE η) (CE η') (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) →
      ExtB (CE η) (CE η') ∧ FootInD c.lbase c.n i n0 E0 (CE η') := by
    intro η' hfoot
    refine ⟨Foot_extB ⟨hfoot, fun l hl => fresh_blankB hm hl⟩, fun l => ?_⟩
    rcases hfoot.2.2.1 l with h5 | ⟨⟨j, hj1, -, hj3⟩, -⟩
    · rw [h5]; exact hf0 l
    · exact .inr ⟨j, Nat.le_trans hn0 hj1, hj3⟩
  by_cases hpub : ∃ y a e, th.term = .let_ y (.publish a) e
  · obtain ⟨y, a, e, hterm⟩ := hpub
    have hpsc : PubScope cx a := TermOwnK4.pubScope_of (by rw [← hterm]; exact hsD)
    obtain ⟨-, hR⟩ := pub_stepD (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hterm hP hT hi hE htv hm
      hpsc hRP hPS hDy
    obtain ⟨E1, h1, h2, h3⟩ := hR r hr
    have hk := tyOKE_tstepB (W := fun _ => True) hn hr EFoot_reflB hTy hRc
      (hnew_none hr hRc (fun _ _ _ _ h => by rw [hterm] at h; cases h))
    rcases h3 with rfl | ⟨lab, V, hl, rfl⟩
    · exact fin _ h1 h2 (Ext_reflB (Coh_CEB η) (CohR_CEB η)) hf0 hk.1 hk.2
    · exact fin _ h1 h2 (ext_shE η lab V) (footInD_sto hf0 (shE_sto η lab V)) (TyOKE_stoD (shE_sto η lab V) hk.1) hk.2
  · have hnp : ∀ y a e, th.term ≠ .let_ y (.publish a) e := fun y a e h => hpub ⟨y, a, e, h⟩
    rcases hsD with hst | ⟨-, hcap⟩
    · by_cases hnw : ∃ x a T e, th.term = .let_ x (.new a T) e
      · obtain ⟨x, a, T, e, hterm⟩ := hnw
        obtain ⟨-, hR⟩ := tstepM_newNCB (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hterm
          (by rw [hterm] at hst; exact hst) hP hn hT hi hE htv hm hRP hPS hDy
        obtain ⟨E', hNC, -, hfoot, h1, h2⟩ := hR r hr
        have h1' := h1
        obtain ⟨ρ', η', cx', hCE', -⟩ := h1'
        subst hCE'
        obtain ⟨hext, hfi⟩ := footStep η' hfoot
        have hk := tyOKE_tstepB hn hr hfoot hTy hRc
          (TermStep.hnew_of hr hRc (show DyFr (gOf p k arch c i).p annNew (progTgts (gOf p k arch c i).p) η th.σs th.term from hDy)
            (fun k => (hE.2.1 k).1) hNC)
        exact fin _ h1 h2 hext hfi hk.1 hk.2
      · have hnn : ∀ x a T e, th.term ≠ .let_ x (.new a T) e := fun x a T e h => hnw ⟨x, a, T, e, h⟩
        obtain ⟨-, hR⟩ := tstepMF_stepB (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hP rfl hn hnd hst hT
          hi hE htv hm hbf (PAx_of_step hs hc hth) (fun _ _ _ _ _ _ h => absurd h (hnp _ _ _)) hRP hPS hSub hSig hTy
          (hDy := hDy)
        obtain ⟨E', hfoot, h1, h2⟩ := hR r hr hpa
        have h1' := h1
        obtain ⟨ρ', η', cx', hCE', -⟩ := h1'
        subst hCE'
        obtain ⟨hext, hfi⟩ := footStep η' hfoot
        have hk := tyOKE_tstepB hn hr hfoot hTy hRc (hnew_none hr hRc hnn)
        exact fin _ h1 h2 hext hfi hk.1 hk.2
    · obtain ⟨-, hR⟩ := tstep_capBD (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hP hcap hT hi hE htv
        hRP hPS hDy
      obtain ⟨h1, hsm⟩ := hR r hr
      have hk := tyOKE_tstepB (W := fun _ => True) hn hr EFoot_reflB hTy hRc
        (fun c0 t hc0 _ => by rw [hnone] at hc0; cases hc0)
      exact fin _ h1 (MemInv_sameB hm hsm) (Ext_reflB (Coh_CEB η) (CohR_CEB η)) hf0 hk.1 hk.2

theorem eta_soloFD {p : Prog} [ProgRetIall p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {lb nn : Nat} {E0 : TEnv} {n0 i : Nat}
    {c c2 : Cfg} (h : Solo p k arch i c c2) :
    Certified p k arch c2 i → TermScope.RunScope c → TermTyped.TidAt i c E0 →
    EtaFD p k arch lb nn E0 n0 i c → EtaFD p k arch lb nn E0 n0 i c2 := by
  induction h with
  | refl => exact fun _ _ _ hI => hI
  | thread hs hrest ih =>
    intro hc2 hrs hTA hI
    have hc' := certified_of_solo hrest hc2
    exact ih hc2 (TermCertScope.drf_thread hps hrs hs) (TermTyped.tidAt_thread hs hTA)
      (eta_stepFD hP hPS hSub hSig hrs hI hs hc')
  | prom a v w hw hrest ih =>
    intro hc2 hrs hTA hI
    exact ih hc2 (TermCertScope.drf_prom hrs) (TermTyped.tidAt_prom hTA) (eta_promFD hI)
  | ext hs hrest ih =>
    intro hc2 hrs hTA hI
    exact ih hc2 (TermCertScope.drf_ext hrs hs)
      (TermTyped.tidAt_solo (p := p) (k := k) (arch := arch) (.ext hs (.refl _)) hTA) (eta_extFD hI hs hTA)

/-- `publish_own_cellB` for any continuation predicate (copy of EtaF `publish_own_cellK`). -/
theorem publish_own_cellKD {p : Prog} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {x : String} {a : At}
    {e : Expr} {rt : Ty} {ws : List Word} {ad : Address} {K : TEnv → List Word → Prop}
    (hT : Typed p cx th.term) (hi : FInvB glb gnum gi ρ η th.σs K cx th.env)
    (hterm : th.term = .let_ x (.publish a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) : ∃ c, η.sto ad.label = some c ∧ c.owner = some η.tid := by
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu, -, -⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) ∧
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind x (.ptr .pub u) = .ok _ := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨-, rt', ws', hea', hv, -⟩ := use_FInvB (bkG := False) hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VRF, VRb2] at hv
    obtain ⟨ad', c, hws', -, hsto, -, hmode, -⟩ := hv
    rw [hws] at hws'
    simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
    subst hws'
    exact ⟨c, hsto, hmode⟩
  | publishBuf hu hsh hb =>
    obtain ⟨n, k, u, c₁, hu, -, -⟩ : ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) ∧
        Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true ∧
        c₁.bind x (.refine (.loc .pub (.array n u)) (.ini k)) = .ok _ := ⟨_, _, _, _, hu, hsh, hb⟩
    obtain ⟨-, rb, wsb, hea', hvb, -⟩ := use_FInvB (bkG := False) hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, -⟩ := hvb
    rcases hv with ⟨hnull, -, -⟩ | ⟨ad', c, U, hws', hsto, -, -, hmode, -⟩
    · rw [hws] at hnull; simp at hnull
    · rw [hws] at hws'
      simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
      subst hws'
      exact ⟨c, hsto, hmode⟩

/-- **The fresh/cut split of a window publish** on EtaFD. -/
theorem pub_splitFD {p : Prog} {k : Promises.Knobs} {arch : Arch} {lb nn : Nat} {E0 : TEnv} {n0 i : Nat} {c1 : Cfg}
    {th1 : TTh} {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word} {ad : Address}
    (hI : EtaFD p k arch lb nn E0 n0 i c1) (hth1 : c1.ths[i]? = some th1) (hterm : th1.term = .let_ y (.publish a) e)
    (hea : evalAt th1.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0]) :
    E0.sto ad.label ≠ none ∨ ∃ j, n0 ≤ j ∧ ad.label = freshLabel lb nn i j := by
  obtain ⟨th, E, hth, ⟨ρ, η, cx, hCE, -, hT, -, hi, -⟩, -, -, -, -, -, -, hf, -⟩ := hI
  rw [hth1] at hth
  cases hth
  obtain ⟨cl, hcl, -⟩ := publish_own_cellKD hT hi hterm hea hws
  rcases hf ad.label with h | h
  · left
    rw [← h, ← hCE]
    show η.sto ad.label ≠ none
    rw [hcl]; exact fun h0 => by cases h0
  · exact .inr h

/-- **The seed at a `SysInvN` base** (O1: every conjunct from `SysInvN`/`ThSysAt` at the base). -/
theorem seedFD {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg0 : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {S0 : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg0 Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg0 (Tot i) (HP i) HS (cr i) (db i) S0) :
    EtaFD p k arch c.lbase c.n (Cut Eg0 i S0) th.nalloc i c := by
  have hB0 : FlatAnchor.ContB c.lbase c.n i p th (Cut Eg0 i S0) := ContAnchor.contB_of hth hS.2.2.1 hinv.rle
  have hB := FlatAnchor.base_shape hinv.clo hS hB0 (FlatAnchor.rsFresh_of hinv hth) hinv.rle
  have hXB := FlatWinStart.ext_REB hB.1
  obtain ⟨⟨ρ0, η0, cx0, Rf0, Rs0, hCE0, hE0, hT0, htv0, hFI0, -, hpw0, hDy0⟩, hmB, -⟩ := hB
  have hTR := hinv.tyRec hth S0
  exact ⟨th, Cut Eg0 i S0, hth, ⟨ρ0, η0, cx0, hCE0, hE0, hT0.1, htv0, finv_ofB htv0 hFI0, hpw0, hDy0⟩, hmB, hinv.bf,
    hXB, rfl, rfl, Nat.le_refl _, footInD_refl, hTR.1, hTR.2⟩

end EtaDyFr
