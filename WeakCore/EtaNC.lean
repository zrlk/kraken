import WeakCore.EtaP
import WeakCore.WinPremises
import WeakCore.TermPtrKey
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! **EtaNC** ((A) reroute, droppable port): EtaFD `tstepM_newNCB` on the N layer (ResumeBN/ThInvEBN with
DyFr, `EFootCN`): a `new` step with its `NewCellSto` output, for the η lineage's TyOKE transfer. -/
namespace CertWinProof
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
theorem tstepM_newNCN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {T : Option Ty} {e : Expr}
    (hterm : th.term = .let_ x (.new a T) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPwN th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ E', NewCellSto g ρ η th E' ∧ FreshArr g ρ η th E' r ∧ EFootCN g th (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧
      ThInvEBN g.lbase g.n g.i p E' r.2.2 ∧ MemInvB g E' (stOf r.1 r.2.1 r.2.2) := by
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
      cnE <| EFoot_freshB rfl rfl rfl rfl (lt_of_eq_succ hna) (fun l => allocE_sto_cases ⟨Clo_cl (fun k => (hE.2.1 k).1) ρ tv,
        mg_cl (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.2.2.2.2.2.2.1) tv 0 0 (use_mg hu htv),
        noIallV_cl (WitAF.ni hi.2.2.2.2.2.2.1) tv 0 0 (hniA tv _ hu), trivial⟩ (alloc_newT hal hwcT) (alloc_undefT hal hwcT) l) (fun _ => .inl rfl)
        (fun _ => ⟨Nat.le_refl _, .inl rfl⟩),
      ⟨ρ, η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto, c', rfl,
        ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPwN_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, ?_⟩
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

end CertWinProof
