import WeakCore.TermOwnX2
import WeakCore.TermPubW
import WeakCore.TermOwnHeldQ
import WeakCore.TermIall

/-!
# TermOwnK3 (own-key layer, package): buffer ops and allocation

Package K3 of `OwnXStepPkg` (`opPkg = 3`): `bufInit`, `xchgAt`, `xchgAtF`, `stl`, `stlw`, `ldl`,
`ldlw`, `new`, `newBuf`.  Holding helpers and the dispatcher: `TermOwnHeldQ`.
Copied lemmas (route (b), design decision) carry a header naming their source.
-/

namespace TermOwnK3
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Copied per-op lemmas (route (b)) -/

/-- (frontier) An old value read at an own-key-free, `∀`-free cell component carries a resource
without own keys. -/
theorem oldValF {ρ : Nat → Nat} {η : TEnv} {u ru T : Ty} {o : Nat} {ws : List Word}
    (hco : Coh η) (hcr : CohR η) (hni : noIallV T = true) (hno : Ty.noOwnIn [] T = true)
    (hat : AtOff T o (cl ρ η.wit 0 0 u)) (hv : VR ρ η u (shp ru) ws) :
    ∃ R, VRR ρ η u (shp ru) ws R ∧ ∀ l, R (.own l) = 0 := by
  have hc := (VR_close hco ρ u [] 0 ρ (fun _ => 0) (shp ru) ws (fun _ => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  obtain ⟨R, hR⟩ := VR_VRR _ (TermIall.noIallV_AtOff hat hni) (RInv_CE η) hc
  exact ⟨R, (VRR_close hco hcr ρ u [] 0 ρ (fun _ => 0) (shp ru) ws R (fun _ => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).2 hR,
    fun l => TermBlkZ.VRR_own_zero l _ [] (CE η) _ _ _ R (noOwn_AtOff hat hno)
      (fun _ _ _ _ h => (h : False).elim) (fun _ _ _ _ h => (h : False).elim) hR⟩

/-- (frontier) A private label is not the frontier target. -/
theorem privOff {E : TEnv} {l : AllocLabel} {a : Address} {f : Ts} (hl : Priv E l) (e : l = a.label)
    (hf : E.pfr a.label = some f) : False := by
  have h2 := hl.2
  rw [e, hf] at h2
  cases h2

-- copied from TermStep.tstepMR_ldl
theorem stepK3_ldl {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.ldl b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hi0 := hi.1
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldl hp hbuf hlo hint hlt hltk hb =>
  obtain ⟨t, u, n, k, j, q, hp, hbuf, hlo, hint, hlt, hltk, hb⟩ : ∃ t u n k j q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧ cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb hlt hltk
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_num hi0.2.1 hpi hti
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi0.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi0.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewN (ev ρ j / w.lanes) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoad (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).filterMap
        fun (s1, old) => (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (ev ρ j % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hni, addrOf, hwv, hbe, lanesOf]
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨CE η, Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv',
    bindR0 hb hi (fix_VR sg w _) (fix_Lay _ sg w _) trivial, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
    MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1),
    memHeldOn_eqs hH f1 f4, hnie, hx, Nat.le_refl _, anchStep_same (bumpIf_nb hterm)⟩

-- copied from TermStep.tstepMR_ldlw
theorem stepK3_ldlw {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.ldlw b wi jl) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hi0 := hi.1
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldlw hp hbuf hlo hint hlt hltk hpj hij hb =>
  obtain ⟨t, u, n, k, jw, tj, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩ : ∃ t u n k jw tj q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_num hi0.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_int hi0.2.1 hpj hoj
  have hJ := hlt ρ hi0.1
  have hJk := hltk ρ hi0.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewN (ev ρ jw) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoad (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).filterMap fun (s1, old) =>
        (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (m % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hni, hnj, addrOf, hwv, hbe, lanesOf]
  -- every load reads a number (`VR` at `lanes`)
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨CE η, Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv',
    bindR0 hb hi (fix_VR sg w _) (fix_Lay _ sg w _) trivial, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
    MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1),
    memHeldOn_eqs hH f1 f4, hnie, hx, Nat.le_refl _, anchStep_same (bumpIf_nb hterm)⟩

-- copied from TermPlant.tstepMR_xchgAtN
theorem stepK3_xchgAt {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.xchgAt b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, n, k, j, tv, c₁, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u ∧ c₁.bind x u = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, hini, hsku, hsig, htb, -⟩ :=
    slot_view hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoad (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 s1).map fun s2 => (s2, ur, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInv g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    obtain ⟨Ro, hvold, hRo⟩ := oldValF hE.2.1 hE.2.2 (hnie _ _ hsto) (MemInv_noOwnT hm hsto hpfN) hat hvr
    have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvold hlay
    refine ⟨CE η, Rr + Ro + Rs, HP, ⟨ρ, η, c', Rr + Ro, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_storeAt (a := (offs ad (ev ρ j * nWords us))) hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
      memHeldOn_store (s' := s2) (a := offs ad (ev ρ j * nWords us)) (memHeldOn_eqs hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLt hm1') hs2,
      hnie, hx, ?_, anchStep_same (bumpIf_nb hterm)⟩
    have h1 := hle (.own xl)
    have h3 := hRo xl
    simp only [Res.add_apply] at h1 ⊢
    omega
  | none =>
  have hnv := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hown hpfN)
  obtain ⟨vq, Rq, R2, H0, hRe, hvql, hvqlat, hvqR, hput0⟩ := heldStoreAtP (a := offs ad (ev ρ j * nWords us)) hm hH (Priv_of hsto hown hpfN) hsto hown hnv (OwnOKPF_cellP hm.2.1 hsto hown hpfN) hat hini hna hvalR hwU hlen
  have hWold : WLe vq old := (loadUnits_latestPA hvql hvqlat h1 hp1).1
  have hvold := oldValR hE.2.1 hE.2.2 hsig (VRR_up _ _ _ _ _ hWold hvqR)
  have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvold hlay
  refine ⟨CE η, Rr + Rq + Rs, R2 + H0, ⟨ρ, η, c', Rr + Rq, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
    MemInv_storeAt (a := (offs ad (ev ρ j * nWords us))) hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
    hput0 g.k g.arch w false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_same (bumpIf_nb hterm)⟩
  have h1 := hle (.own xl)
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply] at h1 h2 ⊢
  omega

-- copied from TermPlant.tstepMR_xchgAtFN
theorem stepK3_xchgAtF {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {q : List Nat} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.xchgAtF b i q v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAtF hp hbuf hct hop _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, c, n, k, j, tv, c₁, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u c n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧
      IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv c ∧ c₁.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK c = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, -, hsku, hsig, htbu, hiniF⟩ :=
    slot_view hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct htbu
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  have hiniC := hiniF o _ hato
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  obtain ⟨cs, hcs, -, hld, hstw⟩ := locLoad (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat' hiniC hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2 hco))
  obtain ⟨hval, hlen⟩ := ownStoreVal hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsgc hcs
  have hwUA : accs (cl ρ η.wit 0 0 c) = some cs := (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2 hco)).symm.trans hcs
  have hwU : wc (cl ρ η.wit 0 0 c) = some (nWords cs) := by rw [← wc_of_sig hsgc]; simp [wc, hcs]
  have hvalR := storeValR hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us + o)) false cs wsv 0 s1).map fun s2 => (s2, cR, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus, hco, hcs]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInv g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    obtain ⟨Ro, hvold, hRo⟩ := oldValF hE.2.1 hE.2.2 (hnie _ _ hsto) (MemInv_noOwnT hm hsto hpfN) hat' hvr
    have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvold hlay
    refine ⟨CE η, Rr + Ro + Rs, HP, ⟨ρ, η, c', Rr + Ro, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_storeAt (a := (offs ad (ev ρ j * nWords us + o))) hm1' hsto hown hat' hiniC hna hval hwUA hlen s2 hs2,
      memHeldOn_store (s' := s2) (a := offs ad (ev ρ j * nWords us + o)) (memHeldOn_eqs hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLt hm1') hs2,
      hnie, hx, ?_, anchStep_same (bumpIf_nb hterm)⟩
    have h1 := hle (.own xl)
    have h3 := hRo xl
    simp only [Res.add_apply] at h1 ⊢
    omega
  | none =>
  have hnv := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hown hpfN)
  obtain ⟨vq, Rq, R2, H0, hRe, hvql, hvqlat, hvqR, hput0⟩ :=
    heldStoreAtP (a := offs ad (ev ρ j * nWords us + o)) hm hH (Priv_of hsto hown hpfN) hsto hown hnv (OwnOKPF_cellP hm.2.1 hsto hown hpfN) hat' hiniC hna hvalR hwU hlen
  have hWold : WLe vq old := (loadUnits_latestPA hvql hvqlat h1 hp1).1
  have hvold := oldValR hE.2.1 hE.2.2 hsgc (VRR_up _ _ _ _ _ hWold hvqR)
  have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvold hlay
  refine ⟨CE η, Rr + Rq + Rs, R2 + H0, ⟨ρ, η, c', Rr + Rq, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
    MemInv_storeAt (a := (offs ad (ev ρ j * nWords us + o))) hm1' hsto hown hat' hiniC hna hval hwUA hlen s2 hs2,
    hput0 g.k g.arch w false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_same (bumpIf_nb hterm)⟩
  have h1 := hle (.own xl)
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply] at h1 h2 ⊢
  omega

-- copied from TermPlant.tstepMR_stlwN
theorem stepK3_stlw {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.stlw b wi jl v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk hpj hij hpv hfx hb =>
  obtain ⟨t, u, n, k, jw, tj, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩ :
      ∃ t u n k jw tj tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩
  have hi0 := hi.1
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_num hi0.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_int hi0.2.1 hpj hoj
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VR hi0.2.1 hpv
  simp only [VR] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ := hlt ρ hi0.1
  have hJk := hltk ρ hi0.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewN (ev ρ jw) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoad (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInv g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ jw)) false [.one]
            [cst (.num (setLaneN w y (m % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hev, hni, hnj, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨-, -, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    refine ⟨CE η, Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_storeAt (a := offs ad (ev ρ jw)) hm1' hsto hmode hat hini hna
        (lanes_EnvVal sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
      memHeldOn_store (s' := s2) (a := offs ad (ev ρ jw)) (memHeldOn_eqs hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLt hm1') hs2,
      hnie, hx, ?_, anchStep_same (bumpIf_nb hterm)⟩
    simp only [Res.add_apply]
    omega
  | none =>
  have hnvP := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hmode hpfN)
  obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput0⟩ := heldStoreAtP (a := offs ad (ev ρ jw)) hm hH (Priv_of hsto hmode hpfN) hsto hmode hnvP (OwnOKPF_cellP hm.2.1 hsto hmode hpfN) hat hini hna
    (lanes_EnvValR sg w (setLaneN w y (m % w.lanes) yv)) hwU (by simp [nWords, Acc.size])
  have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine ⟨CE η, Rf + Rs, R2 + H0, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
    MemInv_storeAt (a := offs ad (ev ρ jw)) hm1' hsto hmode hat hini hna
      (lanes_EnvVal sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
    hput0 g.k g.arch pw false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_same (bumpIf_nb hterm)⟩
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply, Res.zero_apply] at h2 ⊢
  omega

-- copied from TermPlant.tstepMR_stlN
theorem stepK3_stl {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.stl b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stl hp hbuf hlo hint hlt hltk hpv hfx hb =>
  obtain ⟨t, u, n, k, j, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩ : ∃ t u n k j tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩
  have hi0 := hi.1
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0 hlt hltk
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_num hi0.2.1 hpi hti
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VR hi0.2.1 hpv
  simp only [VR] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi0.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi0.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewN (ev ρ j / w.lanes) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoad (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2
        (accs_rtW hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lyt hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInv g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one]
            [cst (.num (setLaneN w y (ev ρ j % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hni, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨-, -, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    refine ⟨CE η, Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_storeAt (a := offs ad (ev ρ j / w.lanes)) hm1' hsto hmode hat hini hna
        (lanes_EnvVal sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
      memHeldOn_store (s' := s2) (a := offs ad (ev ρ j / w.lanes)) (memHeldOn_eqs hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLt hm1') hs2,
      hnie, hx, ?_, anchStep_same (bumpIf_nb hterm)⟩
    simp only [Res.add_apply]
    omega
  | none =>
  have hnvP := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hmode hpfN)
  obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput0⟩ := heldStoreAtP (a := offs ad (ev ρ j / w.lanes)) hm hH (Priv_of hsto hmode hpfN) hsto hmode hnvP (OwnOKPF_cellP hm.2.1 hsto hmode hpfN)
    hat hini hna (lanes_EnvValR sg w (setLaneN w y (ev ρ j % w.lanes) yv)) hwU (by simp [nWords, Acc.size])
  have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine ⟨CE η, Rf + Rs, R2 + H0, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
    MemInv_storeAt (a := offs ad (ev ρ j / w.lanes)) hm1' hsto hmode hat hini hna
      (lanes_EnvVal sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
    hput0 g.k g.arch pw false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_same (bumpIf_nb hterm)⟩
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply, Res.zero_apply] at h2 ⊢
  omega

-- copied from TermStep.heldBufInit; holding on `Q` at `ad.label ∈ Q`
theorem heldBufInitP {Q : AllocLabel → Prop} {g : G} {E E' : TEnv} {s : St} {H : Res} {ad : Address} {c : Cell} {N j : Nat} {e : Ty}
    {us : List Acc} {ws : List Word} {pw : Word} {Rv : Res}
    (hm : MemInv g E s) (hH : MemHeldOn Q E s H) (hql : Q ad.label) (hsto : E.sto ad.label = some c) (_hown : c.owner = some E.tid)
    (hnv : NVP E s ad.label)
    (hcP : ∃ vals, CellOK E (E.rc ad.label) c.ty vals ∧
      ∀ o v, vals[o]? = some v → LatestP s.mem s.promises s.vs.coh ⟨ad.label, o⟩ v)
    (hat : AtOff c.ty ad.offset (.array (.lit N) e)) (hini : IniAt E.ini c ad (.array (.lit N) e))
    (hwe : wc e = some (nWords us)) (hj : j < N) (hjn : j ≤ E.ini ad.label)
    (hq : EnvValR E e ws Rv) (hlen : ws.length = nWords us)
    (hp : E.prog = E'.prog) (ht : E.tid = E'.tid) (hs : E'.sto = E.sto)
    (hil : E'.ini ad.label = max (E.ini ad.label) (j + 1)) (hio : ∀ l', l' ≠ ad.label → E'.ini l' = E.ini l')
    (hpf : E'.pfr = E.pfr) (hbx : ∀ l B, E.box l = some B → E'.box l = some B)
    (hq' : ∀ o, ¬ PredU E' ⟨ad.label, o⟩) (hrio : ∀ l', l' ≠ ad.label → E'.rini l' = E.rini l')
    (hjr : j ≤ E.rc ad.label) (hrc' : E'.rc ad.label = max (E.rc ad.label) (j + 1))
    (hfp : E'.fp = E.fp := by first | rfl | assumption)
    (hri : ∀ l, E.rini l ≤ E'.rini l := by rini_le) :
    ∃ H2, H2 ≤ Rv + H ∧
      ∀ s', s' ∈ storeUnits g.k g.arch pw (offs ad (j * nWords us)) false us ws 0 s → MemHeldOn Q E' s' H2 := by
  obtain ⟨vals, hcell, hlat⟩ := hcP
  obtain ⟨valsm, hW, hP⟩ := own_msgWordsN (E := E) hnv vals hlat
  obtain ⟨R0, H0, rfl, hent0, hX⟩ := memHeldOn_focus hH hql
  have hcR : CellOKR E (E.ini ad.label) (E.rc ad.label) c.ty valsm R0 :=
    HeldEntry_cell hent0 hsto hcell hW.length.symm (fun o w h => (hP o w h).2)
  obtain ⟨N', e', usB, Rl, hT, husB, hn, hvl, hRl, hR, hslots⟩ : BufOKR E (E.ini ad.label) (E.rc ad.label) c.ty valsm R0 := by
    rcases hcR with ⟨hwc, hv⟩ | hb
    · exfalso
      obtain ⟨n', _, _, hwn, -⟩ := VRR_at E.unsee hat hv.1 hwc
      simp [wc, accs] at hwn
    · exact hb
  have hoff : ad.offset = 0 := by
    rcases hini N' e' hT with ⟨hUc, h0⟩ | ⟨us', j', o, hus', -, -, hato⟩
    · exact h0.symm
    · exact (accs_AtOff hato (by rw [hus']; simp) (by simp [accs])).elim
  have hUc : Ty.array (.lit N) e = c.ty := by
    rcases hini N' e' hT with ⟨hUc, -⟩ | ⟨us', j', o, hus', -, -, hato⟩
    · exact hUc
    · exact (accs_AtOff hato (by rw [hus']; simp) (by simp [accs])).elim
  have hb0 : BufOKR E (E.ini ad.label) (E.rc ad.label) (.array (.lit N) e) valsm R0 := by
    rw [hUc]; exact ⟨N', e', usB, Rl, hT, husB, hn, hvl, hRl, hR, hslots⟩
  rw [hT] at hUc
  simp only [Ty.array.injEq, Idx.lit.injEq] at hUc
  obtain ⟨hN, he⟩ := hUc
  subst hN; subst he
  have hnu : nWords usB = nWords us := by rw [wc_of_accs husB] at hwe; exact Option.some.inj hwe
  have hst := hq.store hm.2.2.2.2.1
  obtain ⟨R', hR'le, hb'⟩ := BufOKR_put hb0 husB hj hjn hjr hst (by rw [List.length_map, hlen, hnu])
  rw [hnu, ← hil, ← hrc'] at hb'
  refine ⟨R' + H0, Res.le_def.2 fun k => ?_, fun s' hs' => ?_⟩
  · have h1 := hR'le k
    simp only [Res.add_apply] at h1 ⊢; omega
  have had : offs ad (j * nWords us) = ⟨ad.label, j * nWords us⟩ := by
    simp only [offs, hoff, Nat.zero_add]
  rw [had] at hs'
  obtain ⟨g2, g3⟩ := storeUnits_latP (a := ⟨ad.label, j * nWords us⟩) us ws 0 s s.vs.vRelSt hm.2.2.1
    hm.2.2.2.2.2.2.2.2.2.2.1 (Nat.le_refl _) s' hs'
  have hlenv : j * nWords us + nWords us ≤ valsm.length := by
    have hm := Nat.mul_le_mul_right (nWords us) (show j + 1 ≤ N by omega)
    rw [Nat.succ_mul] at hm; rw [hvl, hnu]; omega
  have htail : ∀ i : Nat, i < nWords us → TailP s (offs ⟨ad.label, j * nWords us⟩ (0 + i)) := fun i hi => by
    have hlt : j * nWords us + i < vals.length := by have := hW.length; omega
    have hv := hlat (j * nWords us + i) (vals[j * nWords us + i]'hlt) (List.getElem?_eq_getElem hlt)
    have e : offs ⟨ad.label, j * nWords us⟩ (0 + i) = ⟨ad.label, j * nWords us + i⟩ := by simp [offs]
    rw [e]; exact fun t m ht hm hl => hv.2.2 t m ht hm hl
  have hlat' := splice_latestP (a := ⟨ad.label, j * nWords us⟩) hlen hlenv (fun o v h => (hP o v h).1)
    (g2 htail) g3
  have hsto' : E'.sto ad.label = some c := by rw [hs]; exact hsto
  have hile : ∀ l', E.ini l' ≤ E'.ini l' := fun l' => by
    by_cases h : l' = ad.label
    · subst h; rw [hil]; exact Nat.le_max_left _ _
    · rw [hio l' h]; exact Nat.le_refl _
  have hmono : ∀ {U : Ty} {vs : List Word} {Rq : Res}, ValOfR E U vs Rq → ValOfR E' U vs Rq :=
    fun h => ValOfR_mono hp ht (fun l c h => by rw [hs]; exact h) hile h (fun l f h => by rw [hpf]; exact h) hbx
  have hent : HeldEntry E' s' ad.label R' :=
    HeldEntry_ownN hsto' (NVP_env (NVP_store hnv hm.2.2.1 hs')
      (fun o h => (VisU_congr (by rw [hs]) ht.symm (by rw [hpf])).1 h)
      (fun h => (Vis_congr (by rw [hs]) ht.symm (by rw [hpf])).1 h) hfp hq') hlat' (Or.inr (by rw [hT]; exact BufOKR_map hmono hb'))
  have hX' := memHeldOn_tr (Q' := fun l' => Q l' ∧ l' ≠ ad.label) (E' := E') (s' := s') hX (fun _ => Iff.rfl)
    (fun l' _ => by rw [hs]) (fun l' h => hio l' h.2) (fun l' h => hrio l' h.2) (fun l' _ => by rw [hpf]) ht.symm hfp
    (fun l' h o w hl => LatestNP_growsAtF (storeUnits_growsF us ws 0 s s' hs').1
      (storeUnits_growsF us ws 0 s s' hs').2.1 (storeUnits_fulL hm.2.2.1 hs') h.2 hl) hmono
  exact memHeldOn_unfocus hX' hent hql

/-- (frontier) `bufInit` at a frontier cell keeps the private holding (environment bumped off the
private cells). -/
theorem heldBufInitF {g : G} {E E' : TEnv} {s s' : St} {H : Res} {ad : Address} {f : Ts}
    {k : Promises.Knobs} {arch : Arch} {pw : Word} {o : Nat} {us : List Acc} {ws : List Word}
    (hm : MemInv g E s) (hH : MemHeldP E s H) (hf : E.pfr ad.label = some f)
    (hp : E.prog = E'.prog) (ht : E.tid = E'.tid) (hs : E'.sto = E.sto)
    (hio : ∀ l', l' ≠ ad.label → E'.ini l' = E.ini l') (hrio : ∀ l', l' ≠ ad.label → E'.rini l' = E.rini l')
    (hpf : E'.pfr = E.pfr) (hbx : ∀ l B, E.box l = some B → E'.box l = some B) (hfp : E'.fp = E.fp)
    (hile : ∀ l, E.ini l ≤ E'.ini l) (hri : ∀ l, E.rini l ≤ E'.rini l)
    (hs' : s' ∈ storeUnits k arch pw (offs ad o) false us ws 0 s) : MemHeldP E' s' H := by
  have hQ : ∀ l, Priv E' l ↔ Priv E l := fun l => by
    unfold Priv OwnL; rw [hs, hpf, ht]
  exact memHeldOn_tr (Q' := Priv E') (E' := E') (s' := s') hH hQ
    (fun l' _ => by rw [hs]) (fun l' h => hio l' (fun e => privOff h e hf))
    (fun l' h => hrio l' (fun e => privOff h e hf)) (fun l' _ => by rw [hpf]) ht.symm hfp
    (fun l' h o w hl => LatestNP_growsAtF (storeUnits_growsF us ws 0 s s' hs').1
      (storeUnits_growsF us ws 0 s s' hs').2.1 (storeUnits_fulL hm.2.2.1 hs')
      (fun e => privOff (a := ad) h (e.trans rfl) hf) hl)
    (fun h => ValOfR_mono hp ht (fun l c h => by rw [hs]; exact h) hile h (fun l f h => by rw [hpf]; exact h) hbx hri)

-- copied from TermPlant.tstepMR_bufInitN
theorem stepK3_bufInit {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.bufInit b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hxl : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | bufInit hu hbuf hint heq hlt hu2 hsub hb =>
  obtain ⟨t, tv, u, n, k, j, c₁, c₂, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩ : ∃ t tv u n k j c₁ c₂,
      cx.use b = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx c₁ i j ∧ EqI c₁ j k ∧
      LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u ∧
      c₂.bind x (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1)))) = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩
  have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
    unfold bufOf at hbuf; split at hbuf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
      obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
    · simp at hbuf
  subst ht
  have htu := use_TvOK hu htv
  obtain ⟨rb, wsb, Rb, Rr1, hea, hvb, hlb, hvrb, hi1, hle1⟩ := useR hu hi hE.2.2
  have hRb := VRR_buf_R hbuf hvrb
  obtain ⟨rv, wsv, Rv, Rr2, hev, hvv, hlv, hvrv, hi2, hle2⟩ := useR hu2 hi1 hE.2.2
  have hJK : ev ρ j = ev ρ k := heq ρ hi1.1.1
  have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1.1
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VR hi1.1.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intS hti hvi)
  have hvb0 := hvb
  simp only [VR] at hvb
  obtain ⟨hv, hir⟩ := hvb
  rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, hmode, hini0⟩
  · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
    simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
    omega
  obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
  obtain ⟨w, rfl, hwv⟩ := map_singleton hws
  have hKi : ev ρ k ≤ η.ini ad.label := by
    simp only [IniR] at hir; exact Nat.le_trans (hir ad (by simp [hwv])) (TEnv.selIni_le_ini _ _ _)
  have hKm : ev ρ k ≤ η.rc ad.label := by
    simp only [IniR] at hir; have h := hir ad (by simp [hwv]); rw [TEnv.selIni_loc] at h; exact h
  have hat := hat0
  have hini := hini0
  simp only [cl, clI_zero] at hat hini
  have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
    rw [hlb.2.1]; rfl
  obtain ⟨μr, nr, ur, ψ, rfl, -, hsu⟩ := buf_runtime' hs'
  have htb1 : tb c₁.ke.length u = true := by
    have h := htu.2.1
    rw [← htu.2.2] at h
    simp [tb] at h
    exact h
  have ho : c₁.opaqueOK u = true :=
    sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu2).1)
  have hsig : sig ur = sig (cl ρ η.wit 0 0 u) := by
    have e1 : sig ur = sig (close th.σs u) := sig_of_eskel hsu
    rw [e1]; exact sig_WitL hi1.1.2.2.2.1 ρ ho (lt_of_guardT htb1 hi1.1.2.2.2.2.1)
  obtain ⟨us0, hus0⟩ : ∃ us, accs (cl ρ η.wit 0 0 u) = some us := by
    rcases AtOff_lay hat with h | ⟨n', e', he', h⟩
    · simp [accs] at h
    · simp only [Ty.array.injEq] at he'; rw [he'.2]
      exact Option.ne_none_iff_exists'.1 h
  obtain ⟨us, hus⟩ : ∃ us, accs ur = some us := by
    have : wc ur ≠ none := by rw [wc_of_sig hsig]; simp [wc, hus0]
    cases h : accs ur with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have hweA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtW hE.2.1 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 ho htb1 (buf_lyt hlb.2.2.2.2 rfl).2).symm.trans hus
  have hwe : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨hval, hlen⟩ :=
    ownStoreVal (cx := c₁) hE.2.1 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 hi2.1.1 hsub ho htb1 hvv hlv hsig hus
  have hvalR := storeValR (cx := c₁) hE.2.1 hE.2.2 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 hi2.1.1 hsub ho htb1
    hvrv hlv hval.2
  let ini' := bumpIni η.ini ad.label (ev ρ j + 1)
  let rini' := bumpIni η.rini ad.label (ev ρ j + 1)
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  have hile : ∀ l, η.ini l ≤ ini' l := bumpIni_le η.ini ad.label (ev ρ j + 1)
  have hx : Ext η (η.withSto η.sto ini' (Ri := rini')) := Ext_withSto hE.2.1 (fun l c h => h) hile (Ri := rini') (hRi := hri')
  let rtR : Ty := Ty.refine (Ty.loc μr (Ty.array nr ur)) (Pred.ini (Idx.lit (ev ρ j + 1)))
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, rtR, [w]) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, numOf, hwi, addrOf, hwv, bufElem, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpa
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hvr : VR ρ (η.withSto η.sto ini' (Ri := rini')) (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      (shp rtR) [w] := by
    have h1 := VR_ext hE.2.1 hx hvb0
    simp only [VR] at h1 ⊢
    refine ⟨h1.1, fun a ha => ?_⟩
    have hav : a = ad := by simp [hwv] at ha; exact ha.symm
    subst hav
    show ev ρ (.add k (.lit 1)) ≤ min (bumpIni η.ini a.label (ev ρ j + 1) a.label)
      (bumpIni η.rini a.label (ev ρ j + 1) a.label)
    rw [bumpIni_self, bumpIni_self]; simp [ev]; omega
  have hlay : Lay th.σs (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      rtR [w] := Lay_repred hlb
  have hE' : EnvOK p (η.withSto η.sto ini' (Ri := rini')) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
  have hfr := bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi2) (RLink_of hE'.2.1 hE'.2.2) (VRR_ofVR_reflocW hvr) hlay
  rw [← hRb] at hfr
  have hAS : ∀ s2, AnchStep g th (CE η) (CE (η.withSto η.sto ini' (Ri := rini'))) (stOf mem pairs th) s2 :=
    fun _ => anchStep_gen (ext_CE hx)
      (bufBump hterm hea hwv hei (by simp [numOf, hwi])
        (show ev ρ j + 1 ≤ bumpIni η.ini ad.label (ev ρ j + 1) ad.label by rw [bumpIni_self]; exact Nat.le_max_right _ _)
        (show ev ρ j + 1 ≤ bumpIni η.rini ad.label (ev ρ j + 1) ad.label by rw [bumpIni_self]; exact Nat.le_max_right _ _))
      (fun _ _ h _ => h) (fun l _ => bumpIni_iniLe η.ini η.rini ad.label (ev ρ j + 1) l)
      (fun _ h0 hl => absurd h0 hl)
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    refine ⟨CE (η.withSto η.sto ini' (Ri := rini')), Rr2 + Rb + Rs, HP,
      ⟨ρ, η.withSto η.sto ini' (Ri := rini'), c', Rr2 + Rb, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_bufInit (E := CE η) (E' := CE (η.withSto η.sto ini' (Ri := rini'))) hm hsto hmode hat hini hweA
        (by omega) (show ev ρ j ≤ η.rc ad.label by omega) hval hlen rfl rfl rfl (bumpIni_self _ _ _)
        (fun l' h => bumpIni_other _ _ _ l' h) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl rfl (fun _ _ h => h) rfl (fun l => hri' l) s' hs' hpa,
      heldBufInitF (E' := CE (η.withSto η.sto ini' (Ri := rini'))) hm hH hpfN rfl rfl rfl
        (fun l' h => bumpIni_other _ _ _ l' h) (fun l' h => bumpIni_other _ _ _ l' h) rfl (fun _ _ h => h) rfl
        hile hri' hs', hnie, hxl, ?_, hAS _⟩
    have h1 := hle1 (.own xl)
    have h2 := hle2 (.own xl)
    simp only [Res.add_apply] at h1 h2 ⊢
    omega
  | none =>
  have hnv := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hmode hpfN)
  obtain ⟨H2, hH2, hput⟩ := heldBufInitP (E := CE η) (E' := CE (η.withSto η.sto ini' (Ri := rini'))) (pw := w) (g := g)
    hm hH (Priv_of hsto hmode hpfN) hsto hmode hnv (OwnOKPF_cellP hm.2.1 hsto hmode hpfN) hat (IniAt_mono (modeIni_le_ini _ _ _) hini) hwe (by omega) (show ev ρ j ≤ η.ini ad.label by omega) hvalR hlen
    rfl rfl rfl (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl (fun _ _ h => h)
    (fun o hq => hnv.2.2 o (PredU_bump (E' := CE (η.withSto η.sto ini' (Ri := rini'))) (k := ev ρ j + 1) rfl rfl rfl (bumpIni_self _ _ _) (by
      show min (bumpIni η.ini ad.label (ev ρ j + 1) ad.label) (bumpIni η.rini ad.label (ev ρ j + 1) ad.label) =
        max (min (η.ini ad.label) (η.rini ad.label)) (ev ρ j + 1)
      rw [bumpIni_self, bumpIni_self]; omega) hq)) (fun l' h => bumpIni_other _ _ _ l' h)
    (show ev ρ j ≤ min (η.ini ad.label) (η.rini ad.label) by have h := hKm; unfold TEnv.rc at h; omega)
    (show min (bumpIni η.ini ad.label (ev ρ j + 1) ad.label) (bumpIni η.rini ad.label (ev ρ j + 1) ad.label) =
        max (min (η.ini ad.label) (η.rini ad.label)) (ev ρ j + 1) by
      rw [bumpIni_self, bumpIni_self]; omega)
  refine ⟨CE (η.withSto η.sto ini' (Ri := rini')), Rr2 + Rb + Rs, H2,
    ⟨ρ, η.withSto η.sto ini' (Ri := rini'), c', Rr2 + Rb, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
    MemInv_bufInit (E := CE η) (E' := CE (η.withSto η.sto ini' (Ri := rini'))) hm hsto hmode hat hini hweA
      (by omega) (show ev ρ j ≤ η.rc ad.label by omega) hval hlen rfl rfl rfl (bumpIni_self _ _ _)
      (fun l' h => bumpIni_other _ _ _ l' h) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl rfl (fun _ _ h => h) rfl (fun l => hri' l) s' hs' hpa,
    hput s' hs', hnie, hxl, ?_, hAS _⟩
  have h1 := hle1 (.own xl)
  have h2 := hle2 (.own xl)
  have h3 := Res.le_def.1 hH2 (.own xl)
  simp only [Res.add_apply] at h1 h2 h3 ⊢
  omega

-- copied from TermStep.tstepMR_new
theorem stepK3_new {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.new a) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hxl : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
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
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  obtain ⟨hnone, hfresh, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hX := memHeldOn_off hH (l := freshLabel g.lbase g.n g.i th.nalloc) (fun h => by
    obtain ⟨⟨c0, hc0, -⟩, -⟩ := h; rw [hnone] at hc0; cases hc0)
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
  · intro r hr _
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
    have hX' := memHeldOn_tr (Q' := fun l' => Priv (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) l' ∧
        l' ≠ freshLabel g.lbase g.n g.i th.nalloc) (s' := s') hX
      (fun l => ⟨fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne] at hc; exact hc, ho⟩, hp⟩, hne⟩,
        fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne]; exact hc, ho⟩, hp⟩, hne⟩⟩)
      (fun l' h => allocE_ne h.2) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
      (fun l' h o w hl => LatestNP_growsAtF hg (fun t h => hsubl.subset h) hful h.2 hl)
      (fun h => ValOfR_mono (η₁ := CE η)
        (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _) h)
    have hxne : xl ≠ freshLabel g.lbase g.n g.i th.nalloc := fun e => hxl (by rw [e]; exact hnone)
    refine ⟨allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv), Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs, Rv + HP,
        ⟨ρ, η.withSto (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto, c',
          Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)), Rs, rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨he, hck⟩, htv', hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩, ?_,
        memHeldOn_unfocus hX' hent (Priv_of allocE_eq rfl hpf0), fun l cl hcl => ?_,
        fun h => hxl (by rw [allocE_ne hxne] at h; exact h), ?_,
        anchStep_fresh (ext_CE hx) (bumpIf_nb hterm (hop := by intro _ _ _ h; cases h) _) (fun _ hl => allocE_ne hl) hpf0 (fun _ _ => rfl) hnone
          (Priv_of allocE_eq rfl hpf0)⟩
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
          refine Classical.byContradiction fun hn' => ?_
          obtain ⟨m', hm', e⟩ := hful t hp hn'
          rw [ht] at hm'; cases hm'
          exact hne (hl.symm.trans e)
        · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
    · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl; rw [allocE_eq] at hcl; cases hcl
        exact noIallV_cl (WitAF.ni hi.1.2.2.2.2.2.2.1) tv 0 0 (hniA tv _ hu)
      · rw [allocE_ne hl] at hcl; exact hnie l cl hcl
    · have h1 := hle (.own xl)
      have h2 : Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) (.own xl) = 0 := by simp [Res.one, hxne]
      simp only [Res.add_apply] at h1 ⊢
      omega

-- copied from TermStep.tstepMR_newBuf
theorem stepK3_newBuf {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {n : At} {τ : Ty} {e : Expr} {Rf Rs HP : Res}
    {xl : AllocLabel}
    (hterm : th.term = .let_ x (.newBuf n τ) e) (hniA : noIallV τ = true) (hP : ProgT p)
    (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldP (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hxl : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepC p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
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
  have hX := memHeldOn_off hH (l := lbl) (fun h => by
    obtain ⟨⟨c0, hc0, -⟩, -⟩ := h; rw [hnone] at hc0; cases hc0)
  have hnone0 : E0.sto lbl = none := hnone
  have hx : Ext η η' := Ext_withSto hE.2.1 (fun l c h => allocE_sub (η := E0) hnone0 h) (bumpIni_le _ _ _)
    (Ri := rini') (hRi := hri')
  let rtR : Ty := .refine (.loc .own (.array (.lit K) (close th.σs τ))) (.ini (.lit iv))
  let R := allocBuf lbl (K * nWords us) z (stOf mem pairs th)
  have key : tstep g mem pairs th =
      [(R.1.mem, R.1.pairs, withS { th with term := e, env := (x, rtR, [R.2]) :: th.env } R.1)] := by
    simp only [tstep, hterm, evalOp, hei, numOf, hus, Option.bind_eq_bind, Option.bind_some, hwi]; rfl
  rw [key]
  intro r hr' _
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
        by rw [List.length_map, List.length_range, hnw], by simp, (TermStep.sum_map_zero _).symm, fun j Rj hj hRj => ?_⟩
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
  have hX' := memHeldOn_tr (Q' := fun l' => Priv E' l' ∧ l' ≠ lbl) (E' := E') (s' := R.1) hX
    (fun l => ⟨fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne] at hc; exact hc, ho⟩, hp⟩, hne⟩,
      fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne]; exact hc, ho⟩, hp⟩, hne⟩⟩)
    (fun l' h => allocE_ne h.2) (fun l' h => bumpIni_other _ _ _ _ h.2) (fun l' h => bumpIni_other _ _ _ _ h.2)
    (fun _ _ => rfl) rfl rfl
    (fun l' h o w hl => LatestNP_growsAtA hg hpr h.2 hl)
    (fun h => ValOfR_mono (η₁ := CE η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) h)
  have hxne : xl ≠ lbl := fun e => hxl (by rw [e]; exact hnone)
  refine ⟨E', Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs, Res.zero + HP,
    ⟨ρ, η', c', Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)), Rs, rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨he, hck⟩, htv', hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
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
          refine Classical.byContradiction fun hz => ?_
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
      memHeldOn_unfocus hX' hent (Priv_of allocE_eq rfl hpf0), fun l cl hcl => ?_,
      fun h => hxl (by rw [allocE_ne hxne] at h; exact h), ?_,
      anchStep_fresh (ext_CE hx) (bumpIf_nb hterm (hop := by intro _ _ _ h; cases h) _) (fun _ hl => allocE_ne hl) hpf0
        (fun _ hl => bumpIni_other _ _ _ _ hl) hnone (Priv_of allocE_eq rfl hpf0)⟩
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
  · by_cases hl : l = lbl
    · subst hl; rw [allocE_eq] at hcl; cases hcl
      exact noIallV_cl (WitAF.ni hiF.2.2.2.2.2.2.1) (.array (.lit K) τ) 0 0 (by simpa [noIallV] using hniA)
    · rw [allocE_ne hl] at hcl; exact hnie l cl hcl
  · have h2 : Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) (.own xl) = 0 := by simp [Res.one]; exact hxne
    simp only [Res.add_apply, Res.zero_apply]
    omega

/-- The nine K3 term shapes. -/
def IsBufInit (t : Expr) : Prop := ∃ y a b c e, t = .let_ y (.bufInit a b c) e
def IsXchgAt (t : Expr) : Prop := ∃ y a b c e, t = .let_ y (.xchgAt a b c) e
def IsXchgAtF (t : Expr) : Prop := ∃ y a b c d e, t = .let_ y (.xchgAtF a b c d) e
def IsStl (t : Expr) : Prop := ∃ y a b c e, t = .let_ y (.stl a b c) e
def IsStlw (t : Expr) : Prop := ∃ y a b c d e, t = .let_ y (.stlw a b c d) e
def IsLdl (t : Expr) : Prop := ∃ y a b e, t = .let_ y (.ldl a b) e
def IsLdlw (t : Expr) : Prop := ∃ y a b c e, t = .let_ y (.ldlw a b c) e
def IsNew (t : Expr) : Prop := ∃ y a e, t = .let_ y (.new a) e
def IsNewBuf (t : Expr) : Prop := ∃ y a b e, t = .let_ y (.newBuf a b) e

/-! ## Wiring (non-frontier ops) -/

theorem ownXStepL_ldl [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepL p x n IsLdl :=
  ownXStepL_of (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ _ hE hT htv hi hRP hm hH _ hni hx hr hpa _ => by
    obtain ⟨_, _, _, _, hte⟩ := ht
    exact stepK3_ldl hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)

theorem ownXStepL_ldlw [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepL p x n IsLdlw :=
  ownXStepL_of (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ _ hE hT htv hi hRP hm hH _ hni hx hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    exact stepK3_ldlw hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)

theorem ownXStepL_new [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepL p x n IsNew :=
  ownXStepL_of (fun _ _ _ th r ρ η cx _ Rs _ _ hn ht hsc _ hE hT htv hi hRP hm hH _ hni hx hr hpa _ => by
    obtain ⟨_, a, _, hte⟩ := ht
    have hsd := hsc ρ η cx hE hT.1 htv (finv_of htv hi)
    rw [hte] at hsd
    have hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true := by
      rcases hsd with h | ⟨_, _, _, ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact h
      all_goals cases h
    exact stepK3_new hte hniA hP hn hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)

theorem ownXStepL_newBuf [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepL p x n IsNewBuf :=
  ownXStepL_of (fun _ _ _ th r ρ η cx _ Rs _ _ hn ht hsc _ hE hT htv hi hRP hm hH _ hni hx hr hpa _ => by
    obtain ⟨_, _, τ, _, hte⟩ := ht
    have hsd := hsc ρ η cx hE hT.1 htv (finv_of htv hi)
    rw [hte] at hsd
    have hniA : noIallV τ = true := by
      rcases hsd with h | ⟨_, _, _, ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact h
      all_goals cases h
    exact stepK3_newBuf hte hniA hP hn hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)

theorem ownXStepL_bufInit [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepL p x n IsBufInit :=
  ownXStepL_of (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ _ hE hT htv hi hRP hm hH _ hni hx hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    exact stepK3_bufInit hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)

theorem ownXStepL_xchgAt [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepL p x n IsXchgAt :=
  ownXStepL_of (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ _ hE hT htv hi hRP hm hH _ hni hx hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    exact stepK3_xchgAt hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)

theorem ownXStepL_xchgAtF [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepL p x n IsXchgAtF :=
  ownXStepL_of (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ _ hE hT htv hi hRP hm hH _ hni hx hr hpa _ => by
    obtain ⟨_, _, _, _, _, _, hte⟩ := ht
    exact stepK3_xchgAtF hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)

theorem ownXStepL_stl [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepL p x n IsStl :=
  ownXStepL_of (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ _ hE hT htv hi hRP hm hH _ hni hx hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    exact stepK3_stl hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)

theorem ownXStepL_stlw [WrIniC] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepL p x n IsStlw :=
  ownXStepL_of (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ _ hE hT htv hi hRP hm hH _ hni hx hr hpa _ => by
    obtain ⟨_, _, _, _, _, _, hte⟩ := ht
    exact stepK3_stlw hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)

/-- **Split** the K3 obligation into the nine per-op obligations. -/
theorem ownXStepL_k3 {p : Prog} {x : AllocLabel} {n : Nat}
    (h1 : OwnXStepL p x n IsBufInit) (h2 : OwnXStepL p x n IsXchgAt) (h3 : OwnXStepL p x n IsXchgAtF)
    (h4 : OwnXStepL p x n IsStl) (h5 : OwnXStepL p x n IsStlw) (h6 : OwnXStepL p x n IsLdl)
    (h7 : OwnXStepL p x n IsLdlw) (h8 : OwnXStepL p x n IsNew) (h9 : OwnXStepL p x n IsNewBuf) :
    OwnXStepL p x n (fun t => exprPkg t = 3) := by
  intro g mem pairs th r hp hn ht
  generalize hte : th.term = t at ht
  cases t with
  | let_ y op e =>
    cases op with
    | bufInit a b c => exact h1 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | xchgAt a b c => exact h2 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | xchgAtF a b c d => exact h3 g mem pairs th r hp hn ⟨y, a, b, c, d, e, hte⟩
    | stl a b c => exact h4 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | stlw a b c d => exact h5 g mem pairs th r hp hn ⟨y, a, b, c, d, e, hte⟩
    | ldl a b => exact h6 g mem pairs th r hp hn ⟨y, a, b, e, hte⟩
    | ldlw a b c => exact h7 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | new a => exact h8 g mem pairs th r hp hn ⟨y, a, e, hte⟩
    | newBuf a b => exact h9 g mem pairs th r hp hn ⟨y, a, b, e, hte⟩
    | _ => simp [exprPkg, opPkg] at ht
  | _ => simp [exprPkg] at ht

/-- **The K3 deliverable from the nine per-op obligations**. -/
theorem ownXStep_k3_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {n : Nat}
    (h1 : OwnXStepL p x n IsBufInit) (h2 : OwnXStepL p x n IsXchgAt) (h3 : OwnXStepL p x n IsXchgAtF)
    (h4 : OwnXStepL p x n IsStl) (h5 : OwnXStepL p x n IsStlw) (h6 : OwnXStepL p x n IsLdl)
    (h7 : OwnXStepL p x n IsLdlw) (h8 : OwnXStepL p x n IsNew) (h9 : OwnXStepL p x n IsNewBuf) :
    OwnXStepPkg p k arch i x n 3 :=
  ownXStepPkg_of_local (ownXStepL_k3 h1 h2 h3 h4 h5 h6 h7 h8 h9)

/-- **The K3 deliverable** (`opPkg = 3`), for every `k` and `n`. -/
theorem ownXStep_k3 [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} [ProgRetIall p]
    (hP : ProgT p) (hPS : PwSkel) : ∀ n, OwnXStepPkg p k arch i x n 3 := fun _ =>
  ownXStep_k3_of (ownXStepL_bufInit hP hPS) (ownXStepL_xchgAt hP hPS) (ownXStepL_xchgAtF hP hPS) (ownXStepL_stl hP hPS)
    (ownXStepL_stlw hP hPS) (ownXStepL_ldl hP hPS) (ownXStepL_ldlw hP hPS) (ownXStepL_new hP hPS) (ownXStepL_newBuf hP hPS)

end TermOwnK3

#print axioms TermOwnK3.ownXStep_k3

#print axioms TermOwnK3.ownXStepL_k3
#print axioms TermOwnK3.ownXStep_k3_of
#print axioms TermOwnK3.heldBufInitP
#print axioms TermOwnK3.stepK3_ldl
#print axioms TermOwnK3.stepK3_ldlw
#print axioms TermOwnK3.stepK3_xchgAt
#print axioms TermOwnK3.stepK3_xchgAtF
#print axioms TermOwnK3.stepK3_stlw
#print axioms TermOwnK3.stepK3_stl
#print axioms TermOwnK3.stepK3_bufInit
#print axioms TermOwnK3.stepK3_new
#print axioms TermOwnK3.stepK3_newBuf
#print axioms TermOwnK3.oldValF
#print axioms TermOwnK3.privOff
#print axioms TermOwnK3.heldBufInitF
#print axioms TermOwnK3.ownXStepL_bufInit
#print axioms TermOwnK3.ownXStepL_xchgAt
#print axioms TermOwnK3.ownXStepL_xchgAtF
#print axioms TermOwnK3.ownXStepL_stl
#print axioms TermOwnK3.ownXStepL_stlw
#print axioms TermOwnK3.ownXStepL_ldl
#print axioms TermOwnK3.ownXStepL_ldlw
#print axioms TermOwnK3.ownXStepL_new
#print axioms TermOwnK3.ownXStepL_newBuf
