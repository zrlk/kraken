import WeakCore.ShadowPubStep
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! B6/B7 window chain (♭, shadow publish, no window premise).
`OwnXLeB 1` at `c`, a solo run to `c1`, the shadow publish of `x` at `c1 → c1'`, a solo run to a certified `c2`
give `OwnXLeB 0` at `c2`, re-anchored at `x` to the publish-point env `CE η1` (ini/rini only). -/
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `E0` with its `ini`/`rini` at `x` replaced by `E1`'s. -/
def reAncB (E0 E1 : TEnv) (x : AllocLabel) : TEnv :=
  { E0 with ini := fun l => if l = x then E1.ini x else E0.ini l,
            rini := fun l => if l = x then E1.rini x else E0.rini l }

/-- The shadow publish of `x` at count 1: count 0 after, ini/rini kept. -/
theorem tgt_publish1S {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat}
    (hS : SrcB p g x 1 mem pairs th ρ η cx Rf Rs HP) (hterm : th.term = .let_ y (.publish a) e)
    (hea0 : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hxl : ad.label = x) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ E Tot HP, ThInvREB g.lbase g.n g.i p E r.2.2 Tot ∧
      MemInvB g E (stOf r.1 r.2.1 r.2.2) ∧ MemHeldPB E (stOf r.1 r.2.1 r.2.2) HP ∧ TermOwnX2.StoNIE E ∧
      E.sto x ≠ none ∧ Tot (.own x) + HP (.own x) ≤ 0 ∧
      TermOwnX2.Flat.AnchStepB g th (CE η) E (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧
      TyOKE { g with tys := tysUpd g.tys th r.2.2 } E ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc ∧
      E.ini = (CE η).ini ∧ E.rini = (CE η).rini := by
  intro r hr _
  obtain ⟨rt', ws', E1, Tot', hea, hT', hm', e1, e2, hle, hx, hsn⟩ := pub_stepS (hDy := hS.dy) hterm hP hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm
    (pubScope_of (by rw [← hterm]; exact hS.sc)) hS.rp hPS r hr
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

/-- **The shadow publish of `x`** (n = 1 → 0), re-anchored at `x` to the publish-point env. -/
theorem ownXPub1S [WrIniCB] {p : Prog} [ProgRetIall p] (hP : ProgT p) {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {x : AllocLabel} (hPS : PwSkel) {E0 : TEnv} {c0 c0' : Cfg} {th : TTh} {y : String} {a : At} {e : Expr}
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat}
    (hth : c0.ths[i]? = some th) (hsc : ScopeAtB p i c0) (hvI : TermViewInv.ViewInv c0)
    (hI : TermOwnX2.Flat.OwnXLeB p k arch E0 i x 1 c0)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hc : Certified p k arch c0' i)
    (hterm : th.term = .let_ y (.publish a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad g']) (hxl : ad.label = x) (hR0 : ∀ l, E0.rini l ≤ E0.ini l) :
    ∃ η1 : TEnv, EnvOKB p η1 ∧ MemInvB (gOf p k arch c0 i) (CE η1) (stOf c0.mem c0.pairs th) ∧
      ExtB E0 (CE η1) ∧ (CE η1).sto x ≠ none ∧ (∀ l, (CE η1).rini l ≤ (CE η1).ini l) ∧
      TermOwnX2.Flat.OwnXLeB p k arch (reAncB E0 (CE η1) x) i x 0 c0' := by
  obtain ⟨th1, E, Tot, HP, hth1, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hT, htv, hFI, rfl, hRP, hDy⟩, hm, hH, hbf, hnie, hsto, hle, hx0, hA, hTy, hRc, -, hR⟩ := hI
  rw [hth] at hth1
  cases hth1
  have hFp := TermOwnX2.Flat.finv_ofB htv hFI
  have hS : SrcB p (gOf p k arch c0 i) x 1 c0.mem c0.pairs th ρ η cx Rf Rs HP :=
    ⟨rfl, Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)), hE, hT.1, hT.2, htv, hFI, hm, hH, hbf, hnie, hsto, hle,
      hsc th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT.1 htv hFp, PAx_of_step hs hc hth, hRP, hDy, hTy, hRc⟩
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  obtain ⟨E', Tot', HP', hT', hm', hH', hnie', hsto', hle', hAS, hTy', hRc', hEi, hEr⟩ :=
    tgt_publish1S hP hS hterm hea hws hxl hPS r hr hpa
  obtain ⟨hx', hA'⟩ := hAS.1 E0 hx0 hA hm.2.2.2.1.old hm' (TermOwnX2.Flat.wrHypB hE hT.1 htv hFp hm hS.sc (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth) hr)
  refine ⟨η, hE, hm, hx0, hsto, hR hR0, r.2.2, E', Tot', HP', e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact hT'), ?_, ?_, by rw [gOf_thread hs]; exact hbf, hnie', hsto', hle', ?_, ?_, ?_, ?_, ?_,
    fun _ => hAS.2.2 (hR hR0)⟩
  · rw [gOf_thread hs, e1, e2]; exact hm'
  · rw [e1, e2]; exact hH'
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hx'
    refine ⟨a1, a2, a3, a4, a5, fun l => ?_, a7, a8, a9, a10, a11, fun l => ?_⟩
    · show (if l = x then (CE η).ini x else E0.ini l) ≤ E'.ini l
      by_cases h : l = x
      · subst h; rw [if_pos rfl, hEi]; exact Nat.le_refl _
      · rw [if_neg h]; exact a6 l
    · show (if l = x then (CE η).rini x else E0.rini l) ≤ E'.rini l
      by_cases h : l = x
      · subst h; rw [if_pos rfl, hEr]; exact Nat.le_refl _
      · rw [if_neg h]; exact a12 l
  · rw [e1, e2]
    obtain ⟨b1, b2⟩ := hA'
    refine ⟨fun l hl => ?_, b2⟩
    show E'.ini l ≤ max (if l = x then (CE η).ini x else E0.ini l) (E'.rini l)
    by_cases h : l = x
    · subst h; rw [if_pos rfl, hEi]; exact Nat.le_max_left _ _
    · rw [if_neg h]; exact b1 l hl
  · rw [gOf_thread hs]; exact TyOKE_mono (TermTyped.tysOf_thread hs hth e3 hRc) hTy'
  · rw [gOf_thread hs]
    exact RecFresh_sub (g := { gOf p k arch c0 i with tys := tysUpd (gOf p k arch c0 i).tys th r.2.2 })
      (g' := { gOf p k arch c0 i with tys := tysOf c0' }) (TermTyped.tysOf_thread hs hth e3 hRc) rfl rfl hRc'
  · intro _
    show E'.rini x ≤ (if x = x then (CE η).rini x else E0.rini x)
    rw [if_pos rfl, hEr]; exact Nat.le_refl _
/-- **The window chain** (♭ `ownXLe_pub_chain`): no window premise beyond `ScopeAtB`. -/
theorem ownXLe_pub_chainS [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c c1 c1' c2 : Cfg} {th : TTh} {y : String} {a : At} {e : Expr}
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0) (hvI : TermViewInv.ViewInv c)
    (h0 : TermOwnX2.Flat.OwnXLeB p k arch E0 i x 1 c) (hTA : TermTyped.TidAt i c E0) (h1 : Solo p k arch i c c1)
    (hs : c1' ∈ threadSteps p k arch c1 i) (hth : c1.ths[i]? = some th) (hterm : th.term = .let_ y (.publish a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hx : ad.label = x)
    (h2 : Solo p k arch i c1' c2) (hc2 : Certified p k arch c2 i) (hR0 : ∀ l, E0.rini l ≤ E0.ini l) :
    ∃ η1 : TEnv, EnvOKB p η1 ∧ MemInvB (gOf p k arch c1 i) (CE η1) (stOf c1.mem c1.pairs th) ∧
      ExtB E0 (CE η1) ∧ (CE η1).sto x ≠ none ∧ (∀ l, (CE η1).rini l ≤ (CE η1).ini l) ∧
      TermOwnX2.Flat.OwnXLeB p k arch (reAncB E0 (CE η1) x) i x 0 c2 := by
  have hc1' : Certified p k arch c1' i := certified_back h2 hc2
  have hc1 : Certified p k arch c1 i := certified_back (.thread hs h2) hc2
  have hI1 := ownXLe_runAllS hP hPS hSub hSig hQ hvI h0 hTA h1 hc1
  obtain ⟨η1, hE1, hm1, hX1, hs1, hr1, hI1'⟩ :=
    ownXPub1S hP hPS hth (hQ c1 h1 hc1) (TermViewInv.viewInv_solo hvI h1) hI1 hs hc1' hterm hea hws hx hR0
  exact ⟨η1, hE1, hm1, hX1, hs1, hr1, ownXLe_runAllS hP hPS hSub hSig (fun c0 h3 h4 => hQ c0 (solo_trans h1 (.thread hs h3)) h4)
    (TermViewInv.viewInv_thread (TermViewInv.viewInv_solo hvI h1) hs) hI1'
    (TermTyped.tidAt_thread hs (TermTyped.tidAt_solo h1 hTA)) h2 hc2⟩

/-- **Holder interface**: after the window publish of `x`, at every certified `c2`, the thread's env is bounded at `x`
by the publish-point env `CE η1` (and `η1` is the thread's own typing env at `c1`). -/
theorem pub_chain_fzS [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c c1 c1' c2 : Cfg} {th : TTh} {y : String} {a : At} {e : Expr}
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0) (hvI : TermViewInv.ViewInv c)
    (h0 : TermOwnX2.Flat.OwnXLeB p k arch E0 i x 1 c) (hTA : TermTyped.TidAt i c E0) (h1 : Solo p k arch i c c1)
    (hs : c1' ∈ threadSteps p k arch c1 i) (hth : c1.ths[i]? = some th) (hterm : th.term = .let_ y (.publish a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hx : ad.label = x)
    (h2 : Solo p k arch i c1' c2) (hc2 : Certified p k arch c2 i) (hR0 : ∀ l, E0.rini l ≤ E0.ini l) :
    ∃ η1 : TEnv, EnvOKB p η1 ∧ MemInvB (gOf p k arch c1 i) (CE η1) (stOf c1.mem c1.pairs th) ∧
      ExtB E0 (CE η1) ∧ (CE η1).sto x ≠ none ∧ (∀ l, (CE η1).rini l ≤ (CE η1).ini l) ∧
      ∃ th2 E, c2.ths[i]? = some th2 ∧ MemInvB (gOf p k arch c2 i) E (stOf c2.mem c2.pairs th2) ∧ ExtB E0 E ∧
        E.sto x ≠ none ∧ (CE η1).ini x ≤ E.ini x ∧ (CE η1).rini x ≤ E.rini x ∧
        E.rini x ≤ (CE η1).rini x ∧ E.ini x ≤ max ((CE η1).ini x) ((CE η1).rini x) := by
  obtain ⟨η1, hE1, hm1, hX1, hs1, hr1, hI⟩ :=
    ownXLe_pub_chainS hP hPS hSub hSig hQ hvI h0 hTA h1 hs hth hterm hea hws hx h2 hc2 hR0
  obtain ⟨th2, E, hth2, hm2, hX2, hs2, hr, hi⟩ := TermOwnX2.Flat.OwnXLeB.fz_bounds hI
  have hi0 := hX2.2.2.2.2.2.1 x
  have hr0 := hX2.rini x
  simp only [reAncB, if_pos] at hr hi hi0 hr0
  refine ⟨η1, hE1, hm1, hX1, hs1, hr1, th2, E, hth2, hm2, ?_, hs2, hi0, hr0, hr, hi⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hX2
  refine ⟨a1, a2, a3, a4, a5, fun l => Nat.le_trans ?_ (a6 l), a7, a8, a9, a10, a11, fun l => Nat.le_trans ?_ (a12 l)⟩
  · show E0.ini l ≤ (if l = x then (CE η1).ini x else E0.ini l)
    by_cases h : l = x
    · subst h; rw [if_pos rfl]; exact hX1.2.2.2.2.2.1 l
    · rw [if_neg h]; exact Nat.le_refl _
  · show E0.rini l ≤ (if l = x then (CE η1).rini x else E0.rini l)
    by_cases h : l = x
    · subst h; rw [if_pos rfl]; exact hX1.rini l
    · rw [if_neg h]; exact Nat.le_refl _
end
end TermOwnK4.Flat
