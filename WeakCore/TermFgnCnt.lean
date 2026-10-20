import WeakCore.TermFgnClos
import WeakCore.TermCntLoc
import WeakCore.TermK2aLabsV

/-! # TermFgnCnt: the staged `SysInvN` clause `FgnPromCntG` (counted slots)

An outstanding promise of `i` at a single-word counted slot (`NotSnd`, `CntOK`) of a Σ cell whose
value is a pointer names a target `TgtOK`.  As `TermFgnClos`, with the typing fact swapped:
* promise step (`fgnCnt_prom`): the certificate types the value (`WordOK` at an extension `E2` of
  the promiser's cut); `cntOK_typed` moves the slot to a counted position of the typed value and
  `labsV_cnt` gives a frontier or a box of `E2` there.  A frontier new since the cut is at a cell
  of `E2` (then as in `fgnClos_prom`) or at one of the promiser's fresh labels (`PfrRun`, carried by
  `solo_typedXC`, internal to the certificate-run induction); boxes as before (`BoxRun`);
* thread step (`fgnCnt_thread`): `fgnClos_thread` verbatim, the guard passed through.

Certificate facts used (as `fgnClos`): `certified_fulfilC`, `certified_back`, `taken_promAbove`, the
certificate run's `MemOKP` (`MemInv.1.1`, stage A: at the fulfilling configuration, before any
publish), and `CertRunP`'s `ScopeAt`/`NoHoldPub`.
-/

namespace TermFgnCnt
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermFul TermGlob TermTyped TermMain TermInterf TermNoHold TermPromClos TermFgnClos
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- With no promises the clause holds. -/
theorem fgnCnt_none {Eg : GEnv} {c : Cfg} (h : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.promises = []) :
    FgnPromCntG Eg c := by
  intro i th t m hi ht
  rw [h i th hi] at ht
  cases ht

/-! ## The certificate run with new frontiers tracked -/

/-- Every frontier of `E` not one of `E0` is at a cell of `E` or one of thread `g.i`'s labels of
index at least `n0`. -/
def PfrRun (g : G) (E0 : TEnv) (n0 : Nat) (E : TEnv) : Prop :=
  ∀ l f, E0.pfr l = none → E.pfr l = some f →
    (∃ c, E.sto l = some c) ∨ ∃ j, n0 ≤ j ∧ l = freshLabel g.lbase g.n g.i j

/-- `InvAtXB` with `PfrRun`. -/
def InvAtXC (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv) (n0 v0 na0 : Nat) (c : Cfg) :
    Prop :=
  ∃ th E, c.ths[i]? = some th ∧ Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) ∧
    na0 ≤ th.nalloc ∧ FreshRun (gOf p k arch c i) E0 na0 E ∧ BoxRun (gOf p k arch c i) E0 na0 E ∧
    PfrRun (gOf p k arch c i) E0 na0 E

theorem InvAtXC.toInvAt {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {n0 v0 na0 : Nat}
    {c : Cfg} (h : InvAtXC p k arch i E0 n0 v0 na0 c) : InvAt p k arch i c :=
  let ⟨th, E, hth, _, h1, h2, _, hbo, _⟩ := h
  ⟨th, hth, E, h1, h2, hbo⟩

theorem InvAtXC_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E : TEnv} {c : Cfg} {th : TTh}
    (hth : c.ths[i]? = some th) (hT : ThInvE p E th)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c i).boxFence = true) (hrc : TermTyped.RiniCoh E (stOf c.mem c.pairs th))
    (hfl : ∀ l cl f, E.sto l = some cl → E.pfr l = some f → f ≤ c.mem.size - 1) :
    InvAtXC p k arch i E c.mem.size th.vs.vWr th.nalloc c := by
  obtain ⟨ρ, η, cx, rfl, h⟩ := hT
  exact ⟨th, CE η, hth, Ext_refl (Coh_CE η) (CohR_CE η), ⟨ρ, η, cx, rfl, h⟩, hm, hSC, hbo,
    FrBound_refl _ _ _, frRunA_start hm hrc hfl,
    Nat.le_refl _, (fun l c h0 h => by rw [h0] at h; cases h), (fun l B h0 h => by rw [h0] at h; cases h),
    (fun l f h0 h => by rw [h0] at h; cases h)⟩

-- COPY of TermFgnClos.solo_typedXB (itself a copy of
-- TermNoHold.solo_typedXF), plus `PfrRun`.
/-- **The tied typed run with new cells, boxes and frontiers tracked.** -/
theorem solo_typedXC {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} {E0 : TEnv}
    {n0 v0 na0 : Nat} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (h0 : InvAtXC p k arch i E0 n0 v0 na0 c) {c2 : Cfg} (h : Solo p k arch i c c2)
    (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : InvAtXC p k arch i E0 n0 v0 na0 c2 := by
  refine (run_inv (c1 := c2) (P := fun c0 => Solo p k arch i c c0 ∧ InvAtXC p k arch i E0 n0 v0 na0 c0) ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hbx, hpr⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
    rw [hth] at hth'
    cases hth'
    obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩ := hTE
    have hscope := hsc c0 hc0 hcert0 th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT htv hi
    obtain ⟨-, hstep⟩ := tstep_footprintQ (hPS := hPS) (hSub := hSub) (hSig := hSig) (g := { gOf p k arch c0 i with zf := fun _ => False }) hP rfl
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)))
      (tstep_notDone hr) hscope hT hi hE htv hm hbo (PAx_of_step hs hc0' hth)
      (hwin c0 hc0 hcert0 th hth ρ η cx hE hT htv hi hm (frRunA_ext hfr hx) hfr.2.1.1 hfr.2.1.2.2.1) (hZ := ZOK_of_not (fun _ _ h => h)) (hRP := hrp)
    obtain ⟨E', hF, hx', hT', hm', hbB⟩ := hstep r hr hpa
    have hA' := anchR_tstep hF hm' hbB hE hT htv hi hm hscope (TermViewInv.envVR_solo hvI hc0 hth) hr (frRunA_ext hfr hx) hfr.2.1
    have hwu := tstep_wrUp _ _ _ _ r hr
    have hfb' := FrBound_foot hF hwu hfb hfr.1
    have hg : gOf p k arch c0' i = gOf p k arch c0 i := TermTyped.gOf_thread hs
    refine ⟨solo_trans hc0 (.thread hs (.refl _)), r.2.2, E', e3, Ext_trans hx hx', hT', ?_,
      StoClo_EFoot hF.1 hSC, by rw [hg]; exact hbo, hfb'.1, ?_, Nat.le_trans hna hwu.2.2.1, ?_, ?_, ?_⟩
    · rw [hg, e1, e2]
      exact hm'
    · rw [e1, e2]
      exact ⟨hfb'.2, hA', hfr.2.2⟩
    · intro l cl h0l hl
      rw [hg]
      rcases hF.1.2.2.1 l with e | ⟨⟨j, hj1, -, hlj⟩, -⟩
      · rw [e] at hl
        exact hfresh l cl h0l hl
      · exact ⟨j, Nat.le_trans hna hj1, hlj⟩
    · intro l B h0l hl
      rw [hg]
      rcases hF.1.2.2.2.1 l with e | ⟨⟨j, hj1, -, hlj⟩, -⟩
      · rw [e] at hl
        exact hbx l B h0l hl
      · exact ⟨j, Nat.le_trans hna hj1, hlj⟩
    · intro l f h0l hl
      rw [hg]
      rcases hF.1.2.2.2.2.2.1 l with e | ⟨-, F, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨⟨j, hj1, -, hlj⟩, -⟩
      · rw [e] at hl
        rcases hpr l f h0l hl with ⟨c1, hc1⟩ | h2
        · exact .inl ⟨c1, hx'.2.2.2.2.1 _ _ hc1⟩
        · exact .inr h2
      · exact .inl ⟨c1, hx'.2.2.2.2.1 _ _ hc1⟩
      · exact .inr ⟨j, Nat.le_trans hna hj1, hlj⟩
  · rintro c0 a v w ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hbx, hpr⟩ hw _
    have hpi := promise_inv (a := a) (v := v) (w := w) hth
    refine ⟨solo_trans hc0 (.prom a v w hw (.refl _)), _, E, hpi.2.1, hx, hTE, ?_, hSC,
      by rw [gOf_promise]; exact hbo, hfb, ?_, hna, by rw [gOf_promise]; exact hfresh,
      by rw [gOf_promise]; exact hbx, by rw [gOf_promise]; exact hpr⟩
    · rw [gOf_promise, hpi.2.2]
      exact MemInv_promSt hm
    · exact frRunA_prom hth hfr

/-- **A certified promise's pointer value at a single-word counted slot of a start cell** names, in an
extension `E2` of the start `E0`, a frontier or a box; new cells, boxes and frontiers are tracked. -/
theorem certified_promTgtC {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv}
    {n0 v0 na0 : Nat} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (h0 : InvAtXC p k arch i E0 n0 v0 na0 c) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ TermFul.promsOf c i) (hm : c.mem[t]? = some m) {cl : Cell}
    (hcl : E0.sto m.loc.label = some cl) (hU : TermPtrRts.NotSnd cl.ty m.loc.offset)
    (hC : TermPtrRts.CntOK cl.ty m.loc.offset (mw m)) {a' : Address} {g : Nat} (hv : m.val = .loc a' g) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ E2, Ext E0 E2 ∧ FreshRun (gOf p k arch c i) E0 na0 E2 ∧ BoxRun (gOf p k arch c i) E0 na0 E2 ∧
      PfrRun (gOf p k arch c i) E0 na0 E2 ∧
      ((∃ f, E2.pfr a'.label = some f) ∨ ∃ B, E2.box a'.label = some B) := by
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, hm1, -, hn2, -⟩ := certified_fulfilC hc (pwf_of_inv h0.toInvAt) ht
  rw [hm] at hm'
  cases hm'
  have h12 : Solo p k arch i c c2 := solo_trans h1 (.thread h2 (.refl _))
  obtain ⟨th2, E2, hth2, hx2, -, hm2i, -, -, -, -, -, hfresh, hbx, hpr⟩ := solo_typedXC (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc hvI hwin h0 h12 hc2
  obtain ⟨th', r, hth', hr, e1, -, -, -⟩ := threadSteps_inv h2
  rw [hth1] at hth'
  cases hth'
  have hm2 : c2.mem[t]? = some m := by rw [e1]; exact (tstep_grow hr).1 t m hm1
  have hn2' : t ∉ th2.promises := by rwa [TermFul.promsOf_some hth2] at hn2
  have hg : gOf p k arch c2 i = gOf p k arch c i := gOf_solo h12
  rw [hg] at hfresh hbx hpr
  refine ⟨E2, hx2, hfresh, hbx, hpr, ?_⟩
  rcases hm2i.1.1 t m cl hn2' hm2 (hx2.2.2.2.2.1 _ _ hcl) with hu | hw
  · rw [hv] at hu; cases hu
  · obtain ⟨b, S, ws, oo, w0, hseg, hvs, hw0, hle, -, hcnt⟩ := TermCntLoc.cntOK_typed hC hw hU
    have hwc : wc S = some ws.length := by
      obtain ⟨L, hL⟩ := TermCntLoc.segOf_accs hseg
      simp only [wc, hL, Option.map_some]
      rw [hvs.2 L hL]
    have hv0 : w0.val = .loc a' g := hle.1.trans hv
    rcases TermK2aLabsV.labsV_cnt (ρ := fun _ => 0) (fun _ _ _ h => h) rfl hwc hvs.1.2 hvs.1.1 oo hcnt w0 a' g
      hw0 hv0 with ⟨f, hf, -⟩ | ⟨B, hB⟩
    · exact .inl ⟨f, hf⟩
    · exact .inr ⟨B, hB⟩

/-! ## Preservation -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **A promise step keeps `FgnPromCntG`**: as `fgnClos_prom`, through `certified_promTgtC`; a frontier
of `E2` missing from `E_g` is new in the certificate run, so at a cell of `E2` or a fresh label. -/
theorem fgnCnt_prom (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hF : FgnPromCntG Eg c) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    FgnPromCntG (EgP Eg P N j c.mem.size) (promise c j a v w) := by
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hlb : (promise c j a v w).lbase = c.lbase := promise_lbase c j a v w
  have hszn : (promise c j a v w).n = c.n := TermStep.promise_n c j a v w
  have htr : ∀ i l, TgtOK Eg c i l → TgtOK (EgP Eg P N j c.mem.size) (promise c j a v w) i l := by
    intro i l h
    rcases h with ⟨f, hf⟩ | h | h | ⟨n, hn, h0⟩
    · left
      simp only [EgP, GEnv.withFp, plantG]
      cases e : P l with
      | none => exact ⟨f, hf⟩
      | some f' => exact ⟨f', rfl⟩
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · refine .inr (.inr (.inr ⟨n, ?_, h0⟩))
      rw [hlb, hszn]
      exact hn
  have hold : ∀ (i : Nat) (thi : TTh) (t : Ts) (m : Msg), c.ths[i]? = some thi → t ∈ thi.promises →
      (promise c j a v w).mem[t]? = some m → c.mem[t]? = some m := by
    intro i thi t m hi ht hm0
    have hlt : t < c.mem.size := X.inv.plt i thi t hi ht
    have hm : (c.mem.push ⟨a, v, w⟩)[t]? = some m := by rw [hpi.1] at hm0; exact hm0
    rw [Array.getElem?_push_lt hlt] at hm
    rw [Array.getElem?_eq_getElem hlt]
    exact hm
  intro i thi t m hi ht hm a' g hv cm hcm hns hcnt
  have hcm0 : Eg.sto m.loc.label = some cm := hcm
  by_cases hij : i = j
  · subst hij
    rw [hpi.2.1] at hi
    cases hi
    rcases List.mem_append.1 ht with ht | ht
    · exact htr _ _ (hF i th t m X.hth ht (hold i th t m X.hth ht hm) a' g hv cm hcm0 hns hcnt)
    · rw [List.mem_singleton] at ht
      subst ht
      have hm2 : (c.mem.push ⟨a, v, w⟩)[c.mem.size]? = some m := by rw [hpi.1] at hm; exact hm
      rw [Array.getElem?_push_size] at hm2
      cases hm2
      obtain ⟨S, hS⟩ := X.inv.thr i th X.hth
      obtain ⟨-, hTE, hmS, -⟩ := id hS
      have hSC : StoClo (Cut Eg i S) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
      have h0 := InvAtXC_of (p := p) (k := k) (arch := arch) hpi.2.1 hTE
        (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hmS) hSC (by rw [gOf_promise]; exact X.inv.bf)
        (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
        (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
          (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
      have htm : c.mem.size ∈ TermFul.promsOf (promise c i a v w) i := by
        rw [TermFul.promsOf_some hpi.2.1]; exact List.mem_append_right _ (List.mem_singleton_self _)
      have hmt : (promise c i a v w).mem[c.mem.size]? = some ⟨a, v, w⟩ := by
        rw [hpi.1]; exact Array.getElem?_push_size
      have hcut : cutSto Eg i a.label = some cm := by
        rcases promLocP (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X with ⟨cl0, hc0⟩ | ⟨n, hn, e⟩
        · have e2 := cutSto_sub hc0
          rw [hcm0] at e2
          cases e2
          exact hc0
        · have h1 := (X.inv.fresh i th X.hth n hn).1
          rw [← e] at h1
          rw [h1] at hcm0
          cases hcm0
      obtain ⟨E2, -, hfr, hbx, hpr, h2⟩ := certified_promTgtC (hPS := hPS) (hSub := hSub) (hSig := hSig) hP (fun c1 h1 h2 => (hrun X S hS c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc')
        (fun c1 h1 h2 => (hrun X S hS c1 h1 h2).2) h0 X.cert htm hmt (E0 := Cut Eg i S) hcut hns hcnt hv
      have hfresh : ∀ n, th.nalloc ≤ n →
          a'.label = freshLabel (promise c i a v w).lbase (promise c i a v w).n i n →
          TgtOK (EgP Eg P N i c.mem.size) (promise c i a v w) i a'.label := by
        intro n hn e
        refine .inr (.inr (.inr ⟨n, e, ?_⟩))
        show Eg.sto a'.label = none
        rw [e, hlb, hszn]
        exact (X.inv.fresh i th X.hth n hn).1
      have hcell : ∀ c3, E2.sto a'.label = some c3 →
          TgtOK (EgP Eg P N i c.mem.size) (promise c i a v w) i a'.label := by
        intro c3 h3
        cases e : cutSto Eg i a'.label with
        | some cl =>
          rcases (cutSto_some.1 e).2 with ho | ⟨f, hf⟩
          · exact .inr (.inl ⟨cl, (cutSto_some.1 e).1, ho⟩)
          · exact htr _ _ (.inl ⟨f, hf⟩)
        | none =>
          obtain ⟨n, hn, e2⟩ := hfr _ _ e h3
          exact hfresh n hn e2
      rcases h2 with ⟨f, hf⟩ | ⟨B, hB⟩
      · cases e : Eg.pfr a'.label with
        | some f' => exact htr _ _ (.inl ⟨f', e⟩)
        | none =>
          rcases hpr _ _ e hf with ⟨c3, h3⟩ | ⟨n, hn, e2⟩
          · exact hcell c3 h3
          · exact hfresh n hn e2
      · cases e : Eg.box a'.label with
        | some B' => exact .inr (.inr (.inl ⟨B', e⟩))
        | none =>
          obtain ⟨n, hn, e2⟩ := hbx _ _ e hB
          exact hfresh n hn e2
  · have hi' : c.ths[i]? = some thi := by rw [← TermStepper.promise_other X.hth hij]; exact hi
    exact htr _ _ (hF i thi t m hi' ht (hold i thi t m hi' ht hm) a' g hv cm hcm0 hns hcnt)

/-- **A thread step keeps `FgnPromCntG`**: `fgnClos_thread` with the guard passed through. -/
theorem fgnCnt_thread (hA : PromAllocF p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (hF : FgnPromCntG Eg c) :
    FgnPromCntG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  intro j thj t m hj ht hm a' g hv cm hcm hns hcnt
  have hgf := gfoot_of X Y Z
  obtain ⟨th0, h0, hs, hi, -⟩ := tctx_old X hj
  have ht0 : t ∈ th0.promises := hs t ht
  have hlt : t < c.mem.size := X.inv.plt j th0 t h0 ht0
  have hm0 : c.mem[t]? = some m := by rw [← tctx_pre X t hlt]; exact hm
  have hcm0 : Eg.sto m.loc.label = some cm := by
    have h2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto m.loc.label = some cm := hcm
    rcases hgf.2.1 m.loc.label with e | ⟨hF, -, -, -, -⟩
    · rw [e] at h2; exact h2
    · exfalso
      by_cases hji : j = i
      · subst hji
        obtain ⟨-, e3⟩ := hi rfl
        subst e3
        exact (hA X Y Z hS hPfr _ hF t m ht hm).1 rfl
      · obtain ⟨n, hn, -, e⟩ := hF
        have hti : t ∈ th.promises := (X.inv.fresh i th X.hth n hn).2.2.2.2 t m hm0 e
        exact X.inv.disj i j th th0 t (Ne.symm hji) X.hth h0 hti ht0
  have hlb : c'.lbase = c.lbase := (TermStep.threadSteps_lbase X.hc').1
  have hszn : c'.n = c.n := TermStep.threadSteps_n X.hc'
  rcases hF j th0 t m h0 ht0 hm0 a' g hv cm hcm0 hns hcnt with ⟨f, hp⟩ | ⟨cl, h1, h2⟩ | ⟨B, hB⟩ | ⟨n, e, hn⟩
  · exact .inl ⟨f, gfoot_pfr hgf hp⟩
  · refine .inr (.inl ⟨cl, ?_, h2⟩)
    show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto a'.label = some cl
    rcases hgf.2.1 a'.label with e | ⟨-, e, -⟩
    · rw [e]; exact h1
    · rw [e] at h1; cases h1
  · refine .inr (.inr (.inl ⟨B, ?_⟩))
    show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').box a'.label = some B
    rcases hgf.2.2.1 a'.label with e | ⟨-, e, -⟩
    · rw [e]; exact hB
    · rw [e] at hB; cases hB
  · rcases hgf.2.1 a'.label with e2 | ⟨⟨q, -, -, hq⟩, -, -, T, hT⟩
    · refine .inr (.inr (.inr ⟨n, by rw [hlb, hszn]; exact e, ?_⟩))
      show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto a'.label = none
      rw [e2]; exact hn
    · have hji : j = i := (TermRun.freshLabel_inj (Cfg.lt_n (arr_lt h0)) (Cfg.lt_n (arr_lt X.hth)) (e.symm.trans hq)).1
      subst hji
      exact .inr (.inl ⟨_, hT, rfl⟩)

end

end TermFgnCnt

#print axioms TermFgnCnt.fgnCnt_none
#print axioms TermFgnCnt.solo_typedXC
#print axioms TermFgnCnt.certified_promTgtC
#print axioms TermFgnCnt.fgnCnt_prom
#print axioms TermFgnCnt.fgnCnt_thread
