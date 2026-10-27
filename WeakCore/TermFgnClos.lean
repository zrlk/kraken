import WeakCore.TermNoHold
import WeakCore.TermPromClos

/-! # TermFgnClos: the `SysInvN` clause `fgnClos` (`FgnPromClosG`)

An outstanding promise of `i` at a Σ cell of a `noOwnIn`/`rgnFree` type whose value is a pointer
names a published cell, a cell of `i`, a box, or one of `i`'s labels holding no cell yet.
* promise step (`fgnClos_prom`): the certificate of the new promise, from its fulfilling
  configuration, types the value (`WordOK` at an extension `E2` of the promiser's cut);
  `wordOK_locPub` gives a frontier cell or a box of `E2`; cells new since the cut are the promiser's
  fresh labels (`FreshRun`), and so are boxes (`BoxRun`, carried by `solo_typedXB`);
* thread step (`fgnClos_thread`): cells, boxes and owners away from the step's fresh labels are
  kept, frontiers only grow; a fresh label is the stepper's (`freshLabel_inj`); a promise at the
  stepper's fresh label is ruled out by `PromAllocF` (as in `promClos_thread`);
* `fgnClos_use`: the consumer form (a Σ target has a frontier or is `i`'s), via `boxSto`/`fresh`.
-/

namespace TermFgnClos
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermFul TermGlob TermTyped TermMain TermInterf TermNoHold TermPromClos
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- With no promises the clause holds. -/
theorem fgnClos_none {Eg : GEnv} {c : Cfg} (h : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.promises = []) :
    FgnPromClosG Eg c := by
  intro i th t m hi ht
  rw [h i th hi] at ht
  cases ht

/-- **The consumer form**: a Σ target of such a promise has a frontier or is a cell of `i`. -/
theorem fgnClos_use {Eg : GEnv} {c : Cfg} (hF : FgnPromClosG Eg c) (hbs : TermBoxZ.BoxSto Eg)
    {i : Nat} {th : TTh} {t : Ts} {m : Msg} (hi : c.ths[i]? = some th) (ht : t ∈ th.promises)
    (hm : c.mem[t]? = some m) {a' : Address} {g : Nat} (hv : m.val = .loc a' g) {cm : Cell}
    (hcm : Eg.sto m.loc.label = some cm) (hno : Ty.noOwnIn [] cm.ty = true) (hrf : rgnFree cm.ty = true)
    {cl : Cell} (hcl : Eg.sto a'.label = some cl) : (∃ f, Eg.pfr a'.label = some f) ∨ cl.owner = some i := by
  rcases hF i th t m hi ht hm a' g hv cm hcm hno hrf with h | ⟨cl', h1, h2⟩ | ⟨B, hB⟩ | ⟨n, -, h0⟩
  · exact .inl h
  · rw [hcl] at h1; cases h1; exact .inr h2
  · rw [hbs _ B hB] at hcl; cases hcl
  · rw [h0] at hcl; cases hcl

/-! ## The certificate run with boxes tracked -/

/-- Every box of `E` not a box of the start `E0` is at one of thread `g.i`'s labels of index at least `n0`. -/
def BoxRun (g : G) (E0 : TEnv) (n0 : Nat) (E : TEnv) : Prop :=
  ∀ l B, E0.box l = none → E.box l = some B → ∃ j, n0 ≤ j ∧ l = freshLabel g.lbase g.n g.i j

/-- `InvAtXF` (no locality labels) with `BoxRun`. -/
def InvAtXB (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv) (n0 v0 na0 : Nat) (c : Cfg) :
    Prop :=
  ∃ th E, c.ths[i]? = some th ∧ Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) ∧
    na0 ≤ th.nalloc ∧ FreshRun (gOf p k arch c i) E0 na0 E ∧ BoxRun (gOf p k arch c i) E0 na0 E

theorem InvAtXB.toInvAt {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {n0 v0 na0 : Nat}
    {c : Cfg} (h : InvAtXB p k arch i E0 n0 v0 na0 c) : InvAt p k arch i c :=
  let ⟨th, E, hth, _, h1, h2, _, hbo, _⟩ := h
  ⟨th, hth, E, h1, h2, hbo⟩

theorem InvAtXB_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E : TEnv} {c : Cfg} {th : TTh}
    (hth : c.ths[i]? = some th) (hT : ThInvE p E th)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c i).boxFence = true) (hrc : TermTyped.RiniCoh E (stOf c.mem c.pairs th))
    (hfl : ∀ l cl f, E.sto l = some cl → E.pfr l = some f → f ≤ c.mem.size - 1) :
    InvAtXB p k arch i E c.mem.size th.vs.vWr th.nalloc c := by
  obtain ⟨ρ, η, cx, rfl, h⟩ := hT
  exact ⟨th, CE η, hth, Ext_refl (Coh_CE η) (CohR_CE η), ⟨ρ, η, cx, rfl, h⟩, hm, hSC, hbo,
    FrBound_refl _ _ _, frRunA_start hm hrc hfl,
    Nat.le_refl _, (fun l c h0 h => by rw [h0] at h; cases h), (fun l B h0 h => by rw [h0] at h; cases h)⟩

-- COPY of TermNoHold.solo_typedXF, at `Z := ∅`, `H := ⊤`, plus `BoxRun`.
/-- **The tied typed run with new cells and boxes tracked.** -/
theorem solo_typedXB {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} {E0 : TEnv}
    {n0 v0 na0 : Nat} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (h0 : InvAtXB p k arch i E0 n0 v0 na0 c) (hTA : TermTyped.TidAt i c E0) {c2 : Cfg} (h : Solo p k arch i c c2)
    (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : InvAtXB p k arch i E0 n0 v0 na0 c2 := by
  refine (run_inv (c1 := c2) (P := fun c0 => Solo p k arch i c c0 ∧ InvAtXB p k arch i E0 n0 v0 na0 c0) ?_ ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hbx⟩ hs hrest
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
      StoClo_EFoot hF.1 hSC, by rw [hg]; exact hbo, hfb'.1, ?_, Nat.le_trans hna hwu.2.2.1, ?_, ?_⟩
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
  · rintro c0 a v w ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hbx⟩ hw _
    have hpi := promise_inv (a := a) (v := v) (w := w) hth
    refine ⟨solo_trans hc0 (.prom a v w hw (.refl _)), _, E, hpi.2.1, hx, hTE, ?_, hSC,
      by rw [gOf_promise]; exact hbo, hfb, ?_, hna, by rw [gOf_promise]; exact hfresh,
      by rw [gOf_promise]; exact hbx⟩
    · rw [gOf_promise, hpi.2.2]
      exact MemInv_promSt hm
    · exact frRunA_prom hth hfr
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hbx⟩ hs _
    rcases TermTyped.extSteps_res hs hth with ⟨x1, n1, a1, e1, rt1, ws1, rs1, hterm, hn1, hev1, hrs1, rfl⟩ | ⟨x1, a1, e1, lb, hterm, htl, rfl⟩
    · exact ⟨solo_trans hc0 (.ext hs (.refl _)), _, E, set_self hth, hx, TermTyped.ThInvE_ext hn1 hterm hev1 hrs1 hTE,
        by rw [gOf_ext hs]; exact hm, hSC, by rw [gOf_ext hs]; exact hbo, hfb, hfr, hna, by rw [gOf_ext hs]; exact hfresh,
        by rw [gOf_ext hs]; exact hbx⟩
    · obtain ⟨hbs, hbp⟩ := TermTyped.tidBox_ext hx (TermTyped.tidAt_solo hc0 hTA th hth lb htl)
      exact ⟨solo_trans hc0 (.ext hs (.refl _)), _, E, set_self (tr := c0.trace) hth, hx, TermTyped.ThInvE_cur hterm hbs hbp hTE,
        by rw [gOf_ext hs]; exact hm, hSC, by rw [gOf_ext hs]; exact hbo, hfb, hfr, hna, by rw [gOf_ext hs]; exact hfresh,
        by rw [gOf_ext hs]; exact hbx⟩

/-- **A certified promise's pointer value at a `noOwnIn`/`rgnFree` start cell** names, in an extension
`E2` of the start `E0`, a frontier cell or a box; new cells and boxes are the thread's fresh labels. -/
theorem certified_promTgt {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv}
    {n0 v0 na0 : Nat} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (h0 : InvAtXB p k arch i E0 n0 v0 na0 c) (hTA : TermTyped.TidAt i c E0) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ TermFul.promsOf c i) (hm : c.mem[t]? = some m) {cl : Cell}
    (hcl : E0.sto m.loc.label = some cl) (hno : Ty.noOwnIn [] cl.ty = true) (hrf : rgnFree cl.ty = true)
    {a' : Address} {g : Nat} (hv : m.val = .loc a' g) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ E2, Ext E0 E2 ∧ FreshRun (gOf p k arch c i) E0 na0 E2 ∧ BoxRun (gOf p k arch c i) E0 na0 E2 ∧
      ((∃ c2 f, E2.sto a'.label = some c2 ∧ E2.pfr a'.label = some f) ∨ ∃ B, E2.box a'.label = some B) := by
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, hm1, -, hn2, -⟩ := certified_fulfilC hc (pwf_of_inv h0.toInvAt) ht
  rw [hm] at hm'
  cases hm'
  have h12 : Solo p k arch i c c2 := solo_trans h1 (.thread h2 (.refl _))
  obtain ⟨th2, E2, hth2, hx2, -, hm2i, -, -, -, -, -, hfresh, hbx⟩ := solo_typedXB (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc hvI hwin h0 hTA h12 hc2
  obtain ⟨th', r, hth', hr, e1, -, -, -⟩ := threadSteps_inv h2
  rw [hth1] at hth'
  cases hth'
  have hm2 : c2.mem[t]? = some m := by rw [e1]; exact (tstep_grow hr).1 t m hm1
  have hn2' : t ∉ th2.promises := by rwa [TermFul.promsOf_some hth2] at hn2
  have hg : gOf p k arch c2 i = gOf p k arch c i := gOf_solo h12
  rw [hg] at hfresh hbx
  refine ⟨E2, hx2, hfresh, hbx, ?_⟩
  rcases hm2i.1.1 t m cl hn2' hm2 (hx2.2.2.2.2.1 _ _ hcl) with hu | hw
  · rw [hv] at hu; cases hu
  · rcases wordOK_locPub hw hno hrf (w := mw m) hv with ⟨c3, f, h3, h4⟩ | ⟨B, hB⟩
    · exact .inl ⟨c3, f, h3, h4⟩
    · exact .inr ⟨B, hB⟩

/-! ## Preservation -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **A promise step keeps `fgnClos`**: old promises keep their targets (frontiers only grow); the
new one's target is, by its certificate (`certified_promTgt` from the promiser's cut), a cell of the
cut (the promiser's or shared), a box of `E_g`, or one of the promiser's fresh labels. -/
theorem fgnClos_prom (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hF : FgnPromClosG Eg c) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    FgnPromClosG (EgP Eg P N j c.mem.size) (promise c j a v w) := by
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
  intro i thi t m hi ht hm a' g hv cm hcm hno hrf
  have hcm0 : Eg.sto m.loc.label = some cm := hcm
  by_cases hij : i = j
  · subst hij
    rw [hpi.2.1] at hi
    cases hi
    rcases List.mem_append.1 ht with ht | ht
    · exact htr _ _ (hF i th t m X.hth ht (hold i th t m X.hth ht hm) a' g hv cm hcm0 hno hrf)
    · rw [List.mem_singleton] at ht
      subst ht
      have hm2 : (c.mem.push ⟨a, v, w⟩)[c.mem.size]? = some m := by rw [hpi.1] at hm; exact hm
      rw [Array.getElem?_push_size] at hm2
      cases hm2
      obtain ⟨S, hS⟩ := X.inv.thr i th X.hth
      obtain ⟨-, hTE, hmS, -⟩ := id hS
      have hSC : StoClo (Cut Eg i S) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
      have h0 := InvAtXB_of (p := p) (k := k) (arch := arch) hpi.2.1 hTE
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
      obtain ⟨E2, -, hfr, hbx, h2⟩ := certified_promTgt (hPS := hPS) (hSub := hSub) (hSig := hSig) hP (fun c1 h1 h2 => (hrun X S hS c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc')
        (fun c1 h1 h2 => (hrun X S hS c1 h1 h2).2) h0 (TermMain.tidAt_cutP X.inv i S) X.cert htm hmt (E0 := Cut Eg i S) hcut hno hrf hv
      have hfresh : ∀ n, th.nalloc ≤ n →
          a'.label = freshLabel (promise c i a v w).lbase (promise c i a v w).n i n →
          TgtOK (EgP Eg P N i c.mem.size) (promise c i a v w) i a'.label := by
        intro n hn e
        refine .inr (.inr (.inr ⟨n, e, ?_⟩))
        show Eg.sto a'.label = none
        rw [e, hlb, hszn]
        exact (X.inv.fresh i th X.hth n hn).1
      rcases h2 with ⟨c3, -, h3, -⟩ | ⟨B, hB⟩
      · cases e : cutSto Eg i a'.label with
        | some cl =>
          rcases (cutSto_some.1 e).2 with ho | ⟨f, hf⟩
          · exact .inr (.inl ⟨cl, (cutSto_some.1 e).1, ho⟩)
          · exact htr _ _ (.inl ⟨f, hf⟩)
        | none =>
          obtain ⟨n, hn, e2⟩ := hfr _ _ e h3
          exact hfresh n hn e2
      · cases e : Eg.box a'.label with
        | some B' => exact .inr (.inr (.inl ⟨B', e⟩))
        | none =>
          obtain ⟨n, hn, e2⟩ := hbx _ _ e hB
          exact hfresh n hn e2
  · have hi' : c.ths[i]? = some thi := by rw [← TermStepper.promise_other X.hth hij]; exact hi
    exact htr _ _ (hF i thi t m hi' ht (hold i thi t m hi' ht hm) a' g hv cm hcm0 hno hrf)

/-- **A thread step keeps `fgnClos`**: the promise's cell is old (`PromAllocF`, as in
`promClos_thread`); frontiers, owned cells and boxes survive (`GFoot`); a label of `i` still free
either stays free or becomes a cell of the stepper, which is then `i` (`freshLabel_inj`). -/
theorem fgnClos_thread (hA : PromAllocF p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (hF : FgnPromClosG Eg c) :
    FgnPromClosG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  intro j thj t m hj ht hm a' g hv cm hcm hno hrf
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
  rcases hF j th0 t m h0 ht0 hm0 a' g hv cm hcm0 hno hrf with ⟨f, hp⟩ | ⟨cl, h1, h2⟩ | ⟨B, hB⟩ | ⟨n, e, hn⟩
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

end TermFgnClos

#print axioms TermFgnClos.fgnClos_use
#print axioms TermFgnClos.solo_typedXB
#print axioms TermFgnClos.certified_promTgt
#print axioms TermFgnClos.fgnClos_none
#print axioms TermFgnClos.fgnClos_prom
#print axioms TermFgnClos.fgnClos_thread
