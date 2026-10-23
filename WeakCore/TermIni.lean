import WeakCore.TermIniStep
import WeakCore.TermTyped
import WeakCore.TermK5P
import WeakCore.TermK5O

/-!
# Holder bound, step 2: the holder bound along the certificate run

`HoldB E0 pb E s`: along the solo run that certifies a promise, at every
label unpublished at the start (`E0.pfr l = none`), the start bound `pb l` is
at most the current planted frontier `plantF E s l` while the label stays
unpublished, and at most the frontier once a `publish` sets it (EFoot's
publish disjunct bounds every holder: F2′ (a″)).  Carries `rini ≤ ini`.
-/

namespace TermIni

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermFul TermIniStep TermTyped TermGlob
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem foldr_filter_le {p : Nat → Bool} {X : Nat} :
    ∀ L : List Nat, (∀ u ∈ L, p u = true → u ≤ X) → (L.filter p).foldr max 0 ≤ X
  | [], _ => Nat.zero_le _
  | u :: L, h => by
      have hL : ∀ v ∈ L, p v = true → v ≤ X := fun v hv => h v (List.mem_cons_of_mem _ hv)
      rw [List.filter_cons]
      split
      · exact Nat.max_le.2 ⟨h u (by simp) ‹_›, foldr_filter_le L hL⟩
      · exact foldr_filter_le L hL

/-- `plantT` is the least bound of the holders. -/
theorem plantT_le {E : TEnv} {s : St} {l : AllocLabel} {X : Nat}
    (h : ∀ u ∈ s.promises, HoldW E s l u → u ≤ X) : plantT E s l ≤ X := by
  unfold plantT
  exact foldr_filter_le _ fun u hu hd => h u hu (@of_decide_eq_true _ (Classical.propDecidable _) hd)

/-- **`plantF` only grows** across a step that grows `vWr`, extends memory,
removes promises only at or below the new `vWr`, adds promises only past the
old memory, and whose new environment initialises the unit of a lowest
outstanding promise only at or below the new `vWr` (`hini`). -/
theorem plantF_mono {E E' : TEnv} {s s' : St} {l : AllocLabel}
    (hv : s.vs.vWr ≤ s'.vs.vWr) (hful : ∀ t ∈ s.promises, t ∉ s'.promises → t ≤ s'.vs.vWr)
    (hlt : ∀ t ∈ s.promises, t < s.mem.size) (hme : TermCert.MemExt s.mem s'.mem)
    (hP : ∀ u ∈ s'.promises, u ∈ s.promises ∨ s.mem.size ≤ u)
    (hini : ∀ t m, t ∈ s.promises → s.mem[t]? = some m →
      (∀ u ∈ s.promises, ∀ m', s.mem[u]? = some m' → m'.loc = m.loc → t ≤ u) →
      ¬ IniWr E m.loc → IniWr E' m.loc → t ≤ s'.vs.vWr) :
    plantF E s l ≤ plantF E' s' l := by
  refine Nat.max_le.2 ⟨Nat.le_trans hv (Nat.le_max_left _ _), plantT_le fun u _ hu => ?_⟩
  obtain ⟨t, ht, m, hm, hl, hut, hmin, hni⟩ := hu
  refine Nat.le_trans hut ?_
  by_cases ht' : t ∈ s'.promises
  · by_cases hi : IniWr E' m.loc
    · exact Nat.le_trans (hini t m ht hm hmin hni hi) (Nat.le_max_left _ _)
    · refine HoldW_le_plantF ⟨t, ht', m, hme t m hm, hl, Nat.le_refl _, fun u hu m' hm' he => ?_, hi⟩
      rcases hP u hu with hu0 | hu0
      · have hlu := hlt u hu0
        obtain ⟨m0, hm0⟩ : ∃ m0, s.mem[u]? = some m0 := ⟨s.mem[u], Array.getElem?_eq_getElem hlu⟩
        have e := hme u m0 hm0
        rw [hm'] at e
        cases e
        exact hmin u hu0 m' hm0 he
      · exact Nat.le_trans (Nat.le_of_lt (hlt t ht)) hu0
  · exact Nat.le_trans (hful t ht ht') (Nat.le_max_left _ _)

/-- A footprint initialises the unit of a lowest outstanding promise only at or
below the new `vWr` (`RiniW`, with `rini ≤ ini` before the step). -/
theorem holder_iniW {g : G} {E E' : TEnv} {s s' : St} (hF : Foot g E E' s s')
    (hrl : ∀ l, E.rini l ≤ E.ini l) (hlt : ∀ t ∈ s.promises, t < s.mem.size) :
    ∀ t m, t ∈ s.promises → s.mem[t]? = some m →
      (∀ u ∈ s.promises, ∀ m', s.mem[u]? = some m' → m'.loc = m.loc → t ≤ u) →
      ¬ IniWr E m.loc → IniWr E' m.loc → t ≤ s'.vs.vWr := by
  intro t m ht hm hmin hni hi
  have hex : ∃ c N e us, E.sto m.loc.label = some c ∧ c.ty = .array (.lit N) e ∧ accs e = some us ∧
      ¬ m.loc.offset < E.rc m.loc.label * nWords us :=
    Classical.byContradiction fun hne => hni fun c N e us h1 h2 h3 =>
      Classical.byContradiction fun hlt' => hne ⟨c, N, e, us, h1, h2, h3, hlt'⟩
  obtain ⟨c, N, e, us, hc, hT, hus, hge⟩ := hex
  have hc' : E'.sto m.loc.label = some c := by
    rcases hF.1.2.2.1 m.loc.label with e1 | ⟨hl, -⟩
    · rw [e1]; exact hc
    · rw [(hF.2 _ hl).1] at hc; cases hc
  have h1 := hi c N e us hc' hT hus
  have hrc : E.rc m.loc.label = E.rini m.loc.label := Nat.min_eq_right (hrl _)
  rw [hrc] at hge
  have h2 : m.loc.offset < E'.rini m.loc.label * nWords us :=
    Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ (Nat.min_le_right _ _))
  obtain ⟨τ, hτ, hτ'⟩ := hF.1.riniW m.loc.label c hc N e us hT hus m.loc.offset (Nat.le_of_not_lt hge) h2
  refine Nat.le_trans ?_ hτ
  rcases hτ' with hs | ⟨hτP, m', hm', hl'⟩
  · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (hlt t ht) hs)
  · exact hmin τ hτP m' hm' hl'

/-- **The holder bound** of a run started at `E0` with start
bounds `pb`, at environment `E` and state `s`. -/
def HoldB (E0 : TEnv) (pb : AllocLabel → Ts) (E : TEnv) (s : St) : Prop :=
  (∀ l, E.rini l ≤ E.ini l) ∧
  (∀ l, E0.pfr l = none → E.pfr l = none → pb l ≤ plantF E s l) ∧
  (∀ l c f, E0.pfr l = none → E.sto l = some c → E.pfr l = some f → pb l ≤ f)

/-- The start of the run. -/
theorem HoldB_start {E0 : TEnv} {s : St} (hrl : ∀ l, E0.rini l ≤ E0.ini l) :
    HoldB E0 (plantF E0 s) E0 s :=
  ⟨hrl, fun _ _ _ => Nat.le_refl _, fun _ _ _ h0 _ h => absurd (h0.symm.trans h) (fun e => by cases e)⟩

/-- **`HoldB` along a thread step** (its footprint `Foot`, F2′ (a″)). -/
theorem HoldB_foot {g : G} {E0 : TEnv} {pb : AllocLabel → Ts} {E E' : TEnv} {s s' : St}
    (hB : HoldB E0 pb E s) (hF : Foot g E E' s s')
    (hlt : ∀ t ∈ s.promises, t < s.mem.size) (hme : TermCert.MemExt s.mem s'.mem)
    (hv : s.vs.vWr ≤ s'.vs.vWr) (hful : ∀ t ∈ s.promises, t ∉ s'.promises → t ≤ s'.vs.vWr)
    (hP : ∀ u ∈ s'.promises, u ∈ s.promises ∨ s.mem.size ≤ u) : HoldB E0 pb E' s' := by
  have hmono : ∀ l, plantF E s l ≤ plantF E' s' l := fun l =>
    plantF_mono hv hful hlt hme hP (holder_iniW hF hB.1 hlt)
  refine ⟨hF.1.2.2.2.2.2.2.2.2.2.2.1 hB.1, fun l h0 hn => ?_, fun l c f h0 hc hf => ?_⟩
  · have hEn : E.pfr l = none := by
      rcases hF.1.2.2.2.2.2.1 l with e | ⟨-, F, e, -⟩ | ⟨-, h, -⟩
      · rw [← e]; exact hn
      · rw [e] at hn; cases hn
      · exact h
    exact Nat.le_trans (hB.2.1 l h0 hEn) (hmono l)
  · rcases hF.1.2.2.2.2.2.1 l with e | ⟨hn, F, e, hvF, -, -, -, hH, -⟩ | ⟨-, -, e⟩
    · rw [e] at hf
      rcases hF.1.2.2.1 l with e' | ⟨hl, -⟩
      · rw [e'] at hc; exact hB.2.2 l c f h0 hc hf
      · rw [(hF.2 l hl).2.2.2] at hf; cases hf
    · rw [e] at hf; cases hf
      exact Nat.le_trans (hB.2.1 l h0 hn) (Nat.max_le.2 ⟨hvF, plantT_le fun u _ hu => hH u hu⟩)
    · rw [e] at hc; cases hc

/-- **`HoldB` along a promise step** (same environment and `vWr`; memory
extends, promises only gain the new message). -/
theorem HoldB_prom {E0 : TEnv} {pb : AllocLabel → Ts} {E : TEnv} {s s' : St}
    (hB : HoldB E0 pb E s) (hlt : ∀ t ∈ s.promises, t < s.mem.size) (hme : TermCert.MemExt s.mem s'.mem)
    (hv : s.vs.vWr = s'.vs.vWr) (hsub : ∀ t ∈ s.promises, t ∈ s'.promises)
    (hP : ∀ u ∈ s'.promises, u ∈ s.promises ∨ s.mem.size ≤ u) : HoldB E0 pb E s' := by
  have hmono : ∀ l, plantF E s l ≤ plantF E s' l := fun l =>
    plantF_mono (Nat.le_of_eq hv) (fun t ht hn => absurd (hsub t ht) hn) hlt hme hP
      (fun _ _ _ _ _ hni hi => absurd hi hni)
  exact ⟨hB.1, fun l h0 hn => Nat.le_trans (hB.2.1 l h0 hn) (hmono l), hB.2.2⟩

/-- `HoldB` across a promise step's state change (`promSt`). -/
theorem HoldB_promSt {E0 : TEnv} {pb : AllocLabel → Ts} {E : TEnv} {s : St} {a : Address}
    {v : WeakMem.Val} {w : Ts} (hB : HoldB E0 pb E s) (hlt : ∀ t ∈ s.promises, t < s.mem.size) :
    HoldB E0 pb E (promSt s a v w) :=
  HoldB_prom hB hlt (TermCert.MemExt.push _ _) rfl (fun t ht => List.mem_append_left _ ht)
    (fun u hu => by
      rcases List.mem_append.1 hu with h | h
      · exact .inl h
      · rw [List.mem_singleton] at h; exact .inr (Nat.le_of_eq h.symm))

/-- `InvAtX` with the holder bound `HoldB` of start bounds `pb`; (iniop) and the run's
count locality `IniLoc` at the start labels `Z`. -/
def InvAtXHZ (Z : AllocLabel → Prop) (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv)
    (n0 v0 : Nat) (pb : AllocLabel → Ts) (c : Cfg) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) : Prop :=
  ∃ th E, c.ths[i]? = some th ∧ Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) ∧
    HoldB E0 pb E (stOf c.mem c.pairs th) ∧ IniLoc Z E0 E ∧ IniHeld H E0 E th.vs.vWr

/-- `InvAtXHZ` with no locality labels. -/
abbrev InvAtXH := InvAtXHZ (fun _ => False)

theorem InvAtXHZ.toX {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {n0 v0 : Nat}
    {pb : AllocLabel → Ts} {c : Cfg} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop}
    (h : InvAtXHZ Z p k arch i E0 n0 v0 pb c H) : InvAtXZ Z p k arch i E0 n0 v0 c H :=
  let ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, _, a9, a10⟩ := h
  ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩

/-- The tied invariant with the holder bound, restarted right after the
plant's promise step (start bounds `plantF` there). -/
theorem InvAtXH_promOf {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP : Cfg} {thP : TTh}
    {E0 : TEnv} {a0 : Address} {vB : WeakMem.Val} {w : Ts}
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true) (hrl0 : ∀ l, E0.rini l ≤ E0.ini l) (hrc0 : TermTyped.RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1)
    (Z : AllocLabel → Prop := fun _ => False) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) :
    InvAtXHZ Z p k arch i E0 (cP.mem.size + 1) thP.vs.vWr
      (plantF E0 (promSt (stOf cP.mem cP.pairs thP) a0 vB w)) (promise cP i a0 vB w) H := by
  have hpi := promise_inv (a := a0) (v := vB) (w := w) hthP
  have hs : (promise cP i a0 vB w).mem.size = cP.mem.size + 1 := by rw [hpi.1, Array.size_push]
  refine ⟨_, E0, hpi.2.1, ?_, hT0, by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm0, hSC,
    by rw [gOf_promise]; exact hbo, FrBound_refl _ _ _, ⟨⟨Nat.le_refl _, by show cP.mem.size + 1 ≤ (promise cP i a0 vB w).mem.size; rw [hs]; exact Nat.le_refl _,
      fun _ _ h0 h => absurd (h0.symm.trans h) (fun e => by cases e)⟩, anchR_prom hthP (anchR_start hm0 hrc0 hfl0), .inl rfl⟩, ?_, IniLoc_refl _ _, IniHeld_refl _ _ _⟩
  · obtain ⟨ρ, η, cx, rfl, -⟩ := hT0
    exact Ext_refl (Coh_CE η) (CohR_CE η)
  · rw [hpi.2.2]; exact HoldB_start hrl0

theorem solo_typedXH {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} {E0 : TEnv}
    {n0 v0 : Nat} {pb : AllocLabel → Ts} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (h0 : InvAtXHZ Z p k arch i E0 n0 v0 pb c H) {c2 : Cfg} (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    InvAtXHZ Z p k arch i E0 n0 v0 pb c2 H := by
  refine (run_inv (c1 := c2) (P := fun c0 => Solo p k arch i c c0 ∧ InvAtXHZ Z p k arch i E0 n0 v0 pb c0 H) ?_ ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hB, hIL, hIH⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
    rw [hth] at hth'
    cases hth'
    obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩ := hTE
    have hscope := hsc c0 hc0 hcert0 th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT htv hi
    obtain ⟨-, hstep⟩ := tstep_footprintQ (hRP := hrp) (hPS := hPS) (hSub := hSub) (hSig := hSig) (g := { gOf p k arch c0 i with zf := Z }) hP rfl
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)))
      (tstep_notDone hr) hscope hT hi hE htv hm hbo (PAx_of_step hs hc0' hth)
      (hwin c0 hc0 hcert0 th hth ρ η cx hE hT htv hi hm (frRunA_ext hfr hx) hfr.2.1.1 hfr.2.1.2.2.1) (hZ := ZOK_of_not (hZr c0 hc0 hcert0 th hth))
    obtain ⟨E', hF, hx', hT', hm', hbB⟩ := hstep r hr hpa
    have hA' := anchR_tstep hF hm' hbB hE hT htv hi hm hscope (TermViewInv.envVR_solo hvI hc0 hth) hr (frRunA_ext hfr hx) hfr.2.1
    have hfb' := FrBound_foot hF (tstep_wrUp _ _ _ _ r hr) hfb hfr.1
    have hIL' := IniLoc_foot hF (fun _ h => h) hfb hIL
    have hlt := MemInv_promLt hm
    have hvf := tstep_vful _ _ _ _ r hr
    have hsub := (tstep_fulfil hlt (MemInv_nopair hm) hr).1
    have hB' := HoldB_foot hB hF hlt hvf.1 hvf.2.1 (fun t ht hn => hvf.2.2 t ht (hlt t ht) hn)
      (fun u hu => .inl (hsub.subset hu))
    refine ⟨solo_trans hc0 (.thread hs (.refl _)), r.2.2, E', e3, Ext_trans hx hx', hT', ?_,
      StoClo_EFoot hF.1 hSC, by rw [gOf_thread hs]; exact hbo, hfb'.1, ?_, ?_, hIL',
      IniHeld_foot hF (tstep_wrUp _ _ _ _ r hr).1 hfb (hHr c0 hc0 hcert0 th hth) hIH⟩
    · rw [gOf_thread hs, e1, e2]
      exact hm'
    · rw [e1, e2]
      exact ⟨hfb'.2, hA', hfr.2.2⟩
    · rw [e1, e2]
      exact hB'
  · rintro c0 a v w ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hB, hIL, hIH⟩ hw _
    refine ⟨solo_trans hc0 (.prom a v w hw (.refl _)), _, E,
      (promise_inv (a := a) (v := v) (w := w) hth).2.1, hx, hTE, ?_, hSC, by rw [gOf_promise]; exact hbo,
      hfb, ?_, ?_, hIL, hIH⟩
    · rw [gOf_promise, (promise_inv (a := a) (v := v) (w := w) hth).2.2]
      exact MemInv_promSt hm
    · exact frRunA_prom hth hfr
    · rw [(promise_inv (a := a) (v := v) (w := w) hth).2.2]
      exact HoldB_promSt hB (MemInv_promLt hm)
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hB, hIL, hIH⟩ hs _
    obtain ⟨x1, a1, e1, evs, hterm, rfl⟩ := extSteps_thread hs hth
    exact ⟨solo_trans hc0 (.ext hs (.refl _)), _, E, set_self hth, hx, TermTyped.ThInvE_emit hterm hTE,
      by rw [gOf_ext hs]; exact hm, hSC, by rw [gOf_ext hs]; exact hbo, hfb, hfr, hB, hIL, hIH⟩

/-- (S1b) `InvAtXHZ` with the run's publish provenance `PfrProvE` from the run start `st`. -/
def InvAtXHP (Z : AllocLabel → Prop) (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv)
    (n0 v0 : Nat) (pb : AllocLabel → Ts) (st c : Cfg) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) : Prop :=
  ∃ th E, c.ths[i]? = some th ∧ Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) ∧
    HoldB E0 pb E (stOf c.mem c.pairs th) ∧ IniLoc Z E0 E ∧ IniHeld H E0 E th.vs.vWr ∧
    TermK5Defs.PfrProvE p k arch i H E0 st c E ∧ TermK5O.PfrProvO p k arch i H E0 st c E

theorem InvAtXHP.toH {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {n0 v0 : Nat}
    {pb : AllocLabel → Ts} {st c : Cfg} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop}
    (h : InvAtXHP Z p k arch i E0 n0 v0 pb st c H) : InvAtXHZ Z p k arch i E0 n0 v0 pb c H :=
  let ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, _⟩ := h
  ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩

/-- (S1b) The tied invariant with the publish provenance, restarted right after the plant's
promise step (the run start). -/
theorem InvAtXHP_promOf {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP : Cfg} {thP : TTh}
    {E0 : TEnv} {a0 : Address} {vB : WeakMem.Val} {w : Ts}
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true) (hrl0 : ∀ l, E0.rini l ≤ E0.ini l) (hrc0 : TermTyped.RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1)
    (Z : AllocLabel → Prop := fun _ => False) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) :
    InvAtXHP Z p k arch i E0 (cP.mem.size + 1) thP.vs.vWr
      (plantF E0 (promSt (stOf cP.mem cP.pairs thP) a0 vB w)) (promise cP i a0 vB w) (promise cP i a0 vB w) H := by
  have hpi := promise_inv (a := a0) (v := vB) (w := w) hthP
  have hs : (promise cP i a0 vB w).mem.size = cP.mem.size + 1 := by rw [hpi.1, Array.size_push]
  refine ⟨_, E0, hpi.2.1, ?_, hT0, by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm0, hSC,
    by rw [gOf_promise]; exact hbo, FrBound_refl _ _ _, ⟨⟨Nat.le_refl _, by show cP.mem.size + 1 ≤ (promise cP i a0 vB w).mem.size; rw [hs]; exact Nat.le_refl _,
      fun _ _ h0 h => absurd (h0.symm.trans h) (fun e => by cases e)⟩, anchR_prom hthP (anchR_start hm0 hrc0 hfl0), .inl rfl⟩, ?_, IniLoc_refl _ _, IniHeld_refl _ _ _, TermK5P.pfrProvE_start _ _ _ _ _ _ _,
      TermK5O.pfrProvO_start _ _ _ _ _ _ _⟩
  · obtain ⟨ρ, η, cx, rfl, -⟩ := hT0
    exact Ext_refl (Coh_CE η) (CohR_CE η)
  · rw [hpi.2.2]; exact HoldB_start hrl0

theorem solo_typedXHP {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} {E0 : TEnv}
    {n0 v0 : Nat} {pb : AllocLabel → Ts} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    {st : Cfg} (h0 : InvAtXHP Z p k arch i E0 n0 v0 pb st c H) {c2 : Cfg} (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i)
    (hrl : ∀ l, E0.rini l ≤ E0.ini l)
    (hZp : ∀ c1 th1 c1' c3 th3 l cl, TermOwnG0Defs.SoloNP p k arch i l st c1 → c1.ths[i]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c3 →
      Certified p k arch c3 i → c3.ths[i]? = some th3 → E0.sto l = some cl → cl.owner = some E0.tid →
      ¬ BufInitOn th3 l)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    InvAtXHP Z p k arch i E0 n0 v0 pb st c2 H := by
  refine (run_inv (c1 := c2) (P := fun c0 => Solo p k arch i c c0 ∧ InvAtXHP Z p k arch i E0 n0 v0 pb st c0 H) ?_ ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hB, hIL, hIH, hPV, hPO⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
    rw [hth] at hth'
    cases hth'
    obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩ := hTE
    have hscope := hsc c0 hc0 hcert0 th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT htv hi
    obtain ⟨-, hstep⟩ := TermK5P.tstep_footprintKQ (hRP := hrp) (hPS := hPS) (hSub := hSub) (hSig := hSig)
      (g := { ({ gOf p k arch c0 i with
          zf := fun l => Z l ∨ TermK5P.PubZ E0 (CE η) l ∨ TermK5O.PubZO p k arch i E0 st c0 l } : G) with
        pf := fun l => TermOwnG0Defs.PubAt th l }) hP rfl
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)))
      (tstep_notDone hr) hscope hT hi hE htv hm hbo (PAx_of_step hs hc0' hth)
      (hwin c0 hc0 hcert0 th hth ρ η cx hE hT htv hi hm (frRunA_ext hfr hx) hfr.2.1.1 hfr.2.1.2.2.1)
      (fun l hbi hz => hz.elim (hZr c0 hc0 hcert0 th hth l hbi) fun hz => hz.elim
        (TermK5P.pubZ_noBufInit hPV (fun c1 th1 c1' l cl h1 h2 h3 h4 h5 h6 h7 _ =>
          hZp c1 th1 c1' c0 th l cl h1 h2 h3 h4 h5 hcert0 hth h6 h7) l hbi)
        (TermK5O.pubZO_noBufInit (fun c1 th1 c1' l cl _ h1 h2 h3 h4 h5 h6 h7 _ =>
          hZp c1 th1 c1' c0 th l cl h1 h2 h3 h4 h5 hcert0 hth h6 h7) l hbi))
      (fun _ h => h)
    obtain ⟨E', hF, hx', hT', hm', hD, hbB⟩ := hstep r hr hpa
    have hA' := anchR_tstep hF hm' hbB hE hT htv hi hm hscope (TermViewInv.envVR_solo hvI hc0 hth) hr (frRunA_ext hfr hx) hfr.2.1
    have hfb' := FrBound_foot hF (tstep_wrUp _ _ _ _ r hr) hfb hfr.1
    have hIL' := IniLoc_foot hF (fun _ h => .inl h) hfb hIL
    have hlt := MemInv_promLt hm
    have hvf := tstep_vful _ _ _ _ r hr
    have hsub := (tstep_fulfil hlt (MemInv_nopair hm) hr).1
    have hB' := HoldB_foot hB hF hlt hvf.1 hvf.2.1 (fun t ht hn => hvf.2.2 t ht (hlt t ht) hn)
      (fun u hu => .inl (hsub.subset hu))
    refine ⟨solo_trans hc0 (.thread hs (.refl _)), r.2.2, E', e3, Ext_trans hx hx', hT', ?_,
      StoClo_EFoot hF.1 hSC, by rw [gOf_thread hs]; exact hbo, hfb'.1, ?_, ?_, hIL',
      IniHeld_foot hF (tstep_wrUp _ _ _ _ r hr).1 hfb (hHr c0 hc0 hcert0 th hth) hIH, ?_, ?_⟩
    · rw [gOf_thread hs, e1, e2]
      exact hm'
    · rw [e1, e2]
      exact ⟨hfb'.2, hA', hfr.2.2⟩
    · rw [e1, e2]
      exact hB'
    · exact TermK5P.pfrProv_thread hPV hF hfb (fun _ h => h) (fun _ h => .inr (.inl h)) hD hs hth
        (fun l hl => TermK5V.pub_vWr hl hr)
        ((IniHeld_foot hF (tstep_wrUp _ _ _ _ r hr).1 hfb (hHr c0 hc0 hcert0 th hth) hIH) hrl).2.1
    · exact TermK5O.pfrProvO_thread hPO hF hfb hx (fun _ h => .inr (.inr h)) hs hth
        (fun l hl => TermK5V.pub_vWr hl hr)
        ((IniHeld_foot hF (tstep_wrUp _ _ _ _ r hr).1 hfb (hHr c0 hc0 hcert0 th hth) hIH) hrl).2.1
  · rintro c0 a v w ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hB, hIL, hIH, hPV, hPO⟩ hw _
    refine ⟨solo_trans hc0 (.prom a v w hw (.refl _)), _, E,
      (promise_inv (a := a) (v := v) (w := w) hth).2.1, hx, hTE, ?_, hSC, by rw [gOf_promise]; exact hbo,
      hfb, ?_, ?_, hIL, hIH, TermK5P.pfrProv_prom hPV hw, TermK5O.pfrProvO_prom hPO hw⟩
    · rw [gOf_promise, (promise_inv (a := a) (v := v) (w := w) hth).2.2]
      exact MemInv_promSt hm
    · exact frRunA_prom hth hfr
    · rw [(promise_inv (a := a) (v := v) (w := w) hth).2.2]
      exact HoldB_promSt hB (MemInv_promLt hm)
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hB, hIL, hIH, hPV, hPO⟩ hs _
    obtain ⟨x1, a1, e1, evs, hterm, rfl⟩ := extSteps_thread hs hth
    exact ⟨solo_trans hc0 (.ext hs (.refl _)), _, E, set_self hth, hx, TermTyped.ThInvE_emit hterm hTE,
      by rw [gOf_ext hs]; exact hm, hSC, by rw [gOf_ext hs]; exact hbo, hfb, hfr, hB, hIL, hIH,
      TermK5P.pfrProv_ext hPV hs, TermK5O.pfrProvO_ext hPO hs⟩


theorem certified_promTypedXH {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv}
    {n0 v0 : Nat} {pb : AllocLabel → Ts} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (h0 : InvAtXHZ Z p k arch i E0 n0 v0 pb c H) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    ∃ c1 c2 th1 th2 ρ η cx E2, Solo p k arch i c c1 ∧ Certified p k arch c1 i ∧
      c2 ∈ threadSteps p k arch c1 i ∧ Certified p k arch c2 i ∧
      c1.ths[i]? = some th1 ∧ c2.ths[i]? = some th2 ∧
      Ext E0 (CE η) ∧ EnvOK p η ∧ Typed p cx th1.term ∧ TvOK cx ∧
      FInv ρ η th1.σs (Resume p th1.stack) cx th1.env ∧
      MemInv (gOf p k arch c1 i) (CE η) (stOf c1.mem c1.pairs th1) ∧ ScopeD th1.σs cx th1.term ∧
      PromAbove (stOf c1.mem c1.pairs th1) ∧
      Ext E0 E2 ∧ ThInvE p E2 th2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      c1.mem[t]? = some m ∧ c2.mem[t]? = some m ∧ t ∈ th1.promises ∧ t ∉ th2.promises ∧
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 m.loc m.val ∧ FrBound E0 n0 v0 E2 ∧
      HoldB E0 pb E2 (stOf c2.mem c2.pairs th2) ∧ IniLoc Z E0 E2 ∧ IniHeld H E0 E2 th2.vs.vWr := by
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, hm1, ht1, hn2, hsw⟩ :=
    certified_fulfilC hc (pwf_of_inv h0.toX.toInvAt) ht
  rw [hm] at hm'
  cases hm'
  have hc1 : Certified p k arch c1 i := certified_back (.thread h2 (.refl _)) hc2
  obtain ⟨th1', E1, hth1', hx1, ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩, hmi1, -⟩ := solo_typedX hP hsc hvI hwin h0.toX h1 hc1 hPS hSub hSig hZr hHr
  rw [hth1] at hth1'
  cases hth1'
  have h12 : Solo p k arch i c c2 := solo_trans h1 (.thread h2 (.refl _))
  obtain ⟨th2, E2, hth2, hx2, hT2, hm2i, -, -, hfb2, -, hB2, hIL2, hIH2⟩ := solo_typedXH hP hsc hvI hwin h0 h12 hc2 hPS hSub hSig hZr hHr
  obtain ⟨th', r, hth', hr, e1, -, -, -⟩ := threadSteps_inv h2
  rw [hth1] at hth'
  cases hth'
  have hm2 : c2.mem[t]? = some m := by rw [e1]; exact (tstep_grow hr).1 t m hm1
  refine ⟨c1, c2, th1, th2, ρ, η, cx, E2, h1, hc1, h2, hc2, hth1, hth2, hx1, hE, hT, htv, hi, hmi1,
    hsc c1 h1 hc1 th1 hth1 (TermTyped.not_spawnT_of_steps hth1 h2) ρ η cx hE hT htv hi, certified_promAboveSt hc1 hth1, hx2, hT2, hm2i, hm1, hm2,
    ht1, ?_, hsw, hfb2, hB2, hIL2, hIH2⟩
  rwa [promsOf_some hth2] at hn2


theorem certified_promNotUndefXH {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {E0 : TEnv} {n0 v0 : Nat} {pb : AllocLabel → Ts} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (h0 : InvAtXHZ Z p k arch i E0 n0 v0 pb c H) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    m.val ≠ .undef ∧ ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧
      c2.ths[i]? = some th2 ∧ Ext E0 E2 ∧ ThInvE p E2 th2 ∧
      MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      (∀ cl, E0.sto m.loc.label = some cl → WordOK E2 cl.ty m.loc.offset (mw m)) ∧
      FrBound E0 n0 v0 E2 ∧ HoldB E0 pb E2 (stOf c2.mem c2.pairs th2) ∧ IniLoc Z E0 E2 ∧ IniHeld H E0 E2 th2.vs.vWr := by
  obtain ⟨c1, c2, th1, th2, ρ, η, cx, E2, h1, hc1, h2, hc2, hth1, hth2, -, hE, hT, htv, hi, hmi1, hscope, -,
    hx2, hT2, hm2i, hm1, hm2, ht1, hn2, hsw, hfb2, hB2, hIL2, hIH2⟩ :=
    certified_promTypedXH hP hsc hvI hwin h0 hc ht hm hPS hSub hSig hZr hHr
  replace hscope := TermTyped.scopeD_SW hscope hsw
  have hnu : m.val ≠ .undef := by
    rcases SW_nundef hE hT htv hi hscope hsw with hnu | ⟨x, o, acq, rel, a, v, e, he⟩
    · exact hnu
    · obtain ⟨th', r, hth', hr, -, -, e3, hpr⟩ := taken_promAbove h2 hc2
      rw [hth1] at hth'
      cases hth'
      rw [hth2] at e3
      obtain rfl := Option.some.inj e3
      obtain ⟨n, hn⟩ := fetch_ful_num he hP hT hi hE htv hmi1 hscope hr hpr ht1 hn2 hm1
      rw [hn]; intro h; cases h
  refine ⟨hnu, c2, th2, E2, solo_trans h1 (.thread h2 (.refl _)), hc2, hth2, hx2, hT2, hm2i,
    fun cl hcl => ?_, hfb2, hB2, hIL2, hIH2⟩
  rcases hm2i.1.1 t m cl hn2 hm2 (hx2.2.2.2.2.1 _ _ hcl) with h | h
  · exact absurd h hnu
  · exact h


theorem certified_holderWordH {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP c' : Cfg}
    {thP : TTh} {E0 : TEnv} {a0 : Address} {vB : WeakMem.Val} {w : Ts} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 vB w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hrc0 : TermTyped.RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true) (hrl0 : ∀ l, E0.rini l ≤ E0.ini l)
    (hsolo : Solo p k arch i (promise cP i a0 vB w) c') (hc' : Certified p k arch c' i)
    {u : Ts} {m : Msg} (hu : u ∈ thP.promises) (hm : cP.mem[u]? = some m) {cl : Cell}
    (hcl : E0.sto m.loc.label = some cl) {Z : AllocLabel → Prop}
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i (promise cP i a0 vB w) c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h) :
    ∃ c2 th2 E2, Solo p k arch i (promise cP i a0 vB w) c2 ∧ Certified p k arch c2 i ∧
      c2.ths[i]? = some th2 ∧ Ext E0 E2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      WordOK E2 cl.ty m.loc.offset (mw m) ∧ FrBound E0 (cP.mem.size + 1) thP.vs.vWr E2 ∧
      HoldB E0 (plantF E0 (promSt (stOf cP.mem cP.pairs thP) a0 vB w)) E2 (stOf c2.mem c2.pairs th2) ∧
      IniLoc Z E0 E2 ∧ IniHeld (WitP cP.mem thP.promises) E0 E2 th2.vs.vWr := by
  have hpi := promise_inv (a := a0) (v := vB) (w := w) hthP
  have hc : Certified p k arch (promise cP i a0 vB w) i := certified_back hsolo hc'
  have h0 := InvAtXH_promOf (hrc0 := hrc0) (hfl0 := hfl0) (k := k) (arch := arch) (a0 := a0) (vB := vB) (w := w) hthP hT0 hm0 hSC hbo hrl0 Z
    (WitP cP.mem thP.promises)
  have ht : u ∈ promsOf (promise cP i a0 vB w) i := by
    rw [promsOf_some hpi.2.1]; exact List.mem_append_left _ hu
  have hlt : u < cP.mem.size := hm0.2.2.1 u hu
  have hm' : (promise cP i a0 vB w).mem[u]? = some m := by
    rw [hpi.1]; show (cP.mem.push _)[u]? = some m
    rw [Array.getElem?_push_lt hlt, ← hm]; simp [hlt]
  obtain ⟨-, c2, th2, E2, h2, hc2, hth2, hx2, -, hm2, hw2, hfb2, hB2, hIL2, hIH2⟩ :=
    certified_promNotUndefXH hP hsc hvI hwin h0 hc ht hm' hPS hSub hSig hZr
      (witP_run hthP hm0.2.2.1 (winInv_prom (winInv_refl hthP)))
  exact ⟨c2, th2, E2, h2, hc2, hth2, hx2, hm2, hw2 cl hcl, hfb2, hB2, hIL2, hIH2⟩


theorem certified_hinhW1H {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP c' : Cfg}
    {thP : TTh} {E0 : TEnv} {a0 : Address} {vB : WeakMem.Val} {w : Ts} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 vB w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hrc0 : TermTyped.RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true) (hrl0 : ∀ l, E0.rini l ≤ E0.ini l)
    (hsolo : Solo p k arch i (promise cP i a0 vB w) c') (hc' : Certified p k arch c' i)
    {Lp : AllocLabel → Prop}
    (hL : ∀ l, Lp l → ∃ c, E0.sto l = some c ∧ c.owner = some E0.tid)
    (hnone : ∀ l, Lp l → E0.pfr l = none)
    (hLcl : ∀ l, Lp l → ∀ u ∈ thP.promises, ∀ m, cP.mem[u]? = some m → m.loc.label = l →
      ∀ (a : Address) (g : Nat), m.val = .loc a g → ∀ cl, E0.sto a.label = some cl →
      cl.owner = some E0.tid → E0.pfr a.label = none → Lp a.label)
    (hfp : ∀ a cl, E0.sto a = some cl → E0.pfr a = none → cl.owner = some E0.tid)
    (hpv : ∀ u ∈ thP.promises, ∀ m, cP.mem[u]? = some m → m.view < cP.mem.size)
    {Z : AllocLabel → Prop}
    (hres : ∀ c2 th2 E2, Solo p k arch i (promise cP i a0 vB w) c2 → Certified p k arch c2 i →
      c2.ths[i]? = some th2 → Ext E0 E2 → MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) →
      FrBound E0 (cP.mem.size + 1) thP.vs.vWr E2 →
      HoldB E0 (plantF E0 (promSt (stOf cP.mem cP.pairs thP) a0 vB w)) E2 (stOf c2.mem c2.pairs th2) →
      IniLoc Z E0 E2 → IniHeld (WitP cP.mem thP.promises) E0 E2 th2.vs.vWr →
      RunAgree E0 (plantE E0 (stOf cP.mem cP.pairs thP) Lp) Lp E2)
    {l : AllocLabel} {c : Cell} (hl : Lp l) (hc : E0.sto l = some c) {b : Nat} {S : Ty} {us : List Acc}
    (hseg : SegOf c.ty b S) (hus : accs S = some us) (h1 : nWords us = 1)
    (hnS : Ty.noOwnIn [] S = true) (hrS : rgnFree S = true)
    (hini : IniSeg (plantE E0 (stOf cP.mem cP.pairs thP) Lp) c l b) (hnot : ¬ IniSeg E0 c l b)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i (promise cP i a0 vB w) c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h) :
    ∃ ws, ValOf (plantE E0 (stOf cP.mem cP.pairs thP) Lp) S ws ∧ ws.length = nWords us := by
  rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us', j, hT, hus', hjN, rfl⟩
  · exact absurd (fun N e hT => by rw [hT] at hA; simp [accs] at hA) hnot
  rw [hus] at hus'
  cases hus'
  rw [h1]
  simp only [h1, Nat.mul_one] at hini hnot
  -- the slot is in the maximal held prefix, above the start count
  have hge : E0.ini l ≤ j := Nat.le_of_not_lt fun hlt =>
    hnot fun N' e' hT' => by
      rw [hT] at hT'
      simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
      obtain ⟨-, rfl⟩ := hT'
      exact ⟨us, j, hus, hlt, by rw [h1, Nat.mul_one]⟩
  have hjI : j < max (E0.ini l) (Np E0 (stOf cP.mem cP.pairs thP) l) := by
    obtain ⟨us2, j2, hus2, hj2, e⟩ := hini N S hT
    rw [hus] at hus2; cases hus2
    rw [h1, Nat.mul_one] at e; subst e
    rw [plantE_ini_in hl, NpZ_eq_of_pos hc hT hus (by rw [h1]; decide)] at hj2; exact hj2
  have hjN : j < Np E0 (stOf cP.mem cP.pairs thP) l := by
    rcases Nat.le_total (E0.ini l) (Np E0 (stOf cP.mem cP.pairs thP) l) with h | h
    · rw [Nat.max_eq_right h] at hjI; exact hjI
    · rw [Nat.max_eq_left h] at hjI; omega
  rcases PrefixHeld_Np hc N S us hT hus j (by rw [h1, Nat.mul_one]; exact hjN) with hI | ⟨u, hu, m, hm, hloc⟩
  · have := hI N S us hT hus; rw [h1, Nat.mul_one] at this; omega
  have hu' : u ∈ thP.promises := hu
  have hm' : cP.mem[u]? = some m := hm
  have hcl : E0.sto m.loc.label = some c := by rw [hloc]; exact hc
  obtain ⟨c2, th2, E2, h2, hc2, hth2, hx2, hm2, hw2, hfb2, hB2, hIL2, hIH2⟩ :=
    certified_holderWordH (hrc0 := hrc0) (hfl0 := hfl0) hP hsc hvI hwin hthP hT0 hm0 hSC hbo hrl0 hsolo hc' hu' hm' hcl hPS hSub hSig hZr
  rw [hT] at hw2
  obtain ⟨w0, hV, hle⟩ := wordOK_slot1 hw2 hus h1
  have hR := hres c2 th2 E2 h2 hc2 hth2 hx2 hm2 hfb2 hB2 hIL2 hIH2
  have hbi := hm2.2.2.2.2.2.2.2.2.2.1
  refine ⟨[w0], ValOf_monoK (G := PlantG E0 Lp) hnS hrS hus (by rw [h1]; rfl) hx2.2.2.1 hx2.2.2.2.1
    (fun a c0 hG hc0 => ?_) (fun a hG => ?_) (fun a f hG hf => ?_) (fun a B hG hB => ?_) hR.pay ?_ hV, rfl⟩
  · show E0.sto a = some c0
    rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B, hB⟩
    · rw [hx2.2.2.2.2.1 a c1 h1'] at hc0; rw [h1', hc0]
    · obtain ⟨c1, h1', -⟩ := hL a hLa
      rw [hx2.2.2.2.2.1 a c1 h1'] at hc0; rw [h1', hc0]
    · have := (hbi.2.2 a B (hx2.2.2.2.2.2.2.2.2.1 a B hB)).1
      rw [hc0] at this; cases this
  · rcases hG with hG | hLa | ⟨B, hB⟩
    · exact hR.ini a (.inl hG)
    · exact hR.ini a (.inr hLa)
    · rw [(hbi.2.2 a B (hx2.2.2.2.2.2.2.2.2.1 a B hB)).2.1]; exact Nat.zero_le _
  · rcases hG with ⟨c1, f0, h1', hf0⟩ | hLa | hB
    · have hnL : ¬ Lp a := fun hLa => by rw [hnone a hLa] at hf0; cases hf0
      rw [hx2.2.2.2.2.2.2.1 a f0 hf0] at hf
      cases hf
      exact ⟨_, by rw [plantE_pfr_ne hnL]; exact hf0, Nat.le_refl _⟩
    · exact hR.pfr a f (.inl hLa) hf
    · exact hR.pfr a f (.inr hB) hf
  · show E0.box a = some B
    rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B0, hB0⟩
    · have := (hbi.2.2 a B hB).1
      rw [hx2.2.2.2.2.1 a c1 h1'] at this; cases this
    · obtain ⟨c1, h1', -⟩ := hL a hLa
      have := (hbi.2.2 a B hB).1
      rw [hx2.2.2.2.2.1 a c1 h1'] at this; cases this
    · rw [hx2.2.2.2.2.2.2.2.2.1 a B0 hB0] at hB; rw [hB0, hB]
  · -- the slot word's reference names a start label
    intro w1 hw1 a g hv
    rw [List.mem_singleton] at hw1
    subst hw1
    have hJ := noJunk_valOf hV hnS hrS hus (by rw [h1]; rfl) w1 (List.mem_singleton_self _) a g hv
    have hvm : w1.view ≤ m.view := hle.2 a g hv
    have hmv : m.val = .loc a g := by rw [← hv]; exact hle.1.symm
    rcases FrBound_inspM hfb2 hJ (Nat.lt_of_le_of_lt hvm (hpv u hu' m hm')) with ⟨c1, hc1⟩ | ⟨B, hB⟩
    · rcases hpf : E0.pfr a.label with _ | f
      · exact .inr (.inl (hLcl l hl u hu' m hm' (by rw [hloc]) a g hmv c1 hc1 (hfp _ c1 hc1 hpf) hpf))
      · exact .inl ⟨c1, f, hc1, hpf⟩
    · exact .inr (.inr ⟨B, hB⟩)

theorem certified_promTypedXHP {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv}
    {n0 v0 : Nat} {pb : AllocLabel → Ts} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    {st : Cfg} (h0 : InvAtXHP Z p k arch i E0 n0 v0 pb st c H) (hc : Certified p k arch c i)
    (hrl : ∀ l, E0.rini l ≤ E0.ini l)
    (hZp : ∀ c1 th1 c1' c3 th3 l cl, TermOwnG0Defs.SoloNP p k arch i l st c1 → c1.ths[i]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c3 →
      Certified p k arch c3 i → c3.ths[i]? = some th3 → E0.sto l = some cl → cl.owner = some E0.tid →
      ¬ BufInitOn th3 l)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    ∃ c1 c2 th1 th2 ρ η cx E2, Solo p k arch i c c1 ∧ Certified p k arch c1 i ∧
      c2 ∈ threadSteps p k arch c1 i ∧ Certified p k arch c2 i ∧
      c1.ths[i]? = some th1 ∧ c2.ths[i]? = some th2 ∧
      Ext E0 (CE η) ∧ EnvOK p η ∧ Typed p cx th1.term ∧ TvOK cx ∧
      FInv ρ η th1.σs (Resume p th1.stack) cx th1.env ∧
      MemInv (gOf p k arch c1 i) (CE η) (stOf c1.mem c1.pairs th1) ∧ ScopeD th1.σs cx th1.term ∧
      PromAbove (stOf c1.mem c1.pairs th1) ∧
      Ext E0 E2 ∧ ThInvE p E2 th2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      c1.mem[t]? = some m ∧ c2.mem[t]? = some m ∧ t ∈ th1.promises ∧ t ∉ th2.promises ∧
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 m.loc m.val ∧ FrBound E0 n0 v0 E2 ∧
      HoldB E0 pb E2 (stOf c2.mem c2.pairs th2) ∧ IniLoc Z E0 E2 ∧ IniHeld H E0 E2 th2.vs.vWr ∧
      TermK5Defs.PfrProvE p k arch i H E0 st c2 E2 ∧ TermK5O.PfrProvO p k arch i H E0 st c2 E2 := by
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, hm1, ht1, hn2, hsw⟩ :=
    certified_fulfilC hc (pwf_of_inv h0.toH.toX.toInvAt) ht
  rw [hm] at hm'
  cases hm'
  have hc1 : Certified p k arch c1 i := certified_back (.thread h2 (.refl _)) hc2
  obtain ⟨th1', E1, hth1', hx1, ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩, hmi1, -⟩ := solo_typedX hP hsc hvI hwin h0.toH.toX h1 hc1 hPS hSub hSig hZr hHr
  rw [hth1] at hth1'
  cases hth1'
  have h12 : Solo p k arch i c c2 := solo_trans h1 (.thread h2 (.refl _))
  obtain ⟨th2, E2, hth2, hx2, hT2, hm2i, -, -, hfb2, -, hB2, hIL2, hIH2, hPV2, hPO2⟩ := solo_typedXHP hP hsc hvI hwin h0 h12 hc2 hrl hZp hPS hSub hSig hZr hHr
  obtain ⟨th', r, hth', hr, e1, -, -, -⟩ := threadSteps_inv h2
  rw [hth1] at hth'
  cases hth'
  have hm2 : c2.mem[t]? = some m := by rw [e1]; exact (tstep_grow hr).1 t m hm1
  refine ⟨c1, c2, th1, th2, ρ, η, cx, E2, h1, hc1, h2, hc2, hth1, hth2, hx1, hE, hT, htv, hi, hmi1,
    hsc c1 h1 hc1 th1 hth1 (TermTyped.not_spawnT_of_steps hth1 h2) ρ η cx hE hT htv hi, certified_promAboveSt hc1 hth1, hx2, hT2, hm2i, hm1, hm2,
    ht1, ?_, hsw, hfb2, hB2, hIL2, hIH2, hPV2, hPO2⟩
  rwa [promsOf_some hth2] at hn2

theorem certified_promNotUndefXHP {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {E0 : TEnv} {n0 v0 : Nat} {pb : AllocLabel → Ts} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    {st : Cfg} (h0 : InvAtXHP Z p k arch i E0 n0 v0 pb st c H) (hc : Certified p k arch c i)
    (hrl : ∀ l, E0.rini l ≤ E0.ini l)
    (hZp : ∀ c1 th1 c1' c3 th3 l cl, TermOwnG0Defs.SoloNP p k arch i l st c1 → c1.ths[i]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c3 →
      Certified p k arch c3 i → c3.ths[i]? = some th3 → E0.sto l = some cl → cl.owner = some E0.tid →
      ¬ BufInitOn th3 l)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    m.val ≠ .undef ∧ ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧
      c2.ths[i]? = some th2 ∧ Ext E0 E2 ∧ ThInvE p E2 th2 ∧
      MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      (∀ cl, E0.sto m.loc.label = some cl → WordOK E2 cl.ty m.loc.offset (mw m)) ∧
      FrBound E0 n0 v0 E2 ∧ HoldB E0 pb E2 (stOf c2.mem c2.pairs th2) ∧ IniLoc Z E0 E2 ∧ IniHeld H E0 E2 th2.vs.vWr ∧
      TermK5Defs.PfrProvE p k arch i H E0 st c2 E2 ∧ TermK5O.PfrProvO p k arch i H E0 st c2 E2 := by
  obtain ⟨c1, c2, th1, th2, ρ, η, cx, E2, h1, hc1, h2, hc2, hth1, hth2, -, hE, hT, htv, hi, hmi1, hscope, -,
    hx2, hT2, hm2i, hm1, hm2, ht1, hn2, hsw, hfb2, hB2, hIL2, hIH2, hPV2, hPO2⟩ :=
    certified_promTypedXHP hP hsc hvI hwin h0 hc hrl hZp ht hm hPS hSub hSig hZr hHr
  replace hscope := TermTyped.scopeD_SW hscope hsw
  have hnu : m.val ≠ .undef := by
    rcases SW_nundef hE hT htv hi hscope hsw with hnu | ⟨x, o, acq, rel, a, v, e, he⟩
    · exact hnu
    · obtain ⟨th', r, hth', hr, -, -, e3, hpr⟩ := taken_promAbove h2 hc2
      rw [hth1] at hth'
      cases hth'
      rw [hth2] at e3
      obtain rfl := Option.some.inj e3
      obtain ⟨n, hn⟩ := fetch_ful_num he hP hT hi hE htv hmi1 hscope hr hpr ht1 hn2 hm1
      rw [hn]; intro h; cases h
  refine ⟨hnu, c2, th2, E2, solo_trans h1 (.thread h2 (.refl _)), hc2, hth2, hx2, hT2, hm2i,
    fun cl hcl => ?_, hfb2, hB2, hIL2, hIH2, hPV2, hPO2⟩
  rcases hm2i.1.1 t m cl hn2 hm2 (hx2.2.2.2.2.1 _ _ hcl) with h | h
  · exact absurd h hnu
  · exact h

theorem certified_holderWordHP {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP c' : Cfg}
    {thP : TTh} {E0 : TEnv} {a0 : Address} {vB : WeakMem.Val} {w : Ts} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 vB w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hrc0 : TermTyped.RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true) (hrl0 : ∀ l, E0.rini l ≤ E0.ini l)
    (hsolo : Solo p k arch i (promise cP i a0 vB w) c') (hc' : Certified p k arch c' i)
    {u : Ts} {m : Msg} (hu : u ∈ thP.promises) (hm : cP.mem[u]? = some m) {cl : Cell}
    (hcl : E0.sto m.loc.label = some cl) {Z : AllocLabel → Prop}
    (hZp : ∀ c1 th1 c1' c3 th3 l cl, TermOwnG0Defs.SoloNP p k arch i l (promise cP i a0 vB w) c1 → c1.ths[i]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c3 →
      Certified p k arch c3 i → c3.ths[i]? = some th3 → E0.sto l = some cl → cl.owner = some E0.tid →
      ¬ BufInitOn th3 l)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i (promise cP i a0 vB w) c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h) :
    ∃ c2 th2 E2, Solo p k arch i (promise cP i a0 vB w) c2 ∧ Certified p k arch c2 i ∧
      c2.ths[i]? = some th2 ∧ Ext E0 E2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      WordOK E2 cl.ty m.loc.offset (mw m) ∧ FrBound E0 (cP.mem.size + 1) thP.vs.vWr E2 ∧
      HoldB E0 (plantF E0 (promSt (stOf cP.mem cP.pairs thP) a0 vB w)) E2 (stOf c2.mem c2.pairs th2) ∧
      IniLoc Z E0 E2 ∧ IniHeld (WitP cP.mem thP.promises) E0 E2 th2.vs.vWr ∧
      TermK5Defs.PfrProvE p k arch i (WitP cP.mem thP.promises) E0 (promise cP i a0 vB w) c2 E2 ∧
      TermK5O.PfrProvO p k arch i (WitP cP.mem thP.promises) E0 (promise cP i a0 vB w) c2 E2 := by
  have hpi := promise_inv (a := a0) (v := vB) (w := w) hthP
  have hc : Certified p k arch (promise cP i a0 vB w) i := certified_back hsolo hc'
  have h0 := InvAtXHP_promOf (hrc0 := hrc0) (hfl0 := hfl0) (k := k) (arch := arch) (a0 := a0) (vB := vB) (w := w) hthP hT0 hm0 hSC hbo hrl0 Z
    (WitP cP.mem thP.promises)
  have ht : u ∈ promsOf (promise cP i a0 vB w) i := by
    rw [promsOf_some hpi.2.1]; exact List.mem_append_left _ hu
  have hlt : u < cP.mem.size := hm0.2.2.1 u hu
  have hm' : (promise cP i a0 vB w).mem[u]? = some m := by
    rw [hpi.1]; show (cP.mem.push _)[u]? = some m
    rw [Array.getElem?_push_lt hlt, ← hm]; simp [hlt]
  obtain ⟨-, c2, th2, E2, h2, hc2, hth2, hx2, -, hm2, hw2, hfb2, hB2, hIL2, hIH2, hPV2, hPO2⟩ :=
    certified_promNotUndefXHP hP hsc hvI hwin h0 hc hrl0 hZp ht hm' hPS hSub hSig hZr
      (witP_run hthP hm0.2.2.1 (winInv_prom (winInv_refl hthP)))
  exact ⟨c2, th2, E2, h2, hc2, hth2, hx2, hm2, hw2 cl hcl, hfb2, hB2, hIL2, hIH2, hPV2, hPO2⟩

theorem certified_hinhW1HP {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP c' : Cfg}
    {thP : TTh} {E0 : TEnv} {a0 : Address} {vB : WeakMem.Val} {w : Ts} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 vB w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hrc0 : TermTyped.RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true) (hrl0 : ∀ l, E0.rini l ≤ E0.ini l)
    (hsolo : Solo p k arch i (promise cP i a0 vB w) c') (hc' : Certified p k arch c' i)
    {Lp : AllocLabel → Prop}
    (hL : ∀ l, Lp l → ∃ c, E0.sto l = some c ∧ c.owner = some E0.tid)
    (hnone : ∀ l, Lp l → E0.pfr l = none)
    (hLcl : ∀ l, Lp l → ∀ u ∈ thP.promises, ∀ m, cP.mem[u]? = some m → m.loc.label = l →
      ∀ (a : Address) (g : Nat), m.val = .loc a g → ∀ cl, E0.sto a.label = some cl →
      cl.owner = some E0.tid → E0.pfr a.label = none → Lp a.label)
    (hfp : ∀ a cl, E0.sto a = some cl → E0.pfr a = none → cl.owner = some E0.tid)
    (hpv : ∀ u ∈ thP.promises, ∀ m, cP.mem[u]? = some m → m.view < cP.mem.size)
    {Z : AllocLabel → Prop}
    (hZp : ∀ c1 th1 c1' c3 th3 l cl, TermOwnG0Defs.SoloNP p k arch i l (promise cP i a0 vB w) c1 → c1.ths[i]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c3 →
      Certified p k arch c3 i → c3.ths[i]? = some th3 → E0.sto l = some cl → cl.owner = some E0.tid →
      ¬ BufInitOn th3 l)
    (hres : ∀ c2 th2 E2, Solo p k arch i (promise cP i a0 vB w) c2 → Certified p k arch c2 i →
      c2.ths[i]? = some th2 → Ext E0 E2 → MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) →
      FrBound E0 (cP.mem.size + 1) thP.vs.vWr E2 →
      HoldB E0 (plantF E0 (promSt (stOf cP.mem cP.pairs thP) a0 vB w)) E2 (stOf c2.mem c2.pairs th2) →
      IniLoc Z E0 E2 → IniHeld (WitP cP.mem thP.promises) E0 E2 th2.vs.vWr →
      TermK5Defs.PfrProvE p k arch i (WitP cP.mem thP.promises) E0 (promise cP i a0 vB w) c2 E2 →
      TermK5O.PfrProvO p k arch i (WitP cP.mem thP.promises) E0 (promise cP i a0 vB w) c2 E2 →
      RunAgree E0 (plantE E0 (stOf cP.mem cP.pairs thP) Lp) Lp E2)
    {l : AllocLabel} {c : Cell} (hl : Lp l) (hc : E0.sto l = some c) {b : Nat} {S : Ty} {us : List Acc}
    (hseg : SegOf c.ty b S) (hus : accs S = some us) (h1 : nWords us = 1)
    (hnS : Ty.noOwnIn [] S = true) (hrS : rgnFree S = true)
    (hini : IniSeg (plantE E0 (stOf cP.mem cP.pairs thP) Lp) c l b) (hnot : ¬ IniSeg E0 c l b)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i (promise cP i a0 vB w) c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h) :
    ∃ ws, ValOf (plantE E0 (stOf cP.mem cP.pairs thP) Lp) S ws ∧ ws.length = nWords us := by
  rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us', j, hT, hus', hjN, rfl⟩
  · exact absurd (fun N e hT => by rw [hT] at hA; simp [accs] at hA) hnot
  rw [hus] at hus'
  cases hus'
  rw [h1]
  simp only [h1, Nat.mul_one] at hini hnot
  -- the slot is in the maximal held prefix, above the start count
  have hge : E0.ini l ≤ j := Nat.le_of_not_lt fun hlt =>
    hnot fun N' e' hT' => by
      rw [hT] at hT'
      simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
      obtain ⟨-, rfl⟩ := hT'
      exact ⟨us, j, hus, hlt, by rw [h1, Nat.mul_one]⟩
  have hjI : j < max (E0.ini l) (Np E0 (stOf cP.mem cP.pairs thP) l) := by
    obtain ⟨us2, j2, hus2, hj2, e⟩ := hini N S hT
    rw [hus] at hus2; cases hus2
    rw [h1, Nat.mul_one] at e; subst e
    rw [plantE_ini_in hl, NpZ_eq_of_pos hc hT hus (by rw [h1]; decide)] at hj2; exact hj2
  have hjN : j < Np E0 (stOf cP.mem cP.pairs thP) l := by
    rcases Nat.le_total (E0.ini l) (Np E0 (stOf cP.mem cP.pairs thP) l) with h | h
    · rw [Nat.max_eq_right h] at hjI; exact hjI
    · rw [Nat.max_eq_left h] at hjI; omega
  rcases PrefixHeld_Np hc N S us hT hus j (by rw [h1, Nat.mul_one]; exact hjN) with hI | ⟨u, hu, m, hm, hloc⟩
  · have := hI N S us hT hus; rw [h1, Nat.mul_one] at this; omega
  have hu' : u ∈ thP.promises := hu
  have hm' : cP.mem[u]? = some m := hm
  have hcl : E0.sto m.loc.label = some c := by rw [hloc]; exact hc
  obtain ⟨c2, th2, E2, h2, hc2, hth2, hx2, hm2, hw2, hfb2, hB2, hIL2, hIH2, hPV2, hPO2⟩ :=
    certified_holderWordHP (hrc0 := hrc0) (hfl0 := hfl0) hP hsc hvI hwin hthP hT0 hm0 hSC hbo hrl0 hsolo hc' hu' hm' hcl hZp hPS hSub hSig hZr
  rw [hT] at hw2
  obtain ⟨w0, hV, hle⟩ := wordOK_slot1 hw2 hus h1
  have hR := hres c2 th2 E2 h2 hc2 hth2 hx2 hm2 hfb2 hB2 hIL2 hIH2 hPV2 hPO2
  have hbi := hm2.2.2.2.2.2.2.2.2.2.1
  refine ⟨[w0], ValOf_monoK (G := PlantG E0 Lp) hnS hrS hus (by rw [h1]; rfl) hx2.2.2.1 hx2.2.2.2.1
    (fun a c0 hG hc0 => ?_) (fun a hG => ?_) (fun a f hG hf => ?_) (fun a B hG hB => ?_) hR.pay ?_ hV, rfl⟩
  · show E0.sto a = some c0
    rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B, hB⟩
    · rw [hx2.2.2.2.2.1 a c1 h1'] at hc0; rw [h1', hc0]
    · obtain ⟨c1, h1', -⟩ := hL a hLa
      rw [hx2.2.2.2.2.1 a c1 h1'] at hc0; rw [h1', hc0]
    · have := (hbi.2.2 a B (hx2.2.2.2.2.2.2.2.2.1 a B hB)).1
      rw [hc0] at this; cases this
  · rcases hG with hG | hLa | ⟨B, hB⟩
    · exact hR.ini a (.inl hG)
    · exact hR.ini a (.inr hLa)
    · rw [(hbi.2.2 a B (hx2.2.2.2.2.2.2.2.2.1 a B hB)).2.1]; exact Nat.zero_le _
  · rcases hG with ⟨c1, f0, h1', hf0⟩ | hLa | hB
    · have hnL : ¬ Lp a := fun hLa => by rw [hnone a hLa] at hf0; cases hf0
      rw [hx2.2.2.2.2.2.2.1 a f0 hf0] at hf
      cases hf
      exact ⟨_, by rw [plantE_pfr_ne hnL]; exact hf0, Nat.le_refl _⟩
    · exact hR.pfr a f (.inl hLa) hf
    · exact hR.pfr a f (.inr hB) hf
  · show E0.box a = some B
    rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B0, hB0⟩
    · have := (hbi.2.2 a B hB).1
      rw [hx2.2.2.2.2.1 a c1 h1'] at this; cases this
    · obtain ⟨c1, h1', -⟩ := hL a hLa
      have := (hbi.2.2 a B hB).1
      rw [hx2.2.2.2.2.1 a c1 h1'] at this; cases this
    · rw [hx2.2.2.2.2.2.2.2.2.1 a B0 hB0] at hB; rw [hB0, hB]
  · -- the slot word's reference names a start label
    intro w1 hw1 a g hv
    rw [List.mem_singleton] at hw1
    subst hw1
    have hJ := noJunk_valOf hV hnS hrS hus (by rw [h1]; rfl) w1 (List.mem_singleton_self _) a g hv
    have hvm : w1.view ≤ m.view := hle.2 a g hv
    have hmv : m.val = .loc a g := by rw [← hv]; exact hle.1.symm
    rcases FrBound_inspM hfb2 hJ (Nat.lt_of_le_of_lt hvm (hpv u hu' m hm')) with ⟨c1, hc1⟩ | ⟨B, hB⟩
    · rcases hpf : E0.pfr a.label with _ | f
      · exact .inr (.inl (hLcl l hl u hu' m hm' (by rw [hloc]) a g hmv c1 hc1 (hfp _ c1 hc1 hpf) hpf))
      · exact .inl ⟨c1, f, hc1, hpf⟩
    · exact .inr (.inr ⟨B, hB⟩)

/-- `RunAgree` without its planted-label frontier part, which the
holder bound gives (`runAgree_pfrL`): the counts (`ini`), the frontiers at the
start's boxes (`pfrB`), and the box payloads (`pay`). -/
structure RunAgreeW (E0 E' : TEnv) (Lp : AllocLabel → Prop) (E2 : TEnv) : Prop where
  ini : ∀ a, ((∃ c f, E0.sto a = some c ∧ E0.pfr a = some f) ∨ Lp a) → E2.ini a ≤ E'.ini a
  pfrB : ∀ a f, (∃ B, E0.box a = some B) → E2.pfr a = some f → ∃ f', E'.pfr a = some f' ∧ f' ≤ f
  pay : ∀ a B, PlantG E0 Lp a → E2.box a = some B → ∀ w ∈ B.pay, ∀ (a' : Address) (g : Nat),
    w.val = .loc a' g → InspM E2 a'.label w.view → PlantG E0 Lp a'.label

theorem RunAgree_ofW {E0 E' : TEnv} {Lp : AllocLabel → Prop} {E2 : TEnv} (h : RunAgreeW E0 E' Lp E2)
    (hp : ∀ a f, Lp a → E2.pfr a = some f → ∃ f', E'.pfr a = some f' ∧ f' ≤ f) : RunAgree E0 E' Lp E2 :=
  ⟨h.ini, fun a f h1 hf => h1.elim (fun hL => hp a f hL hf) (fun hB => h.pfrB a f hB hf), h.pay⟩

/-- **`RunAgree.pfr` at planted labels, from the holder bound**: a
frontier `f` set during the certificate run at a planted label is at least the
planted one, `plantF` at the promiser's pre-promise state `s0` (which the
promise step only raises, `plantF_mono`). -/
theorem runAgree_pfrL {E0 E2 : TEnv} {s0 s2 : St} {Lp : AllocLabel → Prop} {a0 : Address}
    {vB : WeakMem.Val} {w : Ts} (hB : HoldB E0 (plantF E0 (promSt s0 a0 vB w)) E2 s2)
    (hlt : ∀ t ∈ s0.promises, t < s0.mem.size) (hsto : ∀ l c, E0.sto l = some c → E2.sto l = some c)
    (hL : ∀ l, Lp l → ∃ c, E0.sto l = some c) (hn : ∀ l, Lp l → E0.pfr l = none) :
    ∀ a f, Lp a → E2.pfr a = some f → ∃ f', (plantE E0 s0 Lp).pfr a = some f' ∧ f' ≤ f := by
  intro a f ha hf
  obtain ⟨c, hc⟩ := hL a ha
  refine ⟨_, plantE_pfr_in ha, ?_⟩
  have h1 := hB.2.2 a c f (hn a ha) (hsto a c hc) hf
  have h0 : plantF E0 s0 a ≤ plantF E0 (promSt s0 a0 vB w) a :=
    plantF_mono (Nat.le_refl _) (fun t ht hn' => absurd (List.mem_append_left _ ht) hn') hlt
      (TermCert.MemExt.push _ _)
      (fun u hu => by
        rcases List.mem_append.1 hu with h | h
        · exact .inl h
        · rw [List.mem_singleton] at h; exact .inr (Nat.le_of_eq h.symm))
      (fun _ _ _ _ _ hni hi => absurd hi hni)
  exact Nat.le_trans h0 h1

end TermIni

#print axioms TermIni.plantT_le
#print axioms TermIni.plantF_mono
#print axioms TermIni.holder_iniW
#print axioms TermIni.HoldB_start
#print axioms TermIni.HoldB_foot
#print axioms TermIni.HoldB_prom
#print axioms TermIni.HoldB_promSt
#print axioms TermIni.InvAtXH_promOf
#print axioms TermIni.solo_typedXH
#print axioms TermIni.certified_promTypedXH
#print axioms TermIni.certified_promNotUndefXH
#print axioms TermIni.certified_holderWordH
#print axioms TermIni.certified_hinhW1H
#print axioms TermIni.InvAtXHP.toH
#print axioms TermIni.InvAtXHP_promOf
#print axioms TermIni.solo_typedXHP
#print axioms TermIni.certified_promTypedXHP
#print axioms TermIni.certified_promNotUndefXHP
#print axioms TermIni.certified_holderWordHP
#print axioms TermIni.certified_hinhW1HP
#print axioms TermIni.RunAgree_ofW
#print axioms TermIni.runAgree_pfrL
