import WeakCore.TermBox
/-! # TermBoxT — (E2) a thread's `ThSys` survives the ghost box `EgB Eg l` (per-thread transfer). -/
namespace TermBox
open CoreLang CoreTerm TermRun TermSound TermMem TermStep TermCut TermSys TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section boxEnv
variable {E : TEnv} {l : AllocLabel}

theorem boxE_sto_self : (boxE E l).sto l = some ⟨.unit, none⟩ := by simp [boxE]
theorem boxE_pfr_self : (boxE E l).pfr l = some 0 := by simp [boxE]
theorem boxE_sto_ne {x : AllocLabel} (h : x ≠ l) : (boxE E l).sto x = E.sto x := by simp [boxE, h]
theorem boxE_pfr_ne {x : AllocLabel} (h : x ≠ l) : (boxE E l).pfr x = E.pfr x := by simp [boxE, h]
theorem boxE_rc (x : AllocLabel) : (boxE E l).rc x = E.rc x := rfl

/-- The box's label is no own cell's. -/
theorem boxE_own_ne {x : AllocLabel} {c : Cell} (hc : (boxE E l).sto x = some c) (ho : c.owner = some (boxE E l).tid) :
    x ≠ l := by
  rintro rfl; rw [boxE_sto_self] at hc; cases hc; cases ho

theorem boxE_sto_ne_of {x : AllocLabel} {c : Cell} (hs : E.sto l = none) (hc : E.sto x = some c) : x ≠ l := by
  rintro rfl; rw [hs] at hc; cases hc

theorem incl_boxE (hs : E.sto l = none) (hp : E.pfr l = none) : Incl E (boxE E l) where
  prog := rfl
  sto := fun x c h => by rw [boxE_sto_ne (boxE_sto_ne_of hs h)]; exact h
  ini := fun _ => Nat.le_refl _
  pfr := fun x f h => by
    have e : x ≠ l := by rintro rfl; rw [hp] at h; cases h
    rw [boxE_pfr_ne e]; exact h
  box := fun _ _ h => h
  rini := fun _ => Nat.le_refl _

theorem wordOK_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {T : Ty} {o : Nat} {w : Word}
    (h : WordOK E T o w) : WordOK (boxE E l) T o w :=
  WordOK_mono (η₁ := E) (η₂ := boxE E l) rfl rfl (incl_boxE hs hp).sto (fun _ => Nat.le_refl _) (incl_boxE hs hp).pfr (fun _ h => h) h

theorem pairOK_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {T : Ty} {o : Nat} {w0 w1 : Word}
    (h : PairOK E T o w0 w1) : PairOK (boxE E l) T o w0 w1 :=
  PairOK_mono (η₁ := E) (η₂ := boxE E l) rfl rfl (incl_boxE hs hp).sto (fun _ => Nat.le_refl _) (incl_boxE hs hp).pfr (fun _ h => h) h

theorem valOf_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {T : Ty} {ws : List Word}
    (h : ValOf E T ws) : ValOf (boxE E l) T ws :=
  ValOf_mono (η₁ := E) (η₂ := boxE E l) rfl rfl (incl_boxE hs hp).sto (fun _ => Nat.le_refl _) h (incl_boxE hs hp).pfr (fun _ h => h)

theorem hiddenP_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {T : Ty} {mem : Memory} {P : List Ts}
    {x : AllocLabel} {o : Nat} {V : Ts} (h : HiddenP E T mem P x o V) : HiddenP (boxE E l) T mem P x o V :=
  HiddenP_move (fun _ _ => rfl) (fun _ _ h1 h2 => absurd (lt_of_get h2) (Nat.not_lt.2 h1))
    (fun _ h => wordOK_boxE hs hp h) h

/-- Nothing in memory at the box label: every `HiddenP` there holds. -/
theorem hiddenP_nomsg {E' : TEnv} {T : Ty} {mem : Memory} {P : List Ts} {o : Nat} {V : Ts}
    (hm : ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc.label ≠ l) : HiddenP E' T mem P l o V :=
  fun t m _ h1 h2 _ => absurd (by rw [h2]) (hm t m h1)

end boxEnv

section clauses
variable {E : TEnv} {l : AllocLabel} {mem : Memory}

/-- Clause 1. -/
theorem memOKP_boxE (hs : E.sto l = none) (hp : E.pfr l = none)
    (hm : ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc.label ≠ l) {pairs P : List Ts}
    (h : MemOKP E mem pairs P) : MemOKP (boxE E l) mem pairs P := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t m c ht hmt hc => ?_, fun t m0 m1 c ht h0 h1' hc => ?_, h3⟩
  · rw [boxE_sto_ne (hm t m hmt)] at hc
    exact (h1 t m c ht hmt hc).imp id (wordOK_boxE hs hp)
  · rw [boxE_sto_ne (hm t m0 h0)] at hc
    exact pairOK_boxE hs hp (h2 t m0 m1 c ht h0 h1' hc)

/-- Clause 2. -/
theorem ownOKSF_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {pairs : List Ts} {vs : VState}
    {S : Ts → Prop} (h : OwnOKSF E mem pairs vs S) : OwnOKSF (boxE E l) mem pairs vs S := by
  intro x c hc ho
  have e := boxE_own_ne hc ho
  rw [boxE_sto_ne e] at hc
  obtain ⟨vals, h1, h2, h3⟩ := h x c hc ho
  refine ⟨vals, CellOK_mono (η₁ := E) (η₂ := boxE E l) rfl rfl (incl_boxE hs hp) (fun _ h => h) h1, fun o v hv => ?_, fun hn => ?_⟩
  · rw [boxE_pfr_ne e]; exact LatestSF_map (fun _ _ _ h => wordOK_boxE hs hp h) (h2 o v hv)
  · rw [boxE_pfr_ne e] at hn
    exact fun o hT hI => OwnPairAt_map (fun _ _ _ _ h => pairOK_boxE hs hp h) (h3 hn o hT hI)

/-- Clause 4b. -/
theorem privCoh_boxE {s : St} (h : PrivCoh E s) : PrivCoh (boxE E l) s := by
  intro t m ht hmt ⟨c, N, e, us, h1, h2, h3, h4, h5, h6, h7⟩
  have ne := boxE_own_ne h1 h2
  rw [boxE_sto_ne ne] at h1; rw [boxE_pfr_ne ne] at h3
  exact h t m ht hmt ⟨c, N, e, us, h1, h2, h3, h4, h5, h6, h7⟩

/-- Clause 4. -/
theorem freshLP_boxE {g : G} {s s' : St} (h : FreshLP g E s) (hna : s.nalloc ≤ s'.nalloc)
    (hnf : ∀ q, s'.nalloc ≤ q → freshLabel g.lbase g.n g.i q ≠ l)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (e3 : s'.vs = s.vs) :
    FreshLP g (boxE E l) s' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j hj => ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h1 j (Nat.le_trans hna hj)
    have ne := hnf j hj
    refine ⟨by rw [boxE_sto_ne ne]; exact a1, fun t m hm hl => ?_, a3, by rw [boxE_pfr_ne ne]; exact a4⟩
    rw [e1] at hm; rw [e2]; exact a2 t m hm hl
  · intro t m ht hmt hu
    rw [e1] at hmt; rw [e2] at ht; rw [e3]
    exact privCoh_boxE h2 t m ht hmt hu

/-- Clause 5: and the box is unseen. -/
theorem seenLE_boxE (hp : E.pfr l = none) {V : Ts} (h : SeenLE E V) : SeenLE (boxE E l) V := by
  intro x hx
  have ne : x ≠ l := by rintro rfl; obtain ⟨f, hf, -⟩ := h _ hx; rw [hp] at hf; cases hf
  rw [boxE_pfr_ne ne]; exact h x hx

theorem not_seen_of (hp : E.pfr l = none) {V : Ts} (h : SeenLE E V) : ¬ E.seen l := by
  intro hx; obtain ⟨f, hf, -⟩ := h _ hx; rw [hp] at hf; cases hf

/-- Clause 6. -/
theorem ownHidP_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {vs : VState} {P : List Ts}
    (h : OwnHidP E mem vs P) : OwnHidP (boxE E l) mem vs P := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x c hc ho o hI => ?_, fun x c hc ho hlt => ?_⟩
  · have ne := boxE_own_ne hc ho
    rw [boxE_sto_ne ne] at hc
    exact hiddenP_boxE hs hp (h1 x c hc ho o hI)
  · have ne := boxE_own_ne hc ho
    rw [boxE_sto_ne ne] at hc
    obtain ⟨f, hf, hz, hh⟩ := h2 x c hc ho hlt
    refine ⟨f, by rw [boxE_pfr_ne ne]; exact hf, fun hz' => hz fun hw => hz' ((ZW.stoAt (boxE_sto_ne ne)).2 hw),
      fun o hI => hiddenP_boxE hs hp (hh o hI)⟩

/-- Clause 7. -/
theorem pubDefP_boxE (hs : E.sto l = none) (hp : E.pfr l = none)
    (hm : ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc.label ≠ l) {P : List Ts}
    (h : PubDefP E mem P) : PubDefP (boxE E l) mem P := by
  intro x c f hc ho hf o hI
  by_cases ne : x = l
  · subst ne; exact hiddenP_nomsg hm
  · rw [boxE_sto_ne ne] at hc; rw [boxE_pfr_ne ne] at hf
    exact hiddenP_boxE hs hp (h x c f hc ho hf o hI)

/-- Clause 8. -/
theorem ownPubV_boxE {s s' : St} (h : OwnPubV E s) (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises)
    (e3 : s'.vs = s.vs) : OwnPubV (boxE E l) s' := by
  intro x c f hc ho hf
  have ne := boxE_own_ne hc ho
  rw [boxE_sto_ne ne] at hc; rw [boxE_pfr_ne ne] at hf
  rcases h x c f hc ho hf with a | a | ⟨t, ht, m, hm, hl, hft, hmin, hni⟩
  · exact Or.inl a
  · exact Or.inr (Or.inl (by rw [e3]; exact a))
  · refine Or.inr (Or.inr ⟨t, by rw [e2]; exact ht, m, by rw [e1]; exact hm, hl, hft, fun u hu m' hm' => ?_, ?_⟩)
    · rw [e2] at hu; rw [e1] at hm'; exact hmin u hu m' hm'
    · intro hw; apply hni
      exact (IniWr_congr (E := E) (E' := boxE E l) (by rw [hl]; exact boxE_sto_ne ne) rfl).1 hw

end clauses

section pubInv
variable {E : TEnv} {l : AllocLabel} {mem : Memory}

theorem segOf_unit {b : Nat} {S : Ty} (h : SegOf .unit b S) : S = .unit := by
  rcases h with ⟨-, e, -⟩ | ⟨N, us, j, e, -⟩
  · exact e
  · cases e

theorem accs_unit {us : List Acc} (h : accs .unit = some us) : us = [] := by
  have e : accs .unit = some [] := rfl
  rw [e] at h; cases h; rfl

/-- Clause 9a. -/
theorem seenOwn_boxE (hse : ¬ E.seen l) (h : SeenOwn E) : SeenOwn (boxE E l) := by
  intro x hx
  have ne : x ≠ l := by rintro rfl; exact hse hx
  rw [boxE_sto_ne ne]; exact h x hx

/-- Clause 9b. -/
theorem inh_boxE (hs : E.sto l = none) (hp : E.pfr l = none) (h : Inh E) : Inh (boxE E l) := by
  intro x c b S us hc hS hu hI
  by_cases ne : x = l
  · subst ne; rw [boxE_sto_self] at hc; cases hc
    have e1 := segOf_unit hS; subst e1
    have e2 := accs_unit hu; subst e2
    exact ⟨[], by unfold ValOf; simp [VR, Valid], rfl⟩
  · rw [boxE_sto_ne ne] at hc
    obtain ⟨ws, h1, h2⟩ := h x c b S us hc hS hu hI
    exact ⟨ws, valOf_boxE hs hp h1, h2⟩

/-- Clause 9c. -/
theorem pubCpl_boxE (h : PubCpl E) : PubCpl (boxE E l) := by
  intro x c f hc hf
  by_cases ne : x = l
  · subst ne; rw [boxE_sto_self] at hc; cases hc
    refine ⟨Or.inl (by rw [show accs .unit = some [] from rfl]; simp), fun b S hS _ => ?_, rfl, rfl, rfl⟩
    rw [segOf_unit hS]; exact TearOK_of_cpl rfl
  · rw [boxE_sto_ne ne] at hc; rw [boxE_pfr_ne ne] at hf
    exact h x c f hc hf

/-- Clause 9d. -/
theorem pubPair_boxE (hs : E.sto l = none) (hp : E.pfr l = none)
    (hm : ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc.label ≠ l) {pairs P : List Ts}
    (h : PubPair E mem pairs P) : PubPair (boxE E l) mem pairs P := by
  intro x c f o hc hg hf hT t0 t1 m0 m1 n0 n1 h0 h1 l0 l1 hd0 hd1 hst
  by_cases ne : x = l
  · subst ne; exact absurd (by rw [l0]) (hm t0 m0 h0)
  · rw [boxE_sto_ne ne] at hc; rw [boxE_pfr_ne ne] at hf
    exact pairOK_boxE hs hp (h x c f o hc hg hf hT t0 t1 m0 m1 n0 n1 h0 h1 l0 l1 hd0 hd1 hst)

/-- Clause 9e. -/
theorem pubLive_boxE (h : PubLive E mem) : PubLive (boxE E l) mem := by
  intro x c f b S us o hc ho hf hS hu hlt
  by_cases ne : x = l
  · subst ne; rw [boxE_sto_self] at hc; cases hc
    rw [segOf_unit hS] at hu; rw [accs_unit hu] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  · rw [boxE_sto_ne ne] at hc; rw [boxE_pfr_ne ne] at hf
    exact h x c f b S us o hc ho hf hS hu hlt

theorem pubMem_boxE (hs : E.sto l = none) (hp : E.pfr l = none)
    (hm : ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc.label ≠ l) {pairs P : List Ts}
    (h : PubMem E mem pairs P) : PubMem (boxE E l) mem pairs P :=
  ⟨pubPair_boxE hs hp hm h.1, pubLive_boxE h.2⟩

/-- Clause 9. -/
theorem pubInv_boxE (hs : E.sto l = none) (hp : E.pfr l = none) (hse : ¬ E.seen l) {s s' : St}
    (hm : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label ≠ l) (h : PubInv E s)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (e4 : s'.pairs = s.pairs) : PubInv (boxE E l) s' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨seenOwn_boxE hse h1, inh_boxE hs hp h2, pubCpl_boxE h3, ?_⟩
  rw [e1, e2, e4]; exact pubMem_boxE hs hp hm h4

/-- Clause 10. -/
theorem boxInv_boxE (hb : E.box l = none) {g : G} {s s' : St} (h : BoxInv g E s) (hna : s.nalloc ≤ s'.nalloc)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (e3 : s'.vs = s.vs) : BoxInv g (boxE E l) s' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j hj => h1 j (Nat.le_trans hna hj), by rw [e1, e2]; exact h2, fun x B hx => ?_⟩
  have hx' : E.box x = some B := hx
  have ne : x ≠ l := by rintro rfl; rw [hb] at hx'; cases hx'
  obtain ⟨a1, a2, a3⟩ := h3 x B hx'
  refine ⟨by rw [boxE_sto_ne ne]; exact a1, a2, ?_⟩
  rw [e1, e2, e3]; exact a3

end pubInv

section held
variable {E : TEnv} {l : AllocLabel}

/-- The `TEnv`-level `MemInv` transfer (only `nalloc` may grow in the state). -/
theorem memInv_boxE (hs : E.sto l = none) (hp : E.pfr l = none) (hb : E.box l = none) {g : G} {s s' : St}
    (hm : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label ≠ l) (h : MemInv g E s)
    (hna : s.nalloc ≤ s'.nalloc) (hnf : ∀ q, s'.nalloc ≤ q → freshLabel g.lbase g.n g.i q ≠ l)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (e3 : s'.vs = s.vs) (e4 : s'.pairs = s.pairs) :
    MemInv g (boxE E l) s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have hse := not_seen_of hp h5
  refine ⟨?_, ?_, ?_, freshLP_boxE h4 hna hnf e1 e2 e3, ?_, ?_, ?_, ownPubV_boxE h8 e1 e2 e3,
    pubInv_boxE hs hp hse hm h9 e1 e2 e4, boxInv_boxE hb h10 hna e1 e2 e3, ?_⟩
  · rw [e1, e4, e2]; exact memOKP_boxE hs hp hm h1
  · show OwnOKSF _ _ _ _ _; rw [e1, e4, e2, e3]; exact ownOKSF_boxE hs hp h2
  · intro t ht; rw [e2] at ht; rw [e1]; exact h3 t ht
  · rw [e3]; exact seenLE_boxE hp h5
  · rw [e1, e3, e2]; exact ownHidP_boxE hs hp h6
  · rw [e1, e2]; exact pubDefP_boxE hs hp hm h7
  · unfold PromOK at h11 ⊢; rw [e2, e4]; exact h11

theorem heldEntry_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {s s' : St} {x : AllocLabel} {R : Res}
    (ne : x ≠ l) (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (h : HeldEntry E s x R) :
    HeldEntry (boxE E l) s' x R := by
  refine ⟨fun h0 => h.1 (by rw [boxE_sto_ne ne] at h0; exact h0), fun c hc => ?_⟩
  rw [boxE_sto_ne ne] at hc
  obtain ⟨vals, hv, hk⟩ := h.2 c hc
  refine ⟨vals, fun o w hw => ?_, CellOKR_mono (η₁ := E) (η₂ := boxE E l) rfl rfl (incl_boxE hs hp) hk⟩
  rw [PromAt_congr (E := E) (E' := boxE E l) (a := ⟨x, o⟩) (boxE_sto_ne ne) rfl (boxE_pfr_ne ne),
    PromAt_eqp e2 e1, e1]
  exact hv o w hw

theorem priv_boxE_iff (hs : E.sto l = none) (x : AllocLabel) : Priv (boxE E l) x ↔ Priv E x := by
  by_cases ne : x = l
  · subst ne
    refine ⟨fun ⟨⟨c, hc, ho⟩, _⟩ => ?_, fun ⟨⟨c, hc, _⟩, _⟩ => by rw [hs] at hc; cases hc⟩
    rw [boxE_sto_self] at hc; cases hc; cases ho
  · unfold Priv OwnL; rw [boxE_sto_ne ne, boxE_pfr_ne ne]; rfl

theorem memHeldP_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {s s' : St} {H : Res}
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (h : MemHeldP E s H) : MemHeldP (boxE E l) s' H :=
  MemHeldP_move (priv_boxE_iff hs)
    (fun _ ⟨⟨_, hc, _⟩, _⟩ => boxE_sto_ne (boxE_sto_ne_of hs hc))
    (fun _ _ ⟨⟨_, hc, _⟩, _⟩ he => heldEntry_boxE hs hp (boxE_sto_ne_of hs hc) e1 e2 he) h

theorem memHeldS_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {s s' : St} {H : Res}
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (h : MemHeldS E s H) : MemHeldS (boxE E l) s' H := by
  classical
  obtain ⟨L, Rl, hnd, hc, hq, rfl, he⟩ := h
  have hlL : l ∉ L := fun hl => by obtain ⟨f, hf⟩ := hq l hl; rw [hp] at hf; cases hf
  have hneL : ∀ x, x ∈ L → x ≠ l := fun x hx e => hlL (e ▸ hx)
  refine ⟨l :: L, fun x => if x = l then .zero else Rl x, List.nodup_cons.2 ⟨hlL, hnd⟩, fun x c hx hsx => ?_,
    fun x hx => ?_, ?_, fun x hx => ?_⟩
  · by_cases ne : x = l
    · exact ne ▸ List.mem_cons_self
    · have hx' : ∃ f, (boxE E l).pfr x = some f := hx
      rw [boxE_pfr_ne ne] at hx'; rw [boxE_sto_ne ne] at hsx
      exact List.mem_cons_of_mem _ (hc x c hx' hsx)
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨0, boxE_pfr_self⟩
    · rw [boxE_pfr_ne (hneL x hx)]; exact hq x hx
  · simp only [List.map_cons, Res.sum_cons, ite_true, Res.zero_add]
    congr 1
    exact (List.map_congr_left fun x hx => by simp only [hneL x hx, ite_false]).symm
  · rcases List.mem_cons.1 hx with rfl | hx
    · show HeldEntry _ _ _ (if x = x then _ else _)
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      refine ⟨fun h0 => (by rw [boxE_sto_self] at h0), fun c hc => ?_⟩
      rw [boxE_sto_self] at hc; cases hc
      exact ⟨[], ⟨fun o w hw => by simp at hw, Or.inl ⟨rfl, by unfold ValOfR; simp [VRR, Valid]⟩⟩⟩
    · show HeldEntry _ _ _ (if x = l then _ else _)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (hneL x hx))]
      exact heldEntry_boxE hs hp (hneL x hx) e1 e2 (he x hx)

end held

section cred
variable {E : TEnv} {l : AllocLabel}

theorem promCrK_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {s s' : St} {cr db : Ts → Res}
    (hm : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label ≠ l) (hpl : PromLt s)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises)
    (h : TermPlant.PromCrK E s cr db) : TermPlant.PromCrK (boxE E l) s' cr db := by
  intro tw htw
  rw [e2] at htw
  obtain ⟨m, hmt, hd, hc⟩ := h tw htw
  have ne := hm tw m hmt
  have hS : (boxE E l).sto m.loc.label = E.sto m.loc.label := boxE_sto_ne ne
  have hP : (boxE E l).pfr m.loc.label = E.pfr m.loc.label := boxE_pfr_ne ne
  refine ⟨m, by rw [e1]; exact hmt, ?_, ?_⟩
  · rw [e1]
    exact TermPlant.DbRes_congrD hS rfl hP rfl (fun _ _ h => h)
      (by unfold DesigAt PredU; rw [hP, IniW_congrU hS rfl, IniWr_congr hS rfl, DStart_congr hS rfl]) hd
  · rcases hc with (⟨w, hw, hv⟩ | ⟨hn, hz⟩) | ⟨hpc, hk⟩
    · exact Or.inl (Or.inl ⟨w, by rw [e1]; exact hw, VRes_move hS rfl hP (Or.inl rfl) hv⟩)
    · exact Or.inl (Or.inr ⟨fun w hw => hn w (by rw [e1] at hw; exact hw), hz⟩)
    · refine Or.inr ⟨TermPlant.PlantCr_mono (fun t _ => by rw [e1]) (by rw [e1]; exact Nat.le_refl _) e2 hpl hS rfl
        (fun h' => by rw [hP]; exact h') (fun h' => (WordUnit_congr hS).1 h')
        (fun t _ ht => by rw [FpAt_congr (E := E) (E' := boxE E l) (a := ⟨m.loc.label, 0⟩) hS rfl hP rfl] at ht; exact ht)
        (fun _ _ _ h' => ValOfR_mono (η₁ := E) (η₂ := boxE E l) rfl rfl (incl_boxE hs hp).sto
          (fun _ => Nat.le_refl _) h' (incl_boxE hs hp).pfr) hpc, hk⟩

end cred

theorem thSys_box {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {T HP HS : Res} {cr db : Ts → Res} {l : AllocLabel} {n' : Nat} {tl : Option AllocLabel}
    (hf : BoxFresh Eg mem l) (hT : ThSys p g mem pairs th Eg T HP HS cr db)
    (hn : th.nalloc ≤ n') (hfr : ∀ q, th.nalloc ≤ q → q < n' → freshLabel g.lbase g.n g.i q = l)
    (hnf : ∀ q, n' ≤ q → freshLabel g.lbase g.n g.i q ≠ l) :
    ThSys p g mem pairs { th with nalloc := n', tidLbl := tl } (EgB Eg l) T HP HS cr db := by
  obtain ⟨S, h1, h2, h3, h4, h5, h6⟩ := hT
  have hs : (Cut Eg g.i S).sto l = none := cutSto_fresh hf
  have hp : (Cut Eg g.i S).pfr l = none := hf.pfr
  have hb : (Cut Eg g.i S).box l = none := hf.box
  have hm : ∀ (t : Nat) (m : Msg), (stOf mem pairs th).mem[t]? = some m → m.loc.label ≠ l := hf.msg
  refine ⟨S, thInvRE_box hf h1, thInvE_box hf h2, ?_, ?_, ?_, ?_⟩
  · rw [cut_EgB]; exact memInv_boxE hs hp hb hm h3 hn hnf rfl rfl rfl rfl
  · rw [cut_EgB]; exact memHeldP_boxE hs hp rfl rfl h4
  · rw [cut_EgB]; exact memHeldS_boxE hs hp rfl rfl h5
  · rw [cut_EgB]; exact promCrK_boxE hs hp hm h3.2.2.1 rfl rfl h6

end TermBox

#print axioms TermBox.thSys_box

/-! (hygiene) axiom reports. -/
#print axioms TermBox.boxE_sto_self
#print axioms TermBox.boxE_pfr_self
#print axioms TermBox.boxE_sto_ne
#print axioms TermBox.boxE_pfr_ne
#print axioms TermBox.boxE_rc
#print axioms TermBox.boxE_own_ne
#print axioms TermBox.boxE_sto_ne_of
#print axioms TermBox.incl_boxE
#print axioms TermBox.wordOK_boxE
#print axioms TermBox.pairOK_boxE
#print axioms TermBox.valOf_boxE
#print axioms TermBox.hiddenP_boxE
#print axioms TermBox.hiddenP_nomsg
#print axioms TermBox.memOKP_boxE
#print axioms TermBox.ownOKSF_boxE
#print axioms TermBox.privCoh_boxE
#print axioms TermBox.freshLP_boxE
#print axioms TermBox.seenLE_boxE
#print axioms TermBox.not_seen_of
#print axioms TermBox.ownHidP_boxE
#print axioms TermBox.pubDefP_boxE
#print axioms TermBox.ownPubV_boxE
#print axioms TermBox.segOf_unit
#print axioms TermBox.accs_unit
#print axioms TermBox.seenOwn_boxE
#print axioms TermBox.inh_boxE
#print axioms TermBox.pubCpl_boxE
#print axioms TermBox.pubPair_boxE
#print axioms TermBox.pubLive_boxE
#print axioms TermBox.pubMem_boxE
#print axioms TermBox.pubInv_boxE
#print axioms TermBox.boxInv_boxE
#print axioms TermBox.memInv_boxE
#print axioms TermBox.heldEntry_boxE
#print axioms TermBox.priv_boxE_iff
#print axioms TermBox.memHeldP_boxE
#print axioms TermBox.memHeldS_boxE
#print axioms TermBox.promCrK_boxE
