import WeakCore.TermOwnCPin
import WeakCore.TermOverCrX

/-! # TermOwnCOld: the owner's cover at an old frontier cell across a KindC step (ownC)

`overCr_old`: the generic assembly.  The items whose holder survives are kept (piece-local frame,
`TermOwnCR5.crItemQ_frameP`); a fulfilled non-word promise of `l` discharges the lowest own
promises of its whole pieces (`hFP`, the `FulP`/WPD shape), so a dropped item covers nothing still
demanded; every post-demand is a pre-demand (step-specific) or carries a `freeQW` zero item.
-/

namespace TermOwnCOld

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Zero items in general (single- and two-word units) -/

/-- A **zero item** for the lowest own promise `tw` at a unit `o` of `l`: credited at any credits,
resource-free, held piece-lowest, its masked words carrying a lowest own promise, covering `o`. -/
def ZeroIt (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) (tw : Ts)
    (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)) : Prop :=
  ∃ o, TermPlant.LowOwn s ⟨l, o⟩ tw ∧ (∀ cr, TermOverCr.CrItemQ E s cr l c x) ∧ x.2.2.2.2.1 = .zero ∧
    TermOverCr.HolderLow s l [x] ∧
    (∀ usS i o2, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o2 →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o2⟩ t0) ∧
    ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true

/-- A `freeQW` item is a zero item. -/
theorem zeroIt_of_freeQW {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {tw : Ts}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (h : TermFreeQW.FreeQW E s l c tw x) :
    ZeroIt E s l c tw x := by
  obtain ⟨o, us, hlo, hus, hb, ho, hK, hz, hit, hH, hsing⟩ := h
  refine ⟨o, hlo, hit, hz, hH, fun usS i o2 h1 hk hio => ?_, ?_⟩
  · rw [hus] at h1
    cases h1
    rw [hK] at hk
    exact TermFreeQW.freeQW_wa hb hsing hlo i o2 hk hio
  · obtain ⟨i, hi, hk⟩ := TermFreeQW.freeQW_cover (us := us) hb ho
    exact ⟨us, i, hus, hb, hi, by rw [hK]; exact hk⟩

open Classical in
noncomputable def zeroIt (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) (tw : Ts) :
    Ts × Nat × Ty × List Word × Res × (Nat → Bool) :=
  if h : ∃ x, ZeroIt E s l c tw x then Classical.choose h else (tw, 0, .unit, [], .zero, fun _ => true)

open Classical in
/-- One zero item per own promise having one. -/
noncomputable def zeroWL (E : TEnv) (s : St) (l : AllocLabel) (c : Cell) :
    List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :=
  (s.promises.filter (fun tw => decide (∃ x, ZeroIt E s l c tw x))).map (zeroIt E s l c)

theorem zeroIt_spec {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {tw : Ts} (h : ∃ x, ZeroIt E s l c tw x) :
    ZeroIt E s l c tw (zeroIt E s l c tw) := by
  classical
  unfold zeroIt
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec h

theorem mem_zeroWL {E : TEnv} {s : St} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hx : x ∈ zeroWL E s l c) :
    ∃ tw, ZeroIt E s l c tw x := by
  classical
  unfold zeroWL at hx
  obtain ⟨tw, htw, rfl⟩ := List.mem_map.1 hx
  exact ⟨tw, zeroIt_spec (of_decide_eq_true (List.mem_filter.1 htw).2)⟩

theorem zeroWL_cover {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {o : Nat} {tw : Ts}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hx : ZeroIt E s l c tw x)
    (hl : TermPlant.LowOwn s ⟨l, o⟩ tw) :
    ∃ x ∈ zeroWL E s l c, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
      x.2.2.2.2.2 i = true := by
  classical
  have hex : ∃ x, ZeroIt E s l c tw x := ⟨x, hx⟩
  have hmem : zeroIt E s l c tw ∈ zeroWL E s l c :=
    List.mem_map.2 ⟨tw, List.mem_filter.2 ⟨hl.1, decide_eq_true hex⟩, rfl⟩
  obtain ⟨o', hlo', -, -, -, -, hcov⟩ := zeroIt_spec hex
  have eo : o' = o := by
    obtain ⟨m1, hm1, hl1⟩ := hl.2.1
    obtain ⟨m2, hm2, hl2⟩ := hlo'.2.1
    rw [hm1] at hm2
    cases hm2
    exact congrArg Address.offset (hl2.symm.trans hl1)
  subst eo
  exact ⟨_, hmem, hcov⟩

/-- **Kept items plus zero items give the cover.** -/
theorem overCr_keepZI {E : TEnv} {s : St} {f : Ts → Res} {l : AllocLabel} {c : Cell}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (Gk : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))
    (hit : ∀ x ∈ Gk, TermOverCr.CrItemQ E s f l c x) (hsum : ∀ t, TermOverCrW.sumH Gk t ≤ f t)
    (hwa : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hHL : TermOverCr.HolderLow s l Gk)
    (hcov : ∀ o tw, TermOverCr.CovU E c l o → ¬ VisU E ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw → TermPlant.OverT E s ⟨l, o⟩ tw →
      (∃ x ∈ Gk, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true) ∨ ∃ x, ZeroIt E s l c tw x)
    (hz : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      f t ≠ .zero → t ∈ Gk.map (·.1)) :
    TermOverCr.OverCrE E s f l c := by
  refine TermOwnCP.overCr_assemble hcpl hni (Gk ++ zeroWL E s l c) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hit x h
    · obtain ⟨tw, o, -, hi, -⟩ := mem_zeroWL h
      exact hi f
  · intro t
    rw [TermOverCrW.sumH_append, TermOverCrW.sumH_zero (L := zeroWL E s l c) (fun x hx => by
      obtain ⟨tw, o, -, -, hz0, -⟩ := mem_zeroWL hx
      exact hz0) t, Res.add_zero]
    exact hsum t
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hwa x h
    · obtain ⟨tw, o, -, -, -, -, hw, -⟩ := mem_zeroWL h
      exact hw
  · refine TermOverCr.holderLow_append hHL fun x hx => ?_
    obtain ⟨tw, o, -, -, -, hH, -⟩ := mem_zeroWL hx
    exact hH x (List.mem_singleton_self x)
  · intro o tw hc hv hlo hg hov
    rcases hcov o tw hc hv hlo hg hov with ⟨x, hx, r⟩ | ⟨x, hx⟩
    · exact ⟨x, List.mem_append_left _ hx, r⟩
    · obtain ⟨x', hx', r⟩ := zeroWL_cover hx hlo
      exact ⟨x', List.mem_append_right _ hx', r⟩
  · intro t m ht hm hl hw hnz
    rw [List.map_append]
    exact List.mem_append_left _ (hz t m ht hm hl hw hnz)

#print axioms overCr_keepZI

/-- Pointwise bound by `rpSum`. -/
theorem _root_.TermOwnCOldR.le_rpSum : ∀ (RS : List (AllocLabel × Cell × TermPiece.CrIt)) (y : AllocLabel × Cell × TermPiece.CrIt),
    y ∈ RS → y.2.2.2.2.2.2.1 ≤ TermPiece.rpSum RS y.2.2.1
  | [], _, h => absurd h List.not_mem_nil
  | z :: RS, y, h => by
      show y.2.2.2.2.2.2.1 ≤ TermOverCrX.rpSumI (z :: RS) y.2.2.1
      rw [TermOverCrX.rpSumI_cons]
      rcases List.mem_cons.1 h with e | h
      · subst e
        simp only [ite_true]
        exact Res.le_add_right _ _
      · exact Res.le_trans (TermOwnCOldR.le_rpSum RS y h) (TermOverCrW.le_add_leftR _ _)

/-- (Master of `overCr_old`) **The owner's cover at an old
frontier cell across a step, with re-pin items.** -/
theorem _root_.TermOwnCOldR.overCr_oldR {E E' : TEnv} {s s' : St} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell}
    {RS : List (AllocLabel × Cell × TermPiece.CrIt)}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
    (hsto : E.sto l = some c)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hstoL : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ o tw', TermPlant.LowOwn s' ⟨l, o⟩ tw' → FirstW s'.mem ⟨l, o⟩ tw' → PredU E ⟨l, o⟩ →
      PredU E' ⟨l, o⟩)
    (hFP : ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc.label = l →
      ¬ WordUnit E m.loc → ∀ q S usS, TermPiece.Piece c.ty q S → accs S = some usS → q ≤ m.loc.offset →
        m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
          TermPlant.LowOwn s ⟨l, o⟩ th0 → th0 ∉ s'.promises)
    (hRS : TermPiece.RepinQh E' s' RS)
    (hcrT : ∀ t m, t ∈ s'.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr t + TermPiece.rpSum RS t ≤ cr' t)
    (hcrR : ∀ t, TermPiece.rpSum RS t ≤ cr' t)
    (hz : ∀ t m, t ∈ s'.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr' t ≠ .zero → cr t ≠ .zero ∨ ∃ y ∈ RS, y.1 = l ∧ y.2.2.1 = t)
    (hcovN : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s' ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      (TermOverCr.CovU E c l o ∧ ¬ VisU E ⟨l, o⟩ ∧ TermPlant.LowOwn s ⟨l, o⟩ tw ∧
        TermOverCr.WinG E s l o tw ∧ TermPlant.OverT E s ⟨l, o⟩ tw) ∨
      (∃ x, TermOwnCOld.ZeroIt E' s' l c tw x) ∨ ∃ y ∈ RS, y.1 = l ∧ TermPiece.CrCov y.2.2 o)
    (hpreC : TermOverCr.OverCrE E s cr l c) : TermOverCr.OverCrE E' s' cr' l c := by
  obtain ⟨Gs, ⟨h1, h2, h3, h4, h5⟩, hHL⟩ := hpreC
  have hdrop : ∀ x ∈ Gs, x.1 ∉ s'.promises → ∀ usS, accs x.2.2.1 = some usS → ∀ o th0, x.2.1 ≤ o →
      o < x.2.1 + nWords usS → TermPlant.LowOwn s ⟨l, o⟩ th0 → th0 ∉ s'.promises := by
    intro x hx hn usS hus o th0 b1 b2 hlo
    obtain ⟨mh, usS', a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := h2 x hx
    rw [hus] at a7
    cases a7
    have hPc : TermPiece.Piece c.ty x.2.1 x.2.2.1 :=
      ⟨a5, a6, by rw [wc_of_accs hus]; simp only [ne_eq, Option.some.injEq]; omega⟩
    exact hFP x.1 mh a3.1 hn a1 a2 a4 x.2.1 x.2.2.1 usS hPc hus a8 a9 o th0 b1 b2 hlo
  let Gk := Gs.filter (fun x => decide (x.1 ∈ s'.promises))
  have hmemK : ∀ x, x ∈ Gk ↔ x ∈ Gs ∧ x.1 ∈ s'.promises := fun x => by
    simp only [Gk, List.mem_filter, decide_eq_true_eq]
  have hkP : ∀ x ∈ Gk, ∀ usS, accs x.2.2.1 = some usS → ∀ t m, t ∈ s.promises → s.mem[t]? = some m →
      m.loc.label = l → x.2.1 ≤ m.loc.offset → m.loc.offset < x.2.1 + nWords usS → t ∈ s'.promises := by
    intro x hx usS hus t m ht hm hl b1 b2
    obtain ⟨hxG, hxs⟩ := (hmemK x).1 hx
    have hn0 : nWords usS ≠ 0 := fun h => by rw [h, Nat.add_zero] at b2; exact absurd b2 (Nat.not_lt.mpr b1)
    by_cases ht' : t ∈ s'.promises
    · exact ht'
    · obtain ⟨mh, usS', a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := h2 x hxG
      rw [hus] at a7
      cases a7
      have hPc : TermPiece.Piece c.ty x.2.1 x.2.2.1 :=
        ⟨a5, a6, by rw [wc_of_accs hus]; simp only [ne_eq, Option.some.injEq]; exact hn0⟩
      have eh : mh.loc = ⟨l, mh.loc.offset⟩ := by rw [← a2]
      have em : m.loc = ⟨l, m.loc.offset⟩ := by rw [← hl]
      have hnwh : ¬ WordUnit E ⟨l, mh.loc.offset⟩ := by rw [← eh]; exact a4
      have hnwm : ¬ WordUnit E m.loc := by
        rw [em]
        exact TermFreeQW.noWU_piece hsto hPc hus a8 a9 b1 b2 hnwh
      have hlh : TermPlant.LowOwn s ⟨l, mh.loc.offset⟩ x.1 := by rw [← eh]; exact a3
      exact absurd hxs (hFP t m ht ht' hm hl hnwm x.2.1 x.2.2.1 usS hPc hus b1 b2 mh.loc.offset x.1 a8 a9 hlh)
  have hkU : ∀ x ∈ Gk, ∀ usS i o2, accs x.2.2.1 = some usS → InAcc usS i o2 → ∀ t m, t ∈ s.promises →
      s.mem[t]? = some m → m.loc = ⟨l, x.2.1 + o2⟩ → t ∈ s'.promises := by
    intro x hx usS i o2 hus hi t m ht hm hl
    exact hkP x hx usS hus t m ht hm (by rw [hl]) (by rw [hl]; exact Nat.le_add_right _ _)
      (by rw [hl]; exact Nat.add_lt_add_left (TermOwnCR5.inAcc_lt hi) _)
  -- a kept holder: its old credit plus its re-pin credit lie within the new one
  have hcrK2 : ∀ x ∈ Gk, cr x.1 + TermPiece.rpSum RS x.1 ≤ cr' x.1 := by
    intro x hx
    obtain ⟨hxG, hxs⟩ := (hmemK x).1 hx
    obtain ⟨mh, _, a1, a2, -, a4, -⟩ := h2 x hxG
    exact hcrT x.1 mh hxs a1 a2 a4
  have hcrK : ∀ x ∈ Gk, cr x.1 ≤ cr' x.1 := fun x hx =>
    Res.le_trans (Res.le_add_right _ _) (hcrK2 x hx)
  have hndK : (Gk.map (·.1)).Nodup :=
    List.Nodup.sublist ((List.filter_sublist
      (p := fun x : Ts × Nat × Ty × List Word × Res × (Nat → Bool) => decide (x.1 ∈ s'.promises))
      (l := Gs)).map _) h1
  -- the re-pin items at `l` sit at the cell `c`
  have hcell : ∀ y ∈ RS, y.1 = l → y.2.1 = c := by
    intro y hy hl
    have e1 := (hRS y hy).1
    rw [hl, hstoL, hsto] at e1
    exact (Option.some.inj e1).symm
  classical
  let g : Ts → Res := fun t => if t ∈ Gk.map (·.1) then cr t else .zero
  have hsumK : ∀ t, TermOverCrW.sumH Gk t ≤ g t := by
    refine TermOverCrW.sumH_le_of_nodup hndK ?_
    intro x hx
    have hm : x.1 ∈ Gk.map (·.1) := List.mem_map_of_mem hx
    obtain ⟨hxG, -⟩ := (hmemK x).1 hx
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, a12, -⟩ := h2 x hxG
    show x.2.2.2.2.1 ≤ (if x.1 ∈ Gk.map (·.1) then cr x.1 else .zero)
    simp only [hm, ↓reduceIte]
    exact a12
  refine TermOwnCP.overCr_assemble hcpl hni (Gk ++ TermOwnCOld.zeroWL E' s' l c ++ TermOverCrX.rpL RS l)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with h | h
      · exact TermOwnCR5.crItemQ_frameP hpre hP hsub (hkP x h) hstoL hV hPU (hcrK x h)
          (h2 x ((hmemK x).1 h).1)
      · obtain ⟨tw, o, -, hi, -⟩ := TermOwnCOld.mem_zeroWL h
        exact hi cr'
    · obtain ⟨y, hy, hl, rfl⟩ := TermOverCrX.mem_rpL.1 hx
      have hit := (hRS y hy).2.2.2.1
      rw [hl, hcell y hy hl] at hit
      have hb : y.2.2.2.2.2.2.1 ≤ cr' y.2.2.1 := Res.le_trans (TermOwnCOldR.le_rpSum RS y hy) (hcrR _)
      obtain ⟨mh, usS, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, bp⟩ := hit
      exact ⟨mh, usS, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, hb,
        fun i o w tw' hk hi hw hlo => .inl (bp i o w tw' hk hi hw hlo)⟩
  · intro t
    rw [TermOverCrW.sumH_append, TermOverCrW.sumH_append,
      TermOverCrW.sumH_zero (L := TermOwnCOld.zeroWL E' s' l c) (fun x hx => by
        obtain ⟨tw, o, -, -, hz0, -⟩ := TermOwnCOld.mem_zeroWL hx
        exact hz0) t, Res.add_zero]
    have a := hsumK t
    have b := TermOverCrX.sumH_rpL_le l t RS
    have b' : TermOverCrW.sumH (TermOverCrX.rpL RS l) t ≤ TermPiece.rpSum RS t := b
    by_cases ht : t ∈ Gk.map (·.1)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
      have d := hcrK2 x hx
      have a' : TermOverCrW.sumH Gk x.1 ≤ cr x.1 := by
        have := a; simp only [g, ht, ↓reduceIte] at this; exact this
      exact Res.le_trans (Res.add_le_add a' b') d
    · have a' : TermOverCrW.sumH Gk t ≤ .zero := by
        have := a; simp only [g, ht, ↓reduceIte] at this; exact this
      have d := hcrR t
      intro k
      have a1 := a' k; have b1 := b' k; have d1 := d k
      simp only [Res.add_apply, Res.zero_apply] at a1 b1 d1 ⊢; omega
  · intro x hx usS i o2 hus hk hi
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with h | h
      · obtain ⟨t0, ht0⟩ := h4 x ((hmemK x).1 h).1 usS i o2 hus hk hi
        exact ⟨t0, TermOwnCR5.lowOwn_fwdP hpre hP hsub (hkU x h usS i o2 hus hi) ht0⟩
      · obtain ⟨tw, o, -, -, -, -, hw, -⟩ := TermOwnCOld.mem_zeroWL h
        exact hw usS i o2 hus hk hi
    · obtain ⟨y, hy, hl, rfl⟩ := TermOverCrX.mem_rpL.1 hx
      have hc : TermPiece.CrCov y.2.2 (y.2.2.2.1 + o2) :=
        ⟨usS, i, hus, Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hi, hk⟩
      obtain ⟨tw, hlo, -⟩ := (hRS y hy).2.2.2.2.2.2 _ hc
      rw [hl] at hlo
      exact ⟨tw, hlo⟩
  · intro x hx usS hus t m ht hm hl b1 b2
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with h | h
      · have ht0 := hsub t ht
        exact hHL x ((hmemK x).1 h).1 usS hus t m ht0 (by rw [← hpre t (hP t ht0)]; exact hm) hl b1 b2
      · obtain ⟨tw, o, -, -, -, hH, -⟩ := TermOwnCOld.mem_zeroWL h
        exact hH x (List.mem_singleton_self x) usS hus t m ht hm hl b1 b2
    · obtain ⟨y, hy, hyl, rfl⟩ := TermOverCrX.mem_rpL.1 hx
      exact (hRS y hy).2.2.2.2.2.1 usS hus t m ht hm (by rw [hyl]; exact hl) b1 b2
  · intro o tw hc hv hlo hg hov
    rcases hcovN o tw hc hv hlo hg hov with ⟨hc0, hv0, hlo0, hg0, hov0⟩ | ⟨x, hx⟩ | ⟨y, hy, hyl, hcv⟩
    · obtain ⟨x, hx, usS, i, b1, b2, b3, b4⟩ := h3 o tw hc0 hv0 hlo0 hg0 hov0
      have hxs : x.1 ∈ s'.promises := by
        by_cases e : x.1 ∈ s'.promises
        · exact e
        · have hlt : o < x.2.1 + nWords usS := by
            have := TermOwnCR5.inAcc_lt b3
            omega
          exact absurd hlo.1 (hdrop x hx e usS b1 o tw b2 hlt hlo0)
      exact ⟨x, List.mem_append_left _ (List.mem_append_left _ ((hmemK x).2 ⟨hx, hxs⟩)), usS, i, b1, b2, b3, b4⟩
    · obtain ⟨x', hx', r⟩ := TermOwnCOld.zeroWL_cover hx hlo
      exact ⟨x', List.mem_append_left _ (List.mem_append_right _ hx'), r⟩
    · exact ⟨y.2.2, List.mem_append_right _ (TermOverCrX.mem_rpL.2 ⟨y, hy, hyl, rfl⟩), hcv⟩
  · intro t m ht hm hl hw hnz
    have ht0 := hsub t ht
    have hms : s.mem[t]? = some m := by rw [← hpre t (hP t ht0)]; exact hm
    have hw0 : ¬ WordUnit E m.loc := fun hw' => hw (by
      have e : E'.sto m.loc.label = E.sto m.loc.label := by rw [hl]; exact hstoL
      exact (WordUnit_congr e).2 hw')
    rw [List.map_append, List.map_append]
    rcases hz t m ht hms hl hw0 hnz with hnz0 | ⟨y, hy, hyl, hyt⟩
    · obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (h5 t m ht0 hms hl hw0 hnz0)
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨x, (hmemK x).2 ⟨hx, hx1 ▸ ht⟩, hx1⟩))
    · exact List.mem_append_right _
        (List.mem_map.2 ⟨y.2.2, TermOverCrX.mem_rpL.2 ⟨y, hy, hyl, rfl⟩, hyt⟩)

/-- **The owner's cover at an old frontier cell across a step.** -/
theorem overCr_old {E E' : TEnv} {s s' : St} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
    (hsto : E.sto l = some c)
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hstoL : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ o tw', TermPlant.LowOwn s' ⟨l, o⟩ tw' → FirstW s'.mem ⟨l, o⟩ tw' → PredU E ⟨l, o⟩ →
      PredU E' ⟨l, o⟩)
    (hFP : ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc.label = l →
      ¬ WordUnit E m.loc → ∀ q S usS, TermPiece.Piece c.ty q S → accs S = some usS → q ≤ m.loc.offset →
        m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
          TermPlant.LowOwn s ⟨l, o⟩ th0 → th0 ∉ s'.promises)
    (hcr : ∀ t m, t ∈ s'.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr t ≤ cr' t)
    (hz : ∀ t m, t ∈ s'.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr' t ≠ .zero → cr t ≠ .zero)
    (hcovN : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s' ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      (TermOverCr.CovU E c l o ∧ ¬ VisU E ⟨l, o⟩ ∧ TermPlant.LowOwn s ⟨l, o⟩ tw ∧
        TermOverCr.WinG E s l o tw ∧ TermPlant.OverT E s ⟨l, o⟩ tw) ∨
      ∃ x, ZeroIt E' s' l c tw x)
    (hpreC : TermOverCr.OverCrE E s cr l c) : TermOverCr.OverCrE E' s' cr' l c
 :=
  TermOwnCOldR.overCr_oldR (RS := []) hpre hP hsub hsto hcpl hni hstoL hV hPU hFP
    (fun _ h => absurd h List.not_mem_nil)
    (fun t m a b c d => Res.le_def.2 fun k => by
      have h := Res.le_def.1 (hcr t m a b c d) k
      simp only [TermPiece.rpSum_nil, Res.add_apply, Res.zero_apply] at h ⊢; omega)
    (fun t => by rw [TermPiece.rpSum_nil]; exact Res.zero_le _)
    (fun t m a b c d e => .inl (hz t m a b c d e))
    (fun o tw a b c d e => (hcovN o tw a b c d e).imp_right .inl) hpreC

#print axioms overCr_old


end TermOwnCOld
