import WeakCore.TermOverCrX

/-! # TermOwnCF: the frame of the owner's cover at a step keeping its cell (ownC case (i))

`overCrL_frame`: at a step of the owner that keeps the memory prefix, puts no new message at the
label `l`, keeps the owner's promises, and keeps the cell's typing facts at `l`, the old item list
still carries the cover at any credit `cr'` above the old one at every holder, provided the
guard and overtaking predicates only shrink (`hG`, `hOT`: the step-specific content). -/

namespace TermOwnCF
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {s s' : St} {l : AllocLabel}
  (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
  (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
  (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
  (hkeep : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → t ∈ s'.promises)

include hpre hP hsub hkeep in
theorem lowOwn_fwdA {a : Address} (ha : a.label = l) {tw : Ts} (h : TermPlant.LowOwn s a tw) :
    TermPlant.LowOwn s' a tw := by
  obtain ⟨h1, ⟨m, hm, hl⟩, h3⟩ := h
  refine ⟨hkeep tw m h1 hm (by rw [hl, ha]), ⟨m, by rw [hpre tw (hP tw h1)]; exact hm, hl⟩,
    fun t' m' ht' hm' hl' => ?_⟩
  have ht0 := hsub t' ht'
  exact h3 t' m' ht0 (by rw [← hpre t' (hP t' ht0)]; exact hm') hl'

include hpre hP hsub hkeep in
theorem lowOwn_backA {a : Address} (ha : a.label = l) {tw : Ts} (h : TermPlant.LowOwn s' a tw) :
    TermPlant.LowOwn s a tw := by
  obtain ⟨h1, ⟨m, hm, hl⟩, h3⟩ := h
  have h1' := hsub tw h1
  refine ⟨h1', ⟨m, by rw [← hpre tw (hP tw h1')]; exact hm, hl⟩, fun t' m' ht' hm' hl' => ?_⟩
  exact h3 t' m' (hkeep t' m' ht' hm' (by rw [hl', ha])) (by rw [hpre t' (hP t' ht')]; exact hm') hl'

include hpre hP hsub hkeep in
theorem lowOwn_fwdE {o : Nat} {tw : Ts} (h : TermPlant.LowOwn s ⟨l, o⟩ tw) : TermPlant.LowOwn s' ⟨l, o⟩ tw :=
  lowOwn_fwdA hpre hP hsub hkeep rfl h

include hpre hP hsub hkeep in
theorem lowOwn_backE {o : Nat} {tw : Ts} (h : TermPlant.LowOwn s' ⟨l, o⟩ tw) : TermPlant.LowOwn s ⟨l, o⟩ tw :=
  lowOwn_backA hpre hP hsub hkeep rfl h

include hpre in
theorem firstW_fwd {a : Address} {h : Ts} (hh : h < s.mem.size) (hf : FirstW s.mem a h) : FirstW s'.mem a h := by
  obtain ⟨⟨m, hm, hl, hu⟩, h2⟩ := hf
  refine ⟨⟨m, by rw [hpre h hh]; exact hm, hl, hu⟩, fun t m' ht hm' hl' => h2 t m' ht ?_ hl'⟩
  rw [← hpre t (Nat.lt_trans ht hh)]; exact hm'

include hpre hP hsub hkeep in
/-- **A predicted-unit credit item is kept** along such a step. -/
theorem crItemQ_frame {E E' : TEnv} {cr cr' : Ts → Res} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (hstoL : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ o tw', TermPlant.LowOwn s' ⟨l, o⟩ tw' → FirstW s'.mem ⟨l, o⟩ tw' → PredU E ⟨l, o⟩ →
      PredU E' ⟨l, o⟩) (hcr : cr x.1 ≤ cr' x.1)
    (h : TermOverCr.CrItemQ E s cr l c x) : TermOverCr.CrItemQ E' s' cr' l c x := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  have hx : x.1 < s.mem.size := hP _ a3.1
  refine ⟨mh, usS, by rw [hpre _ hx]; exact a1, a2, lowOwn_fwdA hpre hP hsub hkeep a2 a3, ?_, a5, a6, a7, a8, a9, a10,
    hV _ _ _ a11, Res.le_trans a12 hcr, ?_⟩
  · intro hw; apply a4
    have e : E'.sto mh.loc.label = E.sto mh.loc.label := by rw [a2]; exact hstoL
    exact (WordUnit_congr e).1 hw
  · intro i o w tw' hK hIn hw hlo
    have hlo0 := lowOwn_backE hpre hP hsub hkeep hlo
    have htw : tw' < s.mem.size := hP _ hlo0.1
    rcases a13 i o w tw' hK hIn hw hlo0 with hp | ⟨hu, hf, m, hm, hmw⟩
    · exact .inl (TermPlant.PredAt_mono htw hpre hp)
    · have hf' := firstW_fwd hpre htw hf
      exact .inr ⟨hPU _ _ hlo hf' hu, hf', m, by rw [hpre _ htw]; exact hm, hmw⟩

include hpre hP hsub hkeep in
/-- **The frame of the owner's cover**: the old items carry the cover after the step. -/
theorem overCrL_frame {E E' : TEnv} {cr cr' : Ts → Res} {c : Cell} {G G' : Nat → Ts → Prop}
    {Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hstoL : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ o tw', TermPlant.LowOwn s' ⟨l, o⟩ tw' → FirstW s'.mem ⟨l, o⟩ tw' → PredU E ⟨l, o⟩ →
      PredU E' ⟨l, o⟩)
    (hCov : ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o)
    (hVis : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hG : ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → G' o tw → G o tw)
    (hOT : ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw)
    (hcr : ∀ x ∈ Gs, cr x.1 ≤ cr' x.1)
    (hz : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      cr' t ≠ .zero → cr t ≠ .zero)
    (h : TermOverCr.OverCrL E s cr l c G Gs) (hHL : TermOverCr.HolderLow s l Gs) :
    TermOverCr.OverCrL E' s' cr' l c G' Gs ∧ TermOverCr.HolderLow s' l Gs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨⟨h1, fun x hx => crItemQ_frame hpre hP hsub hkeep hstoL hV hPU (hcr x hx) (h2 x hx), ?_, ?_, ?_⟩, ?_⟩
  · intro o tw hc hv hlo hg hov
    have hlo0 := lowOwn_backE hpre hP hsub hkeep hlo
    exact h3 o tw (hCov o hc) (hVis o hv) hlo0 (hG o tw hlo0 hg) (hOT o tw hlo0 hov)
  · intro x hx usS i o h1' h2' h3'
    obtain ⟨t0, ht0⟩ := h4 x hx usS i o h1' h2' h3'
    exact ⟨t0, lowOwn_fwdE hpre hP hsub hkeep ht0⟩
  · intro t m ht hm hl hw hnz
    replace ht := hsub t ht
    have hm0 : s.mem[t]? = some m := by rw [← hpre t (hP t ht)]; exact hm
    have hw0 : ¬ WordUnit E m.loc := fun hw' => hw (by
      have e : E'.sto m.loc.label = E.sto m.loc.label := by rw [hl]; exact hstoL
      exact (WordUnit_congr e).2 hw')
    exact h5 t m ht hm0 hl hw0 (hz t m ht hm0 hl hw0 hnz)
  · intro x hx usS hus t m ht hm hl b1 b2
    replace ht := hsub t ht
    exact hHL x hx usS hus t m ht (by rw [← hpre t (hP t ht)]; exact hm) hl b1 b2

include hpre hsub in
/-- The window conditions shrink along a step not raising the coherence at the unit and keeping
the footprint promises at the label. -/
theorem winG_back {E E' : TEnv} {o : Nat} {tw : Ts}
    (hcoh : s'.vs.coh ⟨l, o⟩ ≤ s.vs.coh ⟨l, o⟩)
    (hfp : ∀ t m, t ∈ FpAt E ⟨l, 0⟩ → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ∈ FpAt E' ⟨l, 0⟩)
    (h : TermOverCr.WinG E' s' l o tw) : TermOverCr.WinG E s l o tw := by
  refine ⟨fun t m hm hl ht => ?_, fun t m ht hm hl => ?_⟩
  · have ht' : t < s.mem.size := TermPiece.lt_size_of_some hm
    by_cases hin : t ∈ s.promises
    · exact .inl hin
    rcases h.1 t m (by rw [hpre t ht']; exact hm) hl ht with h1 | h1
    · exact absurd (hsub t h1) hin
    · exact .inr (by rw [hl] at h1 ⊢; exact Nat.le_trans h1 hcoh)
  · have ht' : t < s.mem.size := TermPiece.lt_size_of_some hm
    exact h.2 t m (hfp t m ht hm hl) (by rw [hpre t ht']; exact hm) hl

include hpre in
/-- Overtaking shrinks along a step putting no new message at the label and skipping no fewer old
messages at the unit. -/
theorem overT_back {E E' : TEnv} {o : Nat} {tw : Ts}
    (hnew : ∀ t m, s.mem.size ≤ t → s'.mem[t]? = some m → m.loc.label ≠ l)
    (hprom : ∀ t, t < s.mem.size → t ∈ PromAt E s ⟨l, o⟩ → t ∈ PromAt E' s' ⟨l, o⟩)
    (h : TermPlant.OverT E' s' ⟨l, o⟩ tw) : TermPlant.OverT E s ⟨l, o⟩ tw := by
  obtain ⟨t, m, h1, h2, h3, h4⟩ := h
  have ht : t < s.mem.size := Nat.lt_of_not_le fun hle => hnew t m hle h2 (by rw [h3])
  exact ⟨t, m, h1, by rw [← hpre t ht]; exact h2, h3, fun h' => h4 (hprom t ht h')⟩

end

#print axioms overCrL_frame
#print axioms winG_back
#print axioms overT_back

end TermOwnCF
