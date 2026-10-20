import WeakCore.TermOverCr4

/-! # TermOverCr5: the owner's cover at its own op (step 5, draft)

At an own-path op the owner fulfils promises (memory unchanged, `r.1 = mem`).  By `PromAbove`
after the step a fulfilled promise is the lowest at its unit (`fulfil_low`).  Items not touching
a fulfilled unit are kept (`crItem_keep`); the units whose lowest promise was fulfilled get new
items from the op's accounting (2a re-key).  `overCr_ownop` combines them.
-/

namespace TermOverCr5
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **A fulfilled promise was the lowest at its unit** (among the promises still outstanding):
`PromAbove` after the step, with the thread's coherence at the unit reaching it. -/
theorem fulfil_low {s' : St} {tf : Ts} {a : Address} (hpa : PromAbove s') (hcoh : tf ≤ s'.vs.coh a) :
    ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m → m.loc = a → tf < t := by
  intro t m ht hm hl
  have h := hpa t ht m hm
  rw [hl] at h
  exact Nat.lt_of_le_of_lt hcoh h

#print axioms fulfil_low

section own
variable {s s' : St} (hmem : s'.mem = s.mem) (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
include hmem hsub

/-- **The lowest promise is kept at a unit where nothing was fulfilled.** -/
theorem lowOwn_keep {a : Address} {tw : Ts}
    (hnf : ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ a)
    (h : TermPlant.LowOwn s a tw) : TermPlant.LowOwn s' a tw := by
  obtain ⟨h1, ⟨m, hm, hl⟩, h3⟩ := h
  have h1' : tw ∈ s'.promises := by
    by_cases hin : tw ∈ s'.promises
    · exact hin
    · exact absurd hl (hnf tw m h1 hin hm)
  exact ⟨h1', ⟨m, by rw [hmem]; exact hm, hl⟩, fun t' m' ht' hm' hl' =>
    h3 t' m' (hsub t' ht') (by rw [← hmem]; exact hm') hl'⟩

omit hsub in
/-- **And back**: a post-step lowest promise at such a unit was lowest before. -/
theorem lowOwn_keep_back {a : Address} {tw : Ts}
    (hsub2 : ∀ t, t ∈ s'.promises → t ∈ s.promises)
    (hnf : ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ a)
    (h : TermPlant.LowOwn s' a tw) : TermPlant.LowOwn s a tw := by
  obtain ⟨h1, ⟨m, hm, hl⟩, h3⟩ := h
  refine ⟨hsub2 tw h1, ⟨m, by rw [← hmem]; exact hm, hl⟩, fun t' m' ht' hm' hl' => ?_⟩
  by_cases hin : t' ∈ s'.promises
  · exact h3 t' m' hin (by rw [hmem]; exact hm') hl'
  · exact absurd hl' (hnf t' m' ht' hin hm')

/-- **An item away from the fulfilled units is kept** (its holder's unit and every `K` unit
carry no fulfilled promise), with credits not lowered at its holder. -/
theorem crItem_keep {E E' : TEnv} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)}
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hcr : cr x.1 ≤ cr' x.1)
    (hnfH : ∀ mh, s.mem[x.1]? = some mh → ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m →
      m.loc ≠ mh.loc)
    (hnfK : ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, x.2.1 + o⟩)
    (hPU : ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      PredU E ⟨l, x.2.1 + o⟩ → PredU E' ⟨l, x.2.1 + o⟩)
    (h : TermOverCr.CrItemQ E s cr l c x) : TermOverCr.CrItemQ E' s' cr' l c x := by
  obtain ⟨mh, usS, hmh, hlab, hlo, hnw, hat, hsol, husS, hq1, hq2, hwl, hvr, hR, hpin⟩ := h
  refine ⟨mh, usS, by rw [hmem]; exact hmh, hlab, lowOwn_keep hmem hsub (hnfH mh hmh) hlo,
    fun hw => hnw ?_, hat, hsol, husS, hq1, hq2, hwl, hV _ _ _ hvr, Res.le_trans hR hcr,
    fun i o w tw' hk hi hw hl => ?_⟩
  · obtain ⟨c1, hc1, hor⟩ := hw
    exact ⟨c1, by rw [hlab, ← hsto, ← hlab]; exact hc1, hor⟩
  · have hl0 := lowOwn_keep_back hmem hsub (hnfK usS i o husS hk hi) hl
    rw [hmem]
    exact (hpin i o w tw' hk hi hw hl0).imp id (fun h => ⟨hPU usS i o husS hk hi h.1, h.2⟩)

#print axioms crItem_keep

/-- **The cover at the owner's own op.**  Kept items `Gk` (a sublist of the old items, away from
fulfilled units) plus new post-state items `Gn` (the 2a re-key, from the op's accounting). -/
theorem overCr_ownop {E E' : TEnv} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell} {G G' : Nat → Ts → Prop}
    {Gs Gk Gn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      PredU E ⟨l, x.2.1 + o⟩ → PredU E' ⟨l, x.2.1 + o⟩)
    (h : TermOverCr.OverCrL E s cr l c G Gs)
    (hGk : Gk.Sublist Gs)
    (hcrK : ∀ x ∈ Gk, cr x.1 ≤ cr' x.1)
    (hnfH : ∀ x ∈ Gk, ∀ mh, s.mem[x.1]? = some mh → ∀ t m, t ∈ s.promises → t ∉ s'.promises →
      s.mem[t]? = some m → m.loc ≠ mh.loc)
    (hnfK : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, x.2.1 + o⟩)
    (hGn : ∀ x ∈ Gn, TermOverCr.CrItemQ E' s' cr' l c x)
    (hnd : (Gn.map (·.1)).Nodup)
    (hdisj : ∀ x ∈ Gk, ∀ y ∈ Gn, x.1 ≠ y.1)
    (hwaN : ∀ x ∈ Gn, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s' ⟨l, x.2.1 + o⟩ t0)
    (hcovN : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s' ⟨l, o⟩ tw → G' o tw →
      TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ((∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, o⟩) ∧
        TermOverCr.CovU E c l o ∧ ¬ VisU E ⟨l, o⟩ ∧ G o tw ∧ TermPlant.OverT E s ⟨l, o⟩ tw ∧
        ∀ x ∈ Gs, (∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
          x.2.2.2.2.2 i = true) → x ∈ Gk) ∨
      ∃ x ∈ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hzN : ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E' m.loc →
      cr' t ≠ .zero → (cr t ≠ .zero ∧ ∀ x ∈ Gs, x.1 = t → x ∈ Gk) ∨ t ∈ Gn.map (·.1)) :
    TermOverCr.OverCrL E' s' cr' l c G' (Gk ++ Gn) := by
  obtain ⟨hnd0, hit, hcov, hwa, hz⟩ := h
  refine ⟨?_, fun x hx => ?_, fun o tw hi hv hl hg hov => ?_, fun x hx usS i o h1 h2 h3 => ?_,
    fun t m ht hm hl hw hnz => ?_⟩
  · rw [List.map_append]
    refine List.nodup_append.2 ⟨hnd0.sublist (hGk.map _), hnd, fun a ha b hb => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact hdisj x hx y hy
  · rcases List.mem_append.1 hx with hx | hx
    · exact crItem_keep hmem hsub hsto hV (hcrK x hx) (hnfH x hx) (hnfK x hx) (hPU x hx) (hit x (hGk.subset hx))
    · exact hGn x hx
  · rcases hcovN o tw hi hv hl hg hov with ⟨hnf, hi0, hv0, hg0, hov0, hin⟩ | ⟨x, hx, hr⟩
    · obtain ⟨x, hx, hr⟩ := hcov o tw hi0 hv0 (lowOwn_keep_back hmem hsub hnf hl) hg0 hov0
      exact ⟨x, List.mem_append_left _ (hin x hx hr), hr⟩
    · exact ⟨x, List.mem_append_right _ hx, hr⟩
  · rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨t0, h0⟩ := hwa x (hGk.subset hx) usS i o h1 h2 h3
      exact ⟨t0, lowOwn_keep hmem hsub (hnfK x hx usS i o h1 h2 h3) h0⟩
    · exact hwaN x hx usS i o h1 h2 h3
  · rw [List.map_append]
    rcases hzN t m ht hm hl hw hnz with ⟨hnz0, hk⟩ | hn
    · have hw0 : ¬ WordUnit E m.loc := fun hw0 => hw (by
        obtain ⟨c1, hc1, hor⟩ := hw0
        exact ⟨c1, by rw [hl, hsto, ← hl]; exact hc1, hor⟩)
      have hm0 : s.mem[t]? = some m := by rw [← hmem]; exact hm
      obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hz t m (hsub t ht) hm0 hl hw0 hnz0)
      exact List.mem_append_left _ (List.mem_map.2 ⟨x, hk x hx hx1, hx1⟩)
    · exact List.mem_append_right _ hn

#print axioms overCr_ownop

omit hmem hsub in
/-- (PredCov) **An op adds no covered unit**: with the cell kept, the frontier set and the typed
count not raised, a unit covered after the op was covered before (a unit newly initialised at
the real count was predicted: `rc ≤ ini`). -/
theorem covU_keep {E E' : TEnv} {l : AllocLabel} {c : Cell}
    (hsto0 : E.sto l = some c) (hsto : E'.sto l = E.sto l) (hpf : E.pfr l ≠ none)
    (hini : E'.ini l ≤ E.ini l) : ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o := by
  intro o hi
  refine Classical.byContradiction fun hi0 => ?_
  have hri : E'.rc l ≤ E.ini l := Nat.le_trans (E'.rc_le_ini l) hini
  have hW : IniW E ⟨l, o⟩ := fun c1 N e us h1 h2 h3 => by
    rw [hsto0] at h1
    cases h1
    rcases hi with hI | ⟨-, hW', -⟩
    · exact Nat.lt_of_lt_of_le (hI N e us h2 h3) (Nat.mul_le_mul_right _ hri)
    · exact Nat.lt_of_lt_of_le (hW' c N e us (by rw [hsto]; exact hsto0) h2 h3)
        (Nat.mul_le_mul_right _ hini)
  refine hi0 (.inr ⟨hpf, hW, fun hw => ?_⟩)
  exact hi0 (.inl fun N e us h2 h3 => hw c N e us hsto0 h2 h3)

#print axioms covU_keep

omit hmem hsub in
/-- (PredCov) **A unit of a frontier cell at an initialised offset is covered**: below the real
count it is `InitRr`; between the real and the reader-visible count it is predicted. -/
theorem covU_of_initR {E : TEnv} {l : AllocLabel} {c : Cell} {o : Nat}
    (hsto0 : E.sto l = some c) (hpf : E.pfr l ≠ none) (hI : InitR E c l o) : TermOverCr.CovU E c l o := by
  by_cases hr : IniWr E ⟨l, o⟩
  · exact .inl fun N e us h2 h3 => hr c N e us hsto0 h2 h3
  · refine .inr ⟨hpf, fun c1 N e us h1 h2 h3 => ?_, hr⟩
    rw [hsto0] at h1
    cases h1
    exact hI N e us h2 h3

#print axioms covU_of_initR

/-- **`overCr_ownop` at an own op**: the new-cover premise `hcovN0` is asked only at units
covered before the op, which is every unit with an own outstanding promise (`covU_of_initR`:
`PromIniE`, the `promIni` clause at the cut, puts such a promise at an initialised offset).
No bound on the step's counts is needed: an `ini` rise only initialises units no promise sits at. -/
theorem overCr_ownopR {E E' : TEnv} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell} {G G' : Nat → Ts → Prop}
    {Gs Gk Gn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hsto0 : E.sto l = some c) (hpf : E.pfr l ≠ none)
    (hpi : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → ∀ cl, E.sto m.loc.label = some cl →
      E.pfr m.loc.label ≠ none → InitR E cl m.loc.label m.loc.offset)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      PredU E ⟨l, x.2.1 + o⟩ → PredU E' ⟨l, x.2.1 + o⟩)
    (h : TermOverCr.OverCrL E s cr l c G Gs)
    (hGk : Gk.Sublist Gs)
    (hcrK : ∀ x ∈ Gk, cr x.1 ≤ cr' x.1)
    (hnfH : ∀ x ∈ Gk, ∀ mh, s.mem[x.1]? = some mh → ∀ t m, t ∈ s.promises → t ∉ s'.promises →
      s.mem[t]? = some m → m.loc ≠ mh.loc)
    (hnfK : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, x.2.1 + o⟩)
    (hGn : ∀ x ∈ Gn, TermOverCr.CrItemQ E' s' cr' l c x)
    (hnd : (Gn.map (·.1)).Nodup)
    (hdisj : ∀ x ∈ Gk, ∀ y ∈ Gn, x.1 ≠ y.1)
    (hwaN : ∀ x ∈ Gn, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s' ⟨l, x.2.1 + o⟩ t0)
    (hcovN0 : ∀ o tw, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s' ⟨l, o⟩ tw →
      G' o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ((∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, o⟩) ∧
        ¬ VisU E ⟨l, o⟩ ∧ G o tw ∧ TermPlant.OverT E s ⟨l, o⟩ tw ∧
        ∀ x ∈ Gs, (∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
          x.2.2.2.2.2 i = true) → x ∈ Gk) ∨
      ∃ x ∈ Gn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hzN : ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E' m.loc →
      cr' t ≠ .zero → (cr t ≠ .zero ∧ ∀ x ∈ Gs, x.1 = t → x ∈ Gk) ∨ t ∈ Gn.map (·.1)) :
    TermOverCr.OverCrL E' s' cr' l c G' (Gk ++ Gn) := by
  refine overCr_ownop hmem hsub hsto hV hPU h hGk hcrK hnfH hnfK hGn hnd hdisj hwaN
    (fun o tw hi hv hl hg hov => ?_) hzN
  have hi0 : TermOverCr.CovU E c l o := by
    obtain ⟨htw, ⟨m, hm, hml⟩, -⟩ := hl
    have hm0 : s.mem[tw]? = some m := by rw [← hmem]; exact hm
    have hI := hpi tw m (hsub tw htw) hm0 c (by rw [hml]; exact hsto0) (by rw [hml]; exact hpf)
    rw [hml] at hI
    exact covU_of_initR hsto0 hpf hI
  rcases hcovN0 o tw hi hi0 hv hl hg hov with ⟨hnf, hv0, hg0, hov0, hin⟩ | hr
  · exact Or.inl ⟨hnf, hi0, hv0, hg0, hov0, hin⟩
  · exact Or.inr hr

#print axioms overCr_ownopR

end own

end TermOverCr5
