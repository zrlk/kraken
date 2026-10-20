import WeakCore.TermOwnCOldR

/-! # TermOwnCGlue: the post-demand trichotomy of the owner's cover (ownC item 3)

`hcovN_of`: `overCr_oldR`'s `hcovN` at the state level.  At a unit `a = ⟨l, o⟩` carrying a
post-step demand, compare the stepper's coherence at `a` before and after the step:
* not raised: the demand is a pre-step demand (no own promise at `a` was fulfilled, `FulC`; no new
  message at `a` overtakes, the step's new messages lie at or below its coherence, `hNC`);
* raised to a pre-step own promise (a fulfilment at `a`): `hB` (the step-shape cover);
* raised to an old non-promise message (a read at `a`): `hC` (the read cover);
* raised to a new message: impossible (`PromAbove` after the step, the lowest own promise is old).
-/

namespace TermOwnCGlue

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The post-step demand at unit `⟨l, o⟩`. -/
def PostD (E' : TEnv) (s' : St) (l : AllocLabel) (c : Cell) (o : Nat) (tw : Ts) : Prop :=
  TermOverCr.CovU E' c l o ∧ ¬ VisU E' ⟨l, o⟩ ∧ TermPlant.LowOwn s' ⟨l, o⟩ tw ∧
    TermOverCr.WinG E' s' l o tw ∧ TermPlant.OverT E' s' ⟨l, o⟩ tw

/-- The cover alternatives other than a pre-step demand. -/
def AltCov (E' : TEnv) (s' : St) (l : AllocLabel) (c : Cell)
    (RS : List (AllocLabel × Cell × TermPiece.CrIt)) (o : Nat) (tw : Ts) : Prop :=
  (∃ x, TermOwnCOld.ZeroIt E' s' l c tw x) ∨ ∃ y ∈ RS, y.1 = l ∧ TermPiece.CrCov y.2.2 o

theorem hcovN_of {E E' : TEnv} {s s' : St} {l : AllocLabel} {c : Cell}
    {RS : List (AllocLabel × Cell × TermPiece.CrIt)}
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hP : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
    (hFC : TermTyped.FulC s s') (hPA : PromAbove s) (hPA' : PromAbove s')
    (hNC : ∀ t m, s.mem.size ≤ t → s'.mem[t]? = some m → m.loc.label = l → t ≤ s'.vs.coh m.loc)
    (hsto : E'.sto l = E.sto l) (htid : E'.tid = E.tid) (hpfe : E'.pfr l = E.pfr l) (hfpe : E'.fp = E.fp)
    (hSame : ∀ o tw, TermPlant.LowOwn s ⟨l, o⟩ tw → s'.vs.coh ⟨l, o⟩ ≤ s.vs.coh ⟨l, o⟩ →
      (PredU E' ⟨l, o⟩ → PredU E ⟨l, o⟩) ∧ (TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o))
    (hB : ∀ o tw, PostD E' s' l c o tw → s.vs.coh ⟨l, o⟩ < s'.vs.coh ⟨l, o⟩ →
      s'.vs.coh ⟨l, o⟩ ∈ s.promises → AltCov E' s' l c RS o tw)
    (hC : ∀ o tw, PostD E' s' l c o tw → s.vs.coh ⟨l, o⟩ < s'.vs.coh ⟨l, o⟩ →
      s'.vs.coh ⟨l, o⟩ < s.mem.size → s'.vs.coh ⟨l, o⟩ ∉ s.promises → AltCov E' s' l c RS o tw) :
    ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s' ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      (TermOverCr.CovU E c l o ∧ ¬ VisU E ⟨l, o⟩ ∧ TermPlant.LowOwn s ⟨l, o⟩ tw ∧
        TermOverCr.WinG E s l o tw ∧ TermPlant.OverT E s ⟨l, o⟩ tw) ∨
      (∃ x, TermOwnCOld.ZeroIt E' s' l c tw x) ∨ ∃ y ∈ RS, y.1 = l ∧ TermPiece.CrCov y.2.2 o := by
  intro o tw hcov hv hlo hg hov
  have hD : PostD E' s' l c o tw := ⟨hcov, hv, hlo, hg, hov⟩
  obtain ⟨htw', ⟨mw, hmw', hlw⟩, hmin'⟩ := id hlo
  have htw : tw ∈ s.promises := hsub tw htw'
  have htwS : tw < s.mem.size := hP tw htw
  have hmw : s.mem[tw]? = some mw := by rw [← hpre tw htwS]; exact hmw'
  -- the post-step coherence at the unit lies below the lowest own promise there
  have hlt' : s'.vs.coh ⟨l, o⟩ < tw := by
    have h := hPA' tw htw' mw hmw'
    rw [hlw] at h
    exact h
  have hlt : s.vs.coh ⟨l, o⟩ < tw := by
    have h := hPA tw htw mw hmw
    rw [hlw] at h
    exact h
  by_cases hle : s'.vs.coh ⟨l, o⟩ ≤ s.vs.coh ⟨l, o⟩
  · -- coherence not raised: a pre-step demand
    left
    have hloS : TermPlant.LowOwn s ⟨l, o⟩ tw := by
      refine ⟨htw, ⟨mw, hmw, hlw⟩, fun t' m' ht' hm' hl' => ?_⟩
      by_cases ht'' : t' ∈ s'.promises
      · exact hmin' t' m' ht'' (by rw [hpre t' (hP t' ht')]; exact hm') hl'
      · obtain ⟨m'', hm'', hc⟩ := hFC t' ht' ht''
        rw [hm'] at hm''
        obtain rfl := Option.some.inj hm''
        rw [hl'] at hc
        have h := hPA t' ht' m' hm'
        rw [hl'] at h
        rw [hc] at hle
        exact absurd (Nat.lt_of_lt_of_le h hle) (Nat.lt_irrefl _)
    obtain ⟨hpu, hcb⟩ := hSame o tw hloS hle
    -- no own promise at the unit was fulfilled
    have hkeep : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc = ⟨l, o⟩ → t ∈ s'.promises := by
      intro t m ht hm hl
      by_cases ht' : t ∈ s'.promises
      · exact ht'
      · obtain ⟨m', hm', hc⟩ := hFC t ht ht'
        rw [hm] at hm'
        obtain rfl := Option.some.inj hm'
        rw [hl] at hc
        have h := hPA t ht m hm
        rw [hl] at h
        rw [hc] at hle
        exact absurd (Nat.lt_of_lt_of_le h hle) (Nat.lt_irrefl _)
    have hvE : ¬ VisU E ⟨l, o⟩ := fun h => hv ((VisU_congr (a := ⟨l, o⟩) hsto htid hpfe).2 h)
    have hFa : ∀ o', FpAt E' ⟨l, o'⟩ = FpAt E ⟨l, o'⟩ := fun o' => FpAt_congr hsto htid hpfe hfpe
    refine ⟨hcb hcov, hvE, hloS, ?_, ?_⟩
    · refine TermOwnCF.winG_back hpre hsub hle (fun t m ht _ _ => ?_) hg
      rw [hFa]; exact ht
    · obtain ⟨t, m, h1, h2, h3, h4⟩ := hov
      have ht : t < s.mem.size := by
        refine Nat.lt_of_not_le fun hge => ?_
        have h5 := hNC t m hge h2 (by rw [h3])
        rw [h3] at h5
        exact absurd (Nat.lt_trans (Nat.lt_of_lt_of_le h1 h5) hlt') (Nat.lt_irrefl _)
      have hm0 : s.mem[t]? = some m := by rw [← hpre t ht]; exact h2
      refine ⟨t, m, h1, hm0, h3, fun hin => h4 ?_⟩
      have hv' : ¬ VisU E' ⟨l, o⟩ := hv
      have hk : t ∈ s.promises → t ∈ s'.promises := fun h => hkeep t m h hm0 h3
      unfold PromAt at hin ⊢
      by_cases hp' : PredU E' ⟨l, o⟩
      · have hp : PredU E ⟨l, o⟩ := hpu hp'
        simp only [hvE, hv', hp, hp', ↓reduceIte, List.mem_filter, List.mem_append,
          decide_eq_true_eq, hFa] at hin ⊢
        obtain ⟨h5, hab⟩ := hin
        obtain ⟨hh, hfw, hht⟩ := hab
        refine ⟨?_, ⟨hh, TermOwnCF.firstW_fwd hpre (Nat.lt_trans hht ht) hfw, hht⟩⟩
        rcases h5 with h5 | h5
        · exact .inl (hk h5)
        · exact .inr h5
      · have hin' : t ∈ s.promises ∨ t ∈ FpAt E ⟨l, o⟩ := by
          by_cases hp : PredU E ⟨l, o⟩
          · simp only [hvE, hp, ↓reduceIte, List.mem_filter, List.mem_append] at hin
            exact hin.1
          · simp only [hvE, hp, ↓reduceIte, List.mem_append] at hin
            exact hin
        simp only [hv', hp', ↓reduceIte, List.mem_append, hFa]
        rcases hin' with h5 | h5
        · exact .inl (hk h5)
        · exact .inr h5
  · right
    have hgt : s.vs.coh ⟨l, o⟩ < s'.vs.coh ⟨l, o⟩ := Nat.lt_of_not_le hle
    by_cases hK : s'.vs.coh ⟨l, o⟩ ∈ s.promises
    · exact hB o tw hD hgt hK
    · exact hC o tw hD hgt (Nat.lt_trans hlt' htwS) hK

#print axioms hcovN_of

end TermOwnCGlue
