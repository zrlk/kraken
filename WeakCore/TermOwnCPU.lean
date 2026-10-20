import WeakCore.TermOwnCGlue
import WeakCore.TermOwnCH
import WeakCore.TermPromStep
import WeakCore.TermSeenHid

/-! # TermOwnCPU: predicted units stay predicted under a first-write own promise (ownC)

`hPU_core`: `overCr_oldR`'s `hPU` without any knowledge of how the step moves the counts
(no `RcKeepC`).  At a unit `b = ⟨l, o⟩` of an own frontier buffer whose first write `tw'` is an
outstanding own promise (`LowOwn`, `FirstW`), a predicted unit stays predicted: were it initialised
at the real count afterwards (`IniWr E' b`), the owner's invariant after the step (`OwnOKSF E'`)
would type the coherence message at `b` (`TermOwnCPin.coh_wordOK`), while `PromAbove` after the
step puts coherence below `tw'`, where every message at `b` is the placeholder `undef` (`FirstW`);
`undef` is no typed word at a one-word unit (`undef_nwordOK_one`), and `b` is one (an outstanding
promise lies on no two-word unit, `PromNoTwoOK`, so its access unit is the word alone).

**Stage-A check.**
(1) `MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2)` is an explicit premise of
`OpenOverCrOwnK` (TermOverCrBII), the stepper's post-state output: in TermMain it is `hm'` of the
tuple from `TermPlant.tstepMCF_stepTKA_zf`, the typed step lemma on pre-state data; it is not
derived from the invariant being proved.
(2) ownC is not on the certificate side: `PromAbove` after the step is likewise a premise of
`OpenOverCrOwnK`, consumed, never produced.
(3) No circularity: ownC proves the post-step `OverCrE` from the pre-step `OverCrG` (the induction
hypothesis) and the stepper's post outputs; `MemInv′` comes from pre-state facts only.
-/

namespace TermOwnCPU

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A word alone in its access unit is a `.one` unit. -/
theorem oneAt_of_single : ∀ (us : List Acc) (o : Nat), o < nWords us →
    (∀ i, InAcc us i o → ∀ o2, InAcc us i o2 → o2 = o) → TermFul.OneAt us o
  | [], o, h, _ => by simp [nWords] at h
  | u :: us, o, h, hs => by
      have hc : nWords (u :: us) = u.size + nWords us := TermTear.nWords_cons u us
      by_cases hlt : o < u.size
      · have h0 : InAcc (u :: us) 0 o := by
          refine ⟨by simp [nWords], ?_⟩
          simp only [List.take_succ_cons, List.take_zero, nWords, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil]
          omega
        cases u with
        | one =>
            have e : o = 0 := by simp only [Acc.size] at hlt; omega
            subst e
            exact TermFul.OneAt.here us
        | two =>
            have hsz : Acc.two.size = 2 := rfl
            have h1 : InAcc (Acc.two :: us) 0 (1 - o) := by
              refine ⟨by simp [nWords], ?_⟩
              simp only [List.take_succ_cons, List.take_zero, nWords, List.map_cons, List.map_nil,
                List.sum_cons, List.sum_nil, Acc.size]
              omega
            have e := hs 0 h0 (1 - o) h1
            rw [hsz] at hlt
            omega
      · have hge : u.size ≤ o := Nat.le_of_not_lt hlt
        have ih := oneAt_of_single us (o - u.size) (by omega) (fun i hi o2 h2 => by
          have hi' : InAcc (u :: us) (i + 1) o := by
            obtain ⟨a1, a2⟩ := hi
            refine ⟨?_, ?_⟩
            · rw [List.take_succ_cons, TermTear.nWords_cons]
              omega
            · rw [List.take_succ_cons, TermTear.nWords_cons]
              omega
          have h2' : InAcc (u :: us) (i + 1) (o2 + u.size) := by
            obtain ⟨a1, a2⟩ := h2
            refine ⟨?_, ?_⟩
            · rw [List.take_succ_cons, TermTear.nWords_cons]
              omega
            · rw [List.take_succ_cons, TermTear.nWords_cons]
              omega
          have e := hs (i + 1) hi' (o2 + u.size) h2'
          omega)
        have h2 := TermFul.OneAt.cons u ih
        have e : o - u.size + u.size = o := by omega
        rw [e] at h2
        exact h2

#print axioms oneAt_of_single

/-- **A predicted unit under a first-write own promise stays predicted** (`overCr_oldR`'s `hPU`). -/
theorem hPU_core {E E' : TEnv} {s' : St} {l : AllocLabel} {c : Cell} {Sk : Ts → Prop}
    (hsto' : E'.sto l = some c) (hown : c.owner = some E'.tid)
    (hOK : OwnOKSF E' s'.mem s'.pairs s'.vs Sk)
    (hsto : E'.sto l = E.sto l) (hpfe : E'.pfr l = E.pfr l) (hini : E.ini l ≤ E'.ini l)
    (hPA' : PromAbove s')
    (hPc : ∀ o tw', TermPlant.LowOwn s' ⟨l, o⟩ tw' →
      ∃ q S us, AtOff c.ty q S ∧ accs S = some us ∧ q ≤ o ∧ o < q + nWords us)
    (hno : ∀ o tw', TermPlant.LowOwn s' ⟨l, o⟩ tw' → ∀ q', TwoAtT c.ty q' → o ≠ q' ∧ o ≠ q' + 1) :
    ∀ o tw', TermPlant.LowOwn s' ⟨l, o⟩ tw' → FirstW s'.mem ⟨l, o⟩ tw' → PredU E ⟨l, o⟩ →
      PredU E' ⟨l, o⟩ := by
  intro o tw' hlo hfw hpu
  obtain ⟨hpf, hiw, hnr⟩ := hpu
  have hsto0 : E.sto l = some c := hsto.symm.trans hsto'
  have hiw' : IniW E' ⟨l, o⟩ := by
    intro c1 N e us h1 h2 h3
    have h4 := hiw c1 N e us (hsto.symm.trans h1) h2 h3
    exact Nat.lt_of_lt_of_le h4 (Nat.mul_le_mul_right _ hini)
  by_cases hw : IniWr E' ⟨l, o⟩
  · -- initialised afterwards: impossible
    by_cases hA : ∃ N e us, c.ty = .array (.lit N) e ∧ accs e = some us
    · obtain ⟨N, e, us, hty, he⟩ := hA
      have hrc : o < E'.rc l * nWords us := hw c N e us hsto' hty he
      obtain ⟨vals, hc, hL, -⟩ := hOK l c hsto' hown
      obtain ⟨q, S, usS, hat, hus, hq1, hq2⟩ := hPc o tw' hlo
      have hoN : o < N * nWords us := by
        have hj : o - q < nWords usS := Nat.sub_lt_left_of_lt_add hq1 hq2
        have h := TermSeenHid.off_lt_buf (j := o - q) hat hty he hus hj
        have e2 : q + (o - q) = o := by omega
        rw [e2] at h
        exact h
      have hlen : o < vals.length := by
        rcases hc with ⟨hwc, -⟩ | ⟨N', e', us', hT', hus', -, hlen, -⟩
        · rw [hty] at hwc
          simp [wc, accs] at hwc
        · rw [hty] at hT'
          simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
          obtain ⟨rfl, rfl⟩ := hT'
          rw [he] at hus'
          cases hus'
          rw [hlen]
          exact hoN
      have hv : vals[o]? = some vals[o] := List.getElem?_eq_getElem hlen
      have hi : ∀ N1 e1 us1, c.ty = .array (.lit N1) e1 → accs e1 = some us1 → o < E'.rc l * nWords us1 := by
        intro N1 e1 us1 h1 h2
        rw [hty] at h1
        simp only [Ty.array.injEq, Idx.lit.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rw [he] at h2
        cases h2
        exact hrc
      obtain ⟨m, hm, hml, hok⟩ := TermOwnCPin.coh_wordOK hc hi hv (hL o vals[o] hv)
      have hclt : s'.vs.coh ⟨l, o⟩ < tw' := TermOwnCPin.coh_lt_of_promAbove hPA' hlo
      have hund : m.val = .undef := hfw.2 _ m hclt hm hml
      have hone : TermFul.OneAt usS (o - q) := by
        refine oneAt_of_single usS (o - q) (Nat.sub_lt_left_of_lt_add hq1 hq2) (fun i hi1 o2 h2 => ?_)
        have e2 : q + (o - q) = o := by omega
        exact TermOverCrW.inAcc_single hat hus hi1 (.inr ⟨N, e, hty⟩) (by rw [e2]; exact hno o tw' hlo) o2 h2
      have hnot := TermPromStep.undef_nwordOK_one (E := E') hat hus hone (w := mw m) hund
      have e2 : q + (o - q) = o := by omega
      rw [e2] at hnot
      exact absurd hok hnot
    · refine absurd (fun c1 N e us h1 h2 h3 => ?_) hnr
      rw [hsto0] at h1
      cases h1
      exact absurd ⟨N, e, us, h2, h3⟩ hA
  · exact ⟨by rw [hpfe]; exact hpf, hiw', hw⟩

#print axioms hPU_core

end TermOwnCPU
