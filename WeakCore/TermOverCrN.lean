import WeakCore.TermOverCrH

/-! # TermOverCrN: access units at own promises are single words (hcovD O3)

`PromNoTwoOK` puts no promise on either word of a two-word unit of its cell, so the access
unit of a piece at a promise's word is a single word.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A two-word unit of a component of a laid-out or array cell type is a two-word unit of the
cell (`TwoAtT`). -/
theorem twoAtT_of_comp {T U : Ty} {o jj : Nat} {us : List Acc} (h1 : AtOff T o U)
    (hus : accs U = some us) (hj : TwoAt us jj)
    (hT : (∃ L, accs T = some L) ∨ ∃ N e, T = .array (.lit N) e) : TwoAtT T (o + jj) := by
  rcases hT with ⟨L, hL⟩ | ⟨N, e, rfl⟩
  · obtain ⟨pre, post, eL, hn⟩ := AtOff_embed h1 hL hus
    have h2 : TwoAt L (o + jj) := by
      have := TwoAt_embed (pre := pre) (post := post) hj
      rw [← eL, hn] at this
      exact this
    exact ⟨0, T, L, o + jj, Or.inl ⟨rfl, rfl, by rw [hL]; exact fun h => by cases h⟩, hL, h2,
      (Nat.zero_add _).symm⟩
  · rcases AtOff_arr_elem h1 rfl with hU | ⟨ue, j', o'', hue, hj', ho, hat⟩
    · subst hU
      simp [accs] at hus
    · obtain ⟨pre, post, eL, hn⟩ := AtOff_embed hat hue hus
      have h2 : TwoAt ue (o'' + jj) := by
        have := TwoAt_embed (pre := pre) (post := post) hj
        rw [← eL, hn] at this
        exact this
      exact ⟨j' * nWords ue, e, ue, o'' + jj, Or.inr ⟨N, ue, j', rfl, hue, hj', rfl⟩, hue, h2,
        by rw [ho, Nat.add_assoc]⟩

#print axioms twoAtT_of_comp

/-- **The access unit at a word with no two-word unit around it is that word alone.** -/
theorem inAcc_single {T S : Ty} {b o' : Nat} {us : List Acc} {i : Nat}
    (hat : AtOff T b S) (hus : accs S = some us) (hio : InAcc us i o')
    (hT : (∃ L, accs T = some L) ∨ ∃ N e, T = .array (.lit N) e)
    (hno : ∀ q, TwoAtT T q → b + o' ≠ q ∧ b + o' ≠ q + 1) :
    ∀ o'', InAcc us i o'' → o'' = o' := by
  intro o'' h2
  obtain ⟨a1, a2⟩ := hio
  obtain ⟨b1, b2⟩ := h2
  cases hu : us[i]? with
  | none =>
      have hle : us.length ≤ i := List.getElem?_eq_none_iff.1 hu
      rw [List.take_of_length_le hle] at a1
      rw [List.take_of_length_le (Nat.le_succ_of_le hle)] at a2
      exact absurd (Nat.lt_of_le_of_lt a1 a2) (Nat.lt_irrefl _)
  | some u =>
      have e := nWords_take_succ hu
      cases u with
      | one =>
          simp only [Acc.size] at e
          omega
      | two =>
          have htw : TwoAt us (nWords (us.take i)) := ⟨i, hu, rfl⟩
          have hq := hno _ (twoAtT_of_comp hat hus htw hT)
          simp only [Acc.size] at e
          omega

#print axioms inAcc_single

end TermOverCrW
