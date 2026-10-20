import WeakCore.TermPredHold

/-! # TermPromAtFW: an own promise is skipped, or is the first write (O5)

At a non-visible unit, a non-`undef` own promise is in `PromAt`, unless the unit is
predicted and the promise is the unit's first write (the deliberate `AboveFW` exclusion).
-/

namespace TermPromAtFW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep
open WeakMem (Msg Memory Address Ts)

/-- **(O5)** A non-`undef` own promise at a non-visible unit is in `PromAt`, or it is the
unit's first write (and the unit is predicted). -/
theorem promAt_or_firstW {E : TEnv} {s : St} {a : Address} {t : Ts} {m : Msg}
    (hP : t ∈ s.promises) (hm : s.mem[t]? = some m) (hl : m.loc = a) (hv : m.val ≠ .undef)
    (hnv : ¬ VisU E a) : t ∈ PromAt E s a ∨ (PredU E a ∧ FirstW s.mem a t) := by
  classical
  unfold PromAt
  simp only [hnv, ↓reduceIte]
  by_cases hpu : PredU E a
  · rw [ite_eq_left hpu]
    obtain ⟨h, hf, hle⟩ := TermPredHold.firstW_ex t m hm hl hv
    rcases Nat.lt_or_ge h t with hlt | hge
    · exact Or.inl (List.mem_filter.2 ⟨List.mem_append_left _ hP, decide_eq_true ⟨h, hf, hlt⟩⟩)
    · have e : h = t := Nat.le_antisymm hle hge
      subst e
      exact Or.inr ⟨hpu, hf⟩
  · rw [ite_eq_right hpu]
    exact Or.inl (List.mem_append_left _ hP)

end TermPromAtFW
