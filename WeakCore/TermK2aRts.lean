import WeakCore.TermPtrRts

/-! # TermK2aRts (K-2a block B helper): `RtsSub`, the rts-tracking `LblSub`

Every label a word of `ws'` names is named by a word of `ws` of no larger `rts`.  The structural
lemmas of `TermPtrRts.pubWords_lblSub`, with `rts` carried. -/

namespace TermK2a
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermPtrRts
open WeakMem (Msg Memory Address Ts AllocLabel)

/-- Every label a word of `ws'` names is named by a word of `ws` of no larger `rts`. -/
def RtsSub (ws' ws : List Word) : Prop :=
  ∀ w ∈ ws', ∀ l, Names l w → ∃ w0 ∈ ws, Names l w0 ∧ w0.rts ≤ w.rts

theorem rtsSub_refl (ws : List Word) : RtsSub ws ws := fun w hw _ hn => ⟨w, hw, hn, Nat.le_refl _⟩

theorem rtsSub_nil (ws : List Word) : RtsSub [] ws := fun _ hw => by cases hw

theorem rtsSub_trans {a b c : List Word} (h1 : RtsSub a b) (h2 : RtsSub b c) : RtsSub a c := by
  intro w hw l hn
  obtain ⟨w1, hw1, hn1, hr1⟩ := h1 w hw l hn
  obtain ⟨w2, hw2, hn2, hr2⟩ := h2 w1 hw1 l hn1
  exact ⟨w2, hw2, hn2, Nat.le_trans hr2 hr1⟩

theorem rtsSub_of_sub {a b : List Word} (h : ∀ w ∈ a, w ∈ b) : RtsSub a b :=
  fun w hw _ hn => ⟨w, h w hw, hn, Nat.le_refl _⟩

theorem rtsSub_append {a b c : List Word} (h1 : RtsSub a c) (h2 : RtsSub b c) : RtsSub (a ++ b) c := by
  intro w hw
  rcases List.mem_append.1 hw with hw | hw
  · exact h1 w hw
  · exact h2 w hw

theorem rtsSub_take (ws : List Word) (n : Nat) : RtsSub (ws.take n) ws :=
  rtsSub_of_sub (fun _ h => List.mem_of_mem_take h)

theorem rtsSub_drop (ws : List Word) (n : Nat) : RtsSub (ws.drop n) ws :=
  rtsSub_of_sub (fun _ h => List.mem_of_mem_drop h)

/-- `RtsSub` forgets `rts` to `LblSub`. -/
theorem RtsSub.lbl {a b : List Word} (h : RtsSub a b) : LblSub a b := by
  intro w hw l hn
  obtain ⟨w0, h0, hn0, -⟩ := h w hw l hn
  exact ⟨w0, h0, hn0⟩

/-- A null word names nothing. -/
theorem not_names_null (l : AllocLabel) : ¬ Names l (cst .null) := by
  rintro ⟨a', g', hv', -⟩
  have e : (cst .null).val = WeakMem.Val.null := rfl
  rw [e] at hv'; cases hv'

/-- A decoded arm payload names only labels of the encoded words, at their `rts` (the niche
decode re-encodes the slot keeping the word's `rts`). -/
theorem decodeArm_rtsSub {tr : Tier} {as : List Ty} {ws p : List Word} {j : Nat}
    (h : decodeArm tr as ws = some (j, p)) : RtsSub p ws := by
  unfold decodeArm at h
  split at h
  · rename_i w
    split at h
    · rename_i a g hv
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro w' hw' l hn
      simp only [List.mem_singleton] at hw'
      subst hw'
      obtain ⟨a', g', hv', hl⟩ := hn
      simp only at hv'
      cases hv'
      exact ⟨w, List.mem_singleton_self _, ⟨a, g, hv, hl⟩, Nat.le_refl _⟩
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨arm, -, h⟩ := h
      split at h <;> simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
      · obtain ⟨-, rfl⟩ := h; exact rtsSub_nil _
      · obtain ⟨-, rfl⟩ := h
        intro w' hw' l hn
        simp only [List.mem_singleton] at hw'
        subst hw'
        exact absurd hn (not_names_null l)
    · cases h
  · rename_i t w
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨arm, -, h⟩ := h
      split at h <;> simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      · obtain ⟨-, rfl⟩ := h; exact rtsSub_nil _
      · obtain ⟨-, rfl⟩ := h
        exact rtsSub_of_sub (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp)
    · cases h
  · cases h

/-- Counted words name only labels of the value's words, at no smaller `rts`. -/
theorem pubWords_rtsSub : ∀ (t : Ty),
    (∀ ws, RtsSub (pubWords t ws) ws) ∧ (∀ j p, RtsSub (pubArm t j p) p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only
        split
        · exact rtsSub_refl _
        · split
          · exact rtsSub_append (rtsSub_trans ((iha).1 _) (rtsSub_take _ _))
              (rtsSub_trans ((ihb).1 _) (rtsSub_drop _ _))
          · exact rtsSub_nil _
      · rw [pubArm.eq_def]; simp only
        rw [pubWords.eq_def]; simp only
        split
        · exact rtsSub_refl _
        · split
          · exact rtsSub_append (rtsSub_trans ((iha).1 _) (rtsSub_take _ _))
              (rtsSub_trans ((ihb).1 _) (rtsSub_drop _ _))
          · exact rtsSub_nil _
  | sum a b iha ihb =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only
        split
        · exact rtsSub_refl _
        · split
          · exact rtsSub_refl _
          · split
            · rename_i j p hd
              split
              · exact rtsSub_trans ((iha).2 _ _) (decodeArm_rtsSub hd)
              · exact rtsSub_trans ((ihb).2 _ _) (decodeArm_rtsSub hd)
            · exact rtsSub_nil _
      · rw [pubArm.eq_def]; simp only
        split
        · exact (iha).2 _ _
        · exact (ihb).2 _ _
  | refine t ψ ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact rtsSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | iall t ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact rtsSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | iex t ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact rtsSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | mu t ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact rtsSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | tex κ t ih =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only; split
        · exact rtsSub_refl _
        · exact ih.1 _
      · rw [pubArm.eq_def]; exact ih.2 _ _
  | array i e ih =>
      have hA : ∀ ws, RtsSub (pubWords (.array i e) ws) ws := by
        intro ws
        rw [pubWords.eq_def]; simp only; split
        · exact rtsSub_refl _
        · exact rtsSub_nil _
      exact ⟨hA, fun j p => by rw [pubArm.eq_def]; exact hA p⟩
  | _ =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      all_goals first
        | (rw [pubWords.eq_def]; simp only; split
           · exact rtsSub_refl _
           · exact rtsSub_nil _)
        | (rw [pubArm.eq_def]; simp only; rw [pubWords.eq_def]; simp only; split
           · exact rtsSub_refl _
           · exact rtsSub_nil _)

#print axioms rtsSub_trans
#print axioms decodeArm_rtsSub
#print axioms pubWords_rtsSub

end TermK2a
