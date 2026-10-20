import WeakCore.TermBlkZ
import WeakCore.TermPiece

/-! # TermPieceCov: every unit of a closed laid-out type lies in a piece (O1) -/

namespace TermPieceCov
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPiece TermBlkZ

/-- The measure form of `piece_cover`. -/
theorem piece_coverM : ∀ (n : Nat) (T : Ty) {L : List Acc} {o : Nat}, skN T < n → Clo T → mg T = true →
    accs T = some L → o < nWords L →
    ∃ b S us, Piece T b S ∧ accs S = some us ∧ b ≤ o ∧ o < b + nWords us
  | 0, _, _, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, T, L, o, hn, hc, hm, hL, ho => by
    have leaf : Solid T → ∃ b S us, Piece T b S ∧ accs S = some us ∧ b ≤ o ∧ o < b + nWords us := by
      intro hS
      refine ⟨0, T, L, ⟨.here (Or.inl (by rw [hL]; exact Option.some_ne_none _)), hS, ?_⟩, hL, Nat.zero_le _,
        by omega⟩
      rw [wc_of_accs hL]
      intro e
      have e2 : nWords L = 0 := Option.some.inj e
      omega
    cases T with
    | prod a b =>
      simp only [skN] at hn
      simp only [mg, Bool.and_eq_true] at hm
      obtain ⟨hca, hcb⟩ := Clo_prod hc
      obtain ⟨ua, ub, hua, hub⟩ := accs_prod_some (by rw [hL]; exact Option.some_ne_none _)
      have hLe : L = ua ++ ub := by
        simp only [accs, hua, hub] at hL
        exact (Option.some.inj hL).symm
      subst hLe
      rw [TermSound.nWords_append] at ho
      by_cases h1 : o < nWords ua
      · obtain ⟨b1, S, us, hP, hus, h2, h3⟩ := piece_coverM n a (by omega) hca hm.1 hua h1
        exact ⟨b1, S, us, ⟨.fst hP.1, hP.2.1, hP.2.2⟩, hus, h2, h3⟩
      · obtain ⟨b1, S, us, hP, hus, h2, h3⟩ :=
          piece_coverM n b (o := o - nWords ua) (by omega) hcb hm.2 hub (by omega)
        exact ⟨nWords ua + b1, S, us, ⟨.snd hua hP.1, hP.2.1, hP.2.2⟩, hus, by omega, by omega⟩
    | mu s =>
      have hm0 := hm
      simp only [mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨hcU, haU, hat⟩ := mu_unfold_facts hc hm.1
      have hsk : skN (unfold1 (.mu s)) < n := by
        show skN (Ty.substT 0 (.mu s) s) < n
        rw [skN_substT s 0 _ hm.1]; simp only [skN] at hn; omega
      obtain ⟨b1, S, us, hP, hus, h2, h3⟩ :=
        piece_coverM n _ hsk hcU (mg_unfold1 hm0) (by rw [haU]; exact hL) ho
      exact ⟨b1, S, us, ⟨hat _ _ hP.1, hP.2.1, hP.2.2⟩, hus, h2, h3⟩
    | array i e => simp [accs] at hL
    | _ => exact leaf ⟨fun _ _ h => Ty.noConfusion h, fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩

/-- **(O1) Every unit of a closed guarded laid-out type lies in a piece.** -/
theorem piece_cover {T : Ty} {L : List Acc} {o : Nat} (hc : Clo T) (hm : mg T = true)
    (hL : accs T = some L) (ho : o < nWords L) :
    ∃ b S us, Piece T b S ∧ accs S = some us ∧ b ≤ o ∧ o < b + nWords us :=
  piece_coverM (skN T + 1) T (Nat.lt_succ_self _) hc hm hL ho

/-- **(O1, buffers)** The same for a buffer type `array (lit N) e`, at a unit below
`N` slots. -/
theorem piece_cover_arr {N : Nat} {e : Ty} {us : List Acc} {o : Nat} (hc : Clo e) (hm : mg e = true)
    (hus : accs e = some us) (ho : o < N * nWords us) :
    ∃ b S vs, Piece (.array (.lit N) e) b S ∧ accs S = some vs ∧ b ≤ o ∧ o < b + nWords vs := by
  have hpos : 0 < nWords us := by
    rcases Nat.eq_zero_or_pos (nWords us) with h | h
    · rw [h, Nat.mul_zero] at ho; exact absurd ho (Nat.not_lt_zero _)
    · exact h
  have hj : o / nWords us < N := (Nat.div_lt_iff_lt_mul hpos).2 ho
  have hr : o % nWords us < nWords us := Nat.mod_lt _ hpos
  obtain ⟨b1, S, vs, hP, hvs, h2, h3⟩ := piece_cover hc hm hus hr
  have hdm : o / nWords us * nWords us + o % nWords us = o := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod o (nWords us)
  refine ⟨o / nWords us * nWords us + b1, S, vs, ⟨.elem hus hj hP.1, hP.2.1, hP.2.2⟩, hvs, by omega, by omega⟩

end TermPieceCov
