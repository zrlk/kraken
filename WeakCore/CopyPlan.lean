import WeakCore.Frame
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! **copyPlan** (L1): level `d` of the stack uses column `c < M` (`M` = stack depth + 2) of thread `i`'s
fresh progression, rows `l` (the label being copied / moved), above a per-level base `b` (≥ every threshold
in play: the top anchor's `OwnFreshZ` bound, `η′`'s cofinite-fresh bound, and the previous levels' bases).
Distinct (base, row, column) triples with the same column residue give distinct progression indices. -/

def colIdx (M b l c : Nat) : Nat := M * (b + l) + c

theorem colIdx_col {M b₁ b₂ l₁ l₂ c₁ c₂ : Nat} (h₁ : c₁ < M) (h₂ : c₂ < M)
    (e : colIdx M b₁ l₁ c₁ = colIdx M b₂ l₂ c₂) : c₁ = c₂ ∧ b₁ + l₁ = b₂ + l₂ := by
  unfold colIdx at e
  have m1 : (M * (b₁ + l₁) + c₁) % M = c₁ := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h₁
  have m2 : (M * (b₂ + l₂) + c₂) % M = c₂ := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h₂
  have hc : c₁ = c₂ := by rw [← m1, ← m2, e]
  subst hc
  refine ⟨rfl, Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel e)⟩

theorem colIdx_inj_row {M b l₁ l₂ c : Nat} (h : c < M) (e : colIdx M b l₁ c = colIdx M b l₂ c) : l₁ = l₂ := by
  have := (colIdx_col h h e).2; omega

theorem colIdx_ge {M b l c : Nat} (hM : 0 < M) : b ≤ colIdx M b l c := by
  unfold colIdx
  have : b + l ≤ M * (b + l) := Nat.le_mul_of_pos_left _ hM
  omega

theorem freshLabel_inj {base n i k₁ k₂ : Nat} (hn : 0 < n) (e : freshLabel base n i k₁ = freshLabel base n i k₂) :
    k₁ = k₂ := by
  unfold freshLabel at e
  exact Nat.eq_of_mul_eq_mul_left hn (Nat.add_left_cancel e)

/-- The copy / move label of row `l` at column `c`, base `b`. -/
def planLbl (base n i M b l c : Nat) : WeakMem.AllocLabel := freshLabel base n i (colIdx M b l c)

theorem planLbl_inj {base n i M b₁ b₂ l₁ l₂ c₁ c₂ : Nat} (hn : 0 < n) (h₁ : c₁ < M) (h₂ : c₂ < M)
    (e : planLbl base n i M b₁ l₁ c₁ = planLbl base n i M b₂ l₂ c₂) : c₁ = c₂ ∧ b₁ + l₁ = b₂ + l₂ :=
  colIdx_col h₁ h₂ (freshLabel_inj hn e)

theorem planLbl_tail {base n i M b l c N : Nat} (hM : 0 < M) (hb : N ≤ b) :
    ∃ k, N ≤ k ∧ planLbl base n i M b l c = freshLabel base n i k :=
  ⟨colIdx M b l c, Nat.le_trans hb (colIdx_ge hM), rfl⟩

end TermSound.Flat
