/-! For the box variants: the Nat pairing `pr x m = 2^x * (2m+1)` is injective.
Core Lean only (no Mathlib). -/
namespace NatPair

def pr (x m : Nat) : Nat := 2 ^ x * (2 * m + 1)

theorem pr_succ (x m : Nat) : pr (x + 1) m = 2 * pr x m := by
  unfold pr; rw [Nat.pow_succ, Nat.mul_comm (2 ^ x) 2, Nat.mul_assoc]

theorem pr_zero (m : Nat) : pr 0 m = 2 * m + 1 := by
  unfold pr; simp

theorem pr_pos (x m : Nat) : 0 < pr x m := by
  unfold pr; exact Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.succ_pos _)

theorem pr_inj : ∀ {x m y n : Nat}, pr x m = pr y n → x = y ∧ m = n
  | 0, m, 0, n, h => by
      rw [pr_zero, pr_zero] at h; exact ⟨rfl, by omega⟩
  | 0, m, y + 1, n, h => by
      rw [pr_zero, pr_succ] at h; exact absurd h (by omega)
  | x + 1, m, 0, n, h => by
      rw [pr_zero, pr_succ] at h; exact absurd h (by omega)
  | x + 1, m, y + 1, n, h => by
      rw [pr_succ, pr_succ] at h
      have h' : pr x m = pr y n := by omega
      obtain ⟨e1, e2⟩ := pr_inj h'
      exact ⟨by rw [e1], e2⟩

theorem pr_inj_iff {x m y n : Nat} : pr x m = pr y n ↔ x = y ∧ m = n :=
  ⟨pr_inj, fun ⟨e1, e2⟩ => by rw [e1, e2]⟩

#print axioms pr_inj
#print axioms pr_inj_iff
end NatPair
