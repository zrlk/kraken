/-
**Register-view arrays that change in two slots**
(ISA-neutral, architecture-neutral, program-independent).

In the spin loops of the ticket locks (`LiveCertBoundedTicket`,
`LiveCertBoundedTicketX64`) only two register views change: the loaded
register's (slot `k₁`) and the flags' (slot `k₂`). `RegS k₁ k₂ base a`: `a`
agrees with `base` outside those slots. After a load into `k₁` and a compare
into `k₂`, two such arrays are dominated (`ArrLe`) as soon as the two new
views are (`RegS.arrLe`), and before the compare they agree up to `≤`
outside `k₂` (`RegS.le`).
-/
import Kraken.Promising.LiveCertCut

namespace Kraken.Promising.Live.CertCut

theorem get_set (a : Array View) (i j : Nat) (ν : View) :
    (a.setIfInBounds i ν)[j]! = if i = j ∧ j < a.size then ν else a[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hb : i < a.size
    · simp [hb]
    · simp [hb]
  · simp [hij]

theorem get_oob (a : Array View) (j : Nat) (h : a.size ≤ j) : (a[j]! : View) = 0 := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]

/-- Register-view arrays that agree with `base` outside slots `k₁` and `k₂`. -/
def RegS (k₁ k₂ : Nat) (base a : Array View) : Prop :=
  a.size = base.size ∧ ∀ i, i ≠ k₁ → i ≠ k₂ → (a[i]! : View) = base[i]!

theorem RegS.refl (k₁ k₂ : Nat) (a : Array View) : RegS k₁ k₂ a a := ⟨rfl, fun _ _ _ => rfl⟩

theorem RegS.set {k₁ k₂ : Nat} {base a : Array View} (h : RegS k₁ k₂ base a) {i : Nat} (hi : i = k₁ ∨ i = k₂)
    (ν : View) : RegS k₁ k₂ base (a.setIfInBounds i ν) :=
  ⟨by simp [h.1], fun j h1 h2 => by
    rw [get_set, ite_eq_right (by rintro ⟨rfl, -⟩; rcases hi with rfl | rfl <;> simp_all)]
    exact h.2 j h1 h2⟩

/-- Two `RegS` arrays with slot `k₁` set to `x ≤ y` agree up to `≤` outside
slot `k₂`. -/
theorem RegS.le {k₁ k₂ : Nat} {base a b : Array View} (ha : RegS k₁ k₂ base a) (hb : RegS k₁ k₂ base b)
    {x y : View} (hxy : x ≤ y) (j : Nat) (hj : j ≠ k₂) :
    ((a.setIfInBounds k₁ x)[j]! : View) ≤ (b.setIfInBounds k₁ y)[j]! := by
  by_cases hin : j < base.size
  · rw [get_set, get_set, ha.1, hb.1]
    by_cases e : j = k₁
    · subst e; simp only [hin, and_self, ↓reduceIte]; exact hxy
    · rw [ite_eq_right (by rintro ⟨h, -⟩; exact e h.symm), ite_eq_right (by rintro ⟨h, -⟩; exact e h.symm),
        ha.2 j e hj, hb.2 j e hj]
      exact Nat.le_refl _
  · rw [get_oob _ _ (by simp [ha.1]; omega)]; exact Nat.zero_le _

/-- **The register views after a load and a compare are dominated.** -/
theorem RegS.arrLe {k₁ k₂ : Nat} {base a b : Array View} (ha : RegS k₁ k₂ base a) (hb : RegS k₁ k₂ base b)
    {x y z w : View} (hxy : x ≤ y) (hzw : z ≤ w) :
    ArrLe ((a.setIfInBounds k₁ x).setIfInBounds k₂ z) ((b.setIfInBounds k₁ y).setIfInBounds k₂ w) := by
  refine ⟨by simp [ha.1, hb.1], fun j => ?_⟩
  by_cases hin : j < base.size
  · rw [get_set (a.setIfInBounds k₁ x) k₂ j z, get_set (b.setIfInBounds k₁ y) k₂ j w]
    simp only [Array.size_setIfInBounds, ha.1, hb.1]
    by_cases e : j = k₂
    · subst e; simp only [hin, and_self, ↓reduceIte]; exact hzw
    · rw [ite_eq_right (by rintro ⟨h, -⟩; exact e h.symm), ite_eq_right (by rintro ⟨h, -⟩; exact e h.symm)]
      exact ha.le hb hxy j e
  · rw [get_oob _ _ (by simp [ha.1]; omega)]; exact Nat.zero_le _

end Kraken.Promising.Live.CertCut
