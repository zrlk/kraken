/-
Generic splitting of resources (`SLR/Resources.lean`): a write permission
splits into two fractions that share its write set (`Perm.part`,
`Perm.part_op_part`), and a resource splits location-wise by a fraction
function (`Res.take`/`Res.leave`, `Res.leave_op_take`): `take f` holds the
fraction `f x` of every location `x` (no acquire ids), `leave f` the rest
(all acquire ids). A part of fraction `0` has an empty write set (the
`Perm.zero` invariant); a positive part keeps the whole write set.

Used by release rules that hand a part of the thread's resource to a
message's slots (`EvTree.eraseWPR_store_rel`'s `r' ⋅ R = r ⊎ {msg}`).
-/
import Kraken.Promising.SLR.Rmw

namespace Kraken.Promising.SLR

namespace Perm

/-- The fraction `q` of `a`, with `a`'s write set when `q ≠ 0`. -/
def part (a : Perm) (q : Rat) (h0 : 0 ≤ q) : Perm where
  q := q
  X p := q ≠ 0 ∧ a.X p
  nonneg := h0
  zero h _ hp := hp.1 h

@[simp] theorem part_q (a : Perm) (q : Rat) (h0 : 0 ≤ q) : (a.part q h0).q = q := rfl

theorem part_X (a : Perm) (q : Rat) (h0 : 0 ≤ q) (p : Val × Time) : (a.part q h0).X p ↔ q ≠ 0 ∧ a.X p :=
  Iff.rfl

/-- A positive part keeps the write set. -/
theorem part_X_pos (a : Perm) {q : Rat} (h0 : 0 ≤ q) (hq : 0 < q) (p : Val × Time) :
    (a.part q h0).X p ↔ a.X p := by
  have : q ≠ 0 := fun h => by rw [h] at hq; exact Rat.lt_irrefl hq
  simp [part_X, this]

/-- **A permission is the composition of two parts** with fractions summing
to its own. -/
theorem part_op_part (a : Perm) {q₁ q₂ : Rat} (h₁ : 0 ≤ q₁) (h₂ : 0 ≤ q₂) (hs : q₁ + q₂ = a.q) :
    (a.part q₁ h₁).op (a.part q₂ h₂) = a := by
  apply ext
  · exact hs
  · funext p
    simp only [op, part]
    apply propext
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    · intro h
      by_cases hq : q₁ = 0
      · refine .inr ⟨fun h0 => a.zero (by rw [← hs, hq, h0, Rat.add_zero]) p h, h⟩
      · exact .inl ⟨hq, h⟩

end Perm

namespace Res

/-- The fraction `f x` of every location `x` of `r` (with `r`'s write set
where positive), no acquire ids. -/
def take (r : Res) (f : Loc → Rat) (hf : ∀ x, 0 ≤ f x) : Res :=
  ⟨fun x => (r.wr x).part (f x) (hf x), fun _ _ => 0⟩

/-- What is left of `r` after `take f`: the fraction `q - f x` of every
location, all acquire ids. -/
def leave (r : Res) (f : Loc → Rat) (hf : ∀ x, f x ≤ (r.wr x).q) : Res :=
  ⟨fun x => (r.wr x).part ((r.wr x).q - f x) (by have := hf x; grind), r.acq⟩

@[simp] theorem take_q (r : Res) (f : Loc → Rat) (hf : ∀ x, 0 ≤ f x) (x : Loc) :
    ((r.take f hf).wr x).q = f x := rfl

@[simp] theorem leave_q (r : Res) (f : Loc → Rat) (hf : ∀ x, f x ≤ (r.wr x).q) (x : Loc) :
    ((r.leave f hf).wr x).q = (r.wr x).q - f x := rfl

@[simp] theorem take_acq (r : Res) (f : Loc → Rat) (hf : ∀ x, 0 ≤ f x) : (r.take f hf).acq = fun _ _ => 0 := rfl

@[simp] theorem leave_acq (r : Res) (f : Loc → Rat) (hf : ∀ x, f x ≤ (r.wr x).q) : (r.leave f hf).acq = r.acq :=
  rfl

theorem take_X (r : Res) (f : Loc → Rat) (hf : ∀ x, 0 ≤ f x) (x : Loc) (p : Val × Time) :
    ((r.take f hf).wr x).X p ↔ f x ≠ 0 ∧ (r.wr x).X p := Iff.rfl

theorem leave_X (r : Res) (f : Loc → Rat) (hf : ∀ x, f x ≤ (r.wr x).q) (x : Loc) (p : Val × Time) :
    ((r.leave f hf).wr x).X p ↔ (r.wr x).q - f x ≠ 0 ∧ (r.wr x).X p := Iff.rfl

/-- A positive taken fraction keeps the write set. -/
theorem take_X_pos (r : Res) (f : Loc → Rat) (hf : ∀ x, 0 ≤ f x) {x : Loc} (hx : 0 < f x) (p : Val × Time) :
    ((r.take f hf).wr x).X p ↔ (r.wr x).X p :=
  Perm.part_X_pos _ _ hx p

/-- A positive remaining fraction keeps the write set. -/
theorem leave_X_pos (r : Res) (f : Loc → Rat) (hf : ∀ x, f x ≤ (r.wr x).q) {x : Loc} (hx : f x < (r.wr x).q)
    (p : Val × Time) : ((r.leave f hf).wr x).X p ↔ (r.wr x).X p :=
  Perm.part_X_pos _ _ (by grind) p

/-- **`r = leave f ⋅ take f`.** -/
theorem leave_op_take (r : Res) (f : Loc → Rat) (hf0 : ∀ x, 0 ≤ f x) (hf : ∀ x, f x ≤ (r.wr x).q) :
    (r.leave f hf).op (r.take f hf0) = r := by
  apply ext
  · funext x
    exact Perm.part_op_part _ _ _ (by grind)
  · funext x ι
    simp [op, leave, take]

end Res

end Kraken.Promising.SLR
