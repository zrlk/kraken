/-
**Release splits: whole locations plus a share**. The generic library for building a
`Plan.Split` (`EnvG/State.lean`) that gives away part of a permission, e.g. a
lock release paying SLR's `Bad` disjunct with part of its own lock share.
ISA-neutral.

- `Perm.take`/`Perm.leave`: a share `δ` of a permission (clamped to
  `[0, q]`) and the rest, both with the full write set when positive;
  `leave_op_take` is exact.
- `Res.shareGive`/`Res.shareKeep`: the whole locations `L` plus a share `δ`
  of `x`; the split is exact (`Res.shareKeep_op_shareGive`) with no `x ∉ L`
  hypothesis.
- `Plan.Split.share x L δ hδ`: the split at `x` for a share `δ cl r` below
  the thread's fraction (so a positive share stays: `Plan.Split.pos`). The
  share may depend on the clean-erasure knowledge `cl` and the resource `r`.

Splits are for store releases only: a release RMW's plan entry must be whole
(`Plan.Whole`, required by `RmwOk`; phase-1 limit).
-/
import Kraken.Promising.SLR.EnvG.Plan

/-! ## Shares of a permission -/

namespace Kraken.Promising.SLR.Perm

/-- `δ` clamped to `[0, q]`. -/
def clampQ (a : Perm) (δ : Rat) : Rat := max 0 (min δ a.q)

theorem clampQ_nonneg (a : Perm) (δ : Rat) : 0 ≤ a.clampQ δ := by
  unfold clampQ; grind

theorem clampQ_le (a : Perm) (δ : Rat) : a.clampQ δ ≤ a.q := by
  have := a.nonneg; unfold clampQ; grind

/-- A share `δ` of `a` (clamped), with `a`'s write set when positive. -/
def take (a : Perm) (δ : Rat) : Perm where
  q := a.clampQ δ
  X p := 0 < a.clampQ δ ∧ a.X p
  nonneg := a.clampQ_nonneg δ
  zero h _ hp := by have := hp.1; grind

/-- What is left of `a` after `take δ`. -/
def leave (a : Perm) (δ : Rat) : Perm where
  q := a.q - a.clampQ δ
  X p := 0 < a.q - a.clampQ δ ∧ a.X p
  nonneg := by have := a.clampQ_le δ; grind
  zero h _ hp := by have := hp.1; grind

theorem leave_op_take (a : Perm) (δ : Rat) : (a.leave δ).op (a.take δ) = a := by
  apply ext
  · simp only [op, leave, take]; grind
  · funext p
    simp only [op, leave, take]
    apply propext
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    · intro h
      have hq : 0 < a.q := by
        have := a.nonneg
        by_cases h' : 0 < a.q
        · exact h'
        · exact absurd h (a.zero (by grind) p)
      have := a.clampQ_nonneg δ
      by_cases hc : 0 < a.clampQ δ
      · exact .inr ⟨hc, h⟩
      · exact .inl ⟨by grind, h⟩

theorem leave_q_pos (a : Perm) {δ : Rat} (hq : 0 < a.q) (hδ : δ < a.q) : 0 < (a.leave δ).q := by
  simp only [leave, clampQ]; grind

theorem take_q_of (a : Perm) {δ : Rat} (h0 : 0 ≤ δ) (hδ : δ ≤ a.q) : (a.take δ).q = δ := by
  simp only [take, clampQ]; grind

end Kraken.Promising.SLR.Perm

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

/-! ## Whole locations plus a share -/

/-- The given part: the locations `L` whole, a share `δ` of `x`. -/
def Res.shareGive (L : List Loc) (x : Loc) (δ : Rat) (r : Res) : Res :=
  ⟨fun y => if y = x then (r.wr x).take δ else if y ∈ L then r.wr y else Perm.unit,
   fun y ι => if y ∈ L then r.acq y ι else 0⟩

/-- The kept part: everything outside `L`, the rest of `x`. -/
def Res.shareKeep (L : List Loc) (x : Loc) (δ : Rat) (r : Res) : Res :=
  ⟨fun y => if y = x then (r.wr x).leave δ else if y ∈ L then Perm.unit else r.wr y,
   fun y ι => if y ∈ L then 0 else r.acq y ι⟩

theorem Res.shareKeep_op_shareGive (L : List Loc) (x : Loc) (δ : Rat) (r : Res) :
    (Res.shareKeep L x δ r).op (Res.shareGive L x δ r) = r := by
  apply Res.ext
  · funext y
    simp only [Res.op, Res.shareKeep, Res.shareGive]
    by_cases hy : y = x
    · subst hy; simp only [↓reduceIte]; exact Perm.leave_op_take _ _
    · simp only [hy, ↓reduceIte]
      split
      · exact Perm.unit_op _
      · exact Perm.op_unit _
  · funext y ι
    simp only [Res.op, Res.shareKeep, Res.shareGive]
    split <;> omega

theorem Res.shareGive_wr_ne {L : List Loc} {x y : Loc} {δ : Rat} {r : Res} (hy : y ≠ x) (hL : y ∈ L) :
    (Res.shareGive L x δ r).wr y = r.wr y := by
  simp only [Res.shareGive, hy, hL, ↓reduceIte]

theorem Res.shareGive_wr_self {L : List Loc} {x : Loc} {δ : Rat} {r : Res} :
    (Res.shareGive L x δ r).wr x = (r.wr x).take δ := by
  simp only [Res.shareGive, ↓reduceIte]

/-- **The share split** at `x`: whole locations `L` and a share `δ cl r` of
`x`, below the thread's fraction (so a positive share stays). -/
def Plan.Split.share (x : Loc) (L : List Loc) (δ : Prop → Res → Rat)
    (hδ : ∀ cl r, 0 < (r.wr x).q → δ cl r < (r.wr x).q) : Plan.Split x where
  give cl r := Res.shareGive L x (δ cl r) r
  keep cl r := Res.shareKeep L x (δ cl r) r
  op_eq cl r := Res.shareKeep_op_shareGive L x (δ cl r) r
  pos cl r hq := by
    simp only [Res.shareKeep, ↓reduceIte]
    exact Perm.leave_q_pos _ hq (hδ cl r hq)

end Kraken.Promising.SLR.EnvG

/-! ## Smoke tests -/

namespace Kraken.Promising.SLR.EnvG

/-- A concrete split plan: a release of `0` to `0x10` gives `0x20` whole and
half of its share of `0x10`. -/
def halfPlan : Plan :=
  ⟨[{ loc := ⟨0x10, 4⟩, val := some 0, gives := [],
      split := some (Plan.Split.share ⟨0x10, 4⟩ [⟨0x20, 4⟩] (fun _ r => (r.wr ⟨0x10, 4⟩).q / 2)
        fun _ r hq => by grind) }]⟩

/-- `Plan.Valid` of a split plan is still checked by `decide`. -/
example : halfPlan.Valid := by decide

/-- A split release is not whole. -/
example : ¬ halfPlan.Whole ⟨0x10, 4⟩ 0 := fun h => by
  have := h _ rfl
  simp at this

end Kraken.Promising.SLR.EnvG
