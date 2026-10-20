/-
**Release splits that give the write set along**. ISA-neutral; a companion of
`EnvG/Split.lean`.

- `Perm.leaveD`: what is left of a permission after `Perm.take δ`, without
  the write set when the share taken is positive (`leaveD_op_take` exact).
- `Res.shareKeepD`: the kept part of `Res.shareGive L x δ` with `Perm.leaveD`
  at `x` (`Res.shareKeepD_op_shareGive` exact).
- `Plan.Split.shareD x L δ hδ`: as `Plan.Split.share`, but a positive share
  takes the write set of `x` and the kept part has none. Used by the CAS
  lock's release (`CasSmoke.lockSplit`); see `EnvG/CasRelease.lean` for why
  `Post` needs it.
- `Res.share2Give`/`Res.share2Keep`, `Plan.Split.share2D`: `shareD` with a
  second, clamped location (moved unchanged from `EnvG/X64SpinRelease.lean`).
  Used by the x64 xchg lock's release (`X64Spin.xlockSplit`).
-/
import Kraken.Promising.SLR.EnvG.Split

/-! ## A share that takes the write set along -/

namespace Kraken.Promising.SLR.Perm

/-- What is left of `a` after `take δ`, **without the write set** when the
share taken is positive (then `take δ` carries it). -/
def leaveD (a : Perm) (δ : Rat) : Perm where
  q := a.q - a.clampQ δ
  X p := a.clampQ δ = 0 ∧ 0 < a.q - a.clampQ δ ∧ a.X p
  nonneg := by have := a.clampQ_le δ; grind
  zero h _ hp := by have := hp.2.1; grind

theorem leaveD_op_take (a : Perm) (δ : Rat) : (a.leaveD δ).op (a.take δ) = a := by
  apply ext
  · simp only [op, leaveD, take]; grind
  · funext p
    simp only [op, leaveD, take]
    apply propext
    constructor
    · rintro (⟨-, -, h⟩ | ⟨-, h⟩) <;> exact h
    · intro h
      have hq : 0 < a.q := by
        have := a.nonneg
        by_cases h' : 0 < a.q
        · exact h'
        · exact absurd h (a.zero (by grind) p)
      have := a.clampQ_nonneg δ
      by_cases hc : 0 < a.clampQ δ
      · exact .inr ⟨hc, h⟩
      · exact .inl ⟨by grind, by grind, h⟩

theorem leaveD_q_pos (a : Perm) {δ : Rat} (hq : 0 < a.q) (hδ : δ < a.q) : 0 < (a.leaveD δ).q := by
  simp only [leaveD, clampQ]; grind

end Kraken.Promising.SLR.Perm

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

/-- The kept part of `Res.shareGive L x δ`: everything outside `L`, the rest
of `x` without its write set when the share given is positive. -/
def Res.shareKeepD (L : List Loc) (x : Loc) (δ : Rat) (r : Res) : Res :=
  ⟨fun y => if y = x then (r.wr x).leaveD δ else if y ∈ L then Perm.unit else r.wr y,
   fun y ι => if y ∈ L then 0 else r.acq y ι⟩

theorem Res.shareKeepD_op_shareGive (L : List Loc) (x : Loc) (δ : Rat) (r : Res) :
    (Res.shareKeepD L x δ r).op (Res.shareGive L x δ r) = r := by
  apply Res.ext
  · funext y
    simp only [Res.op, Res.shareKeepD, Res.shareGive]
    by_cases hy : y = x
    · subst hy; simp only [↓reduceIte]; exact Perm.leaveD_op_take _ _
    · simp only [hy, ↓reduceIte]
      split
      · exact Perm.unit_op _
      · exact Perm.op_unit _
  · funext y ι
    simp only [Res.op, Res.shareKeepD, Res.shareGive]
    split <;> omega

/-- **The share split, write set given along** at `x`: as `Plan.Split.share`
(`EnvG/Split.lean`), but a positive share takes the write set of `x` and the
kept part has none. -/
def Plan.Split.shareD (x : Loc) (L : List Loc) (δ : Prop → Res → Rat)
    (hδ : ∀ cl r, 0 < (r.wr x).q → δ cl r < (r.wr x).q) : Plan.Split x where
  give cl r := Res.shareGive L x (δ cl r) r
  keep cl r := Res.shareKeepD L x (δ cl r) r
  op_eq cl r := Res.shareKeepD_op_shareGive L x (δ cl r) r
  pos cl r hq := by
    simp only [Res.shareKeepD, ↓reduceIte]
    exact Perm.leaveD_q_pos _ hq (hδ cl r hq)

/-! ## A split with a second, clamped location -/

/-- The given part: a share `δ` of `x`, a share `ε` of `y`, and the other
locations of `L` whole. -/
def Res.share2Give (L : List Loc) (x : Loc) (δ : Rat) (y : Loc) (ε : Rat) (r : Res) : Res :=
  ⟨fun z => if z = x then (r.wr x).take δ else if z = y then (r.wr y).take ε else if z ∈ L then r.wr z
    else Perm.unit,
   fun z ι => if z ∈ L then r.acq z ι else 0⟩

/-- The kept part: the rest of `x` (without its write set when a positive
share is given), the rest of `y`, everything outside `L`. -/
def Res.share2Keep (L : List Loc) (x : Loc) (δ : Rat) (y : Loc) (ε : Rat) (r : Res) : Res :=
  ⟨fun z => if z = x then (r.wr x).leaveD δ else if z = y then (r.wr y).leave ε else if z ∈ L then Perm.unit
    else r.wr z,
   fun z ι => if z ∈ L then 0 else r.acq z ι⟩

theorem Res.share2Keep_op_share2Give (L : List Loc) (x : Loc) (δ : Rat) (y : Loc) (ε : Rat) (r : Res) :
    (Res.share2Keep L x δ y ε r).op (Res.share2Give L x δ y ε r) = r := by
  apply Res.ext
  · funext z
    simp only [Res.op, Res.share2Keep, Res.share2Give]
    by_cases hx : z = x
    · subst hx; simp only [↓reduceIte]; exact Perm.leaveD_op_take _ _
    · by_cases hy : z = y
      · subst hy; simp only [hx, ↓reduceIte]; exact Perm.leave_op_take _ _
      · simp only [hx, hy, ↓reduceIte]
        split
        · exact Perm.unit_op _
        · exact Perm.op_unit _
  · funext z ι
    simp only [Res.op, Res.share2Keep, Res.share2Give]
    split <;> omega

theorem Res.share2Give_wr_ne {L : List Loc} {x y z : Loc} {δ ε : Rat} {r : Res} (hx : z ≠ x) (hy : z ≠ y)
    (hL : z ∈ L) : (Res.share2Give L x δ y ε r).wr z = r.wr z := by
  simp only [Res.share2Give, hx, hy, hL, ↓reduceIte]

theorem Res.share2Give_wr_y {L : List Loc} {x y : Loc} {δ ε : Rat} {r : Res} (hx : y ≠ x) :
    (Res.share2Give L x δ y ε r).wr y = (r.wr y).take ε := by
  simp only [Res.share2Give, hx, ↓reduceIte]

theorem Res.share2Give_wr_self {L : List Loc} {x y : Loc} {δ ε : Rat} {r : Res} :
    (Res.share2Give L x δ y ε r).wr x = (r.wr x).take δ := by
  simp only [Res.share2Give, ↓reduceIte]

/-- **The two-share split** at `x`: `shareD` (`EnvG/CasRelease.lean`) and a
clamped share `ε cl r` of a second location `y`. -/
def Plan.Split.share2D (x : Loc) (L : List Loc) (δ : Prop → Res → Rat)
    (hδ : ∀ cl r, 0 < (r.wr x).q → δ cl r < (r.wr x).q) (y : Loc) (ε : Prop → Res → Rat) : Plan.Split x where
  give cl r := Res.share2Give L x (δ cl r) y (ε cl r) r
  keep cl r := Res.share2Keep L x (δ cl r) y (ε cl r) r
  op_eq cl r := Res.share2Keep_op_share2Give L x (δ cl r) y (ε cl r) r
  pos cl r hq := by
    simp only [Res.share2Keep, ↓reduceIte]
    exact Perm.leaveD_q_pos _ hq (hδ cl r hq)

end Kraken.Promising.SLR.EnvG
