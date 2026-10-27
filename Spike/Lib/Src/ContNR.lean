/-
**No bare `ret` right after a checked `+`, a saturating `-` or an `if`'s
`else`** (ISA-neutral): the walk facts `main`'s blocks need for their
states inside `W2` at no frames (`W2`'s `noRet` at `(ret k, [])`). The
blocks of `let x = a + b in e` (its pending store at `e`), of
`let x = a - b in e` (at `e`) and of `if a = b then y else n` (the `jmp` at
`n`) are at a continuation's node; `main`'s body passes `heldRetOk`, so on
every path a `ret` follows a call (`HeldTail`), never one of these.

- `ContNR`: at `t`, the continuation of a `+`, a `-` or an `if`'s `else` is
  no bare `ret`.
- `contNR_ret`, `contNR_of_heldRetOk`: at a bare `ret`; at a term passing
  `heldRetOk`.
- `contNR_of_tail`: at every term still to lower (`TailOf`) of a body
  passing `heldRetOk`.
- `contNR_tailAt2`: at every term of `TailAt2 p j`, the `j`th compiled
  block's body passing `heldRetOk`.
- `ContNR.qAdd`, `ContNR.qSub`, `ContNR.qIf`: the `hQ` of `addC2_ofQ`,
  `subC2_ofQ`, `ifC2_ofQ` at the guard `P → no bare ret`.
-/
import Spike.Lib.Src.Walk2Facts

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm

/-- **At `t`, no continuation of a checked `+`, a saturating `-` or an
`if`'s `else` is a bare `ret`.** -/
def ContNR (t : Expr) : Prop :=
  (∀ x a b e, t = .let_ x (.add a b) e → ∀ r, e ≠ .ret r) ∧
    (∀ x a b e, t = .let_ x (.sub a b) e → ∀ r, e ≠ .ret r) ∧
    (∀ a b y n, t = .ifeq a b y n → ∀ r, n ≠ .ret r)

/-- `ContNR` at a bare `ret`: it is none of the three. -/
theorem contNR_ret (a : At) : ContNR (.ret a) :=
  ⟨fun _ _ _ _ h => (nomatch h), fun _ _ _ _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩

/-- **`ContNR` at a term passing `heldRetOk`**: past a `+` or a `-` the
continuation passes it, so is no bare `ret`; so does an `if`'s `else`. -/
theorem contNR_of_heldRetOk {t : Expr} (h : Scc.Lower.heldRetOk t = true) : ContNR t := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x a b e rfl r rfl
    simp [Scc.Lower.heldRetOk] at h
  · rintro x a b e rfl r rfl
    simp [Scc.Lower.heldRetOk] at h
  · rintro a b y n rfl r rfl
    simp [Scc.Lower.heldRetOk] at h

/-- **`ContNR` at every term still to lower of a body passing
`heldRetOk`**: down a `let`, a pair split, an unpack or a branch the term
passes `heldRetOk`, but at a held tail `let x = call … in ret b`, whose
only term still to lower below it is the bare `ret b`. -/
theorem contNR_of_tail {t e : Expr} (ht : TailOf t e) (h : Scc.Lower.heldRetOk e = true) : ContNR t := by
  induction ht with
  | refl => exact contNR_of_heldRetOk h
  | let_ x op ht ih =>
    rename_i e'
    by_cases hc : Scc.Lower.heldRetOk e' = true
    · exact ih hc
    · -- the held tail: `e'` is a bare `ret`, the only term still to lower below it
      rw [Scc.Lower.heldRetOk.eq_def] at h
      split at h
      · rename_i heq
        obtain ⟨-, -, rfl⟩ := Expr.let_.inj heq
        cases ht with
        | refl => exact contNR_ret _
      · obtain ⟨-, -, rfl⟩ := Expr.let_.inj ‹_›
        exact absurd h hc
      all_goals first | (exfalso; simp_all) | cases h
  | split a x y ht ih => exact ih (by simpa [Scc.Lower.heldRetOk] using h)
  | unpack a i x ht ih => exact ih (by simpa [Scc.Lower.heldRetOk] using h)
  | unpackT a α x ht ih => simp [Scc.Lower.heldRetOk] at h
  | yes a b no ht ih => exact ih (by simp [Scc.Lower.heldRetOk] at h; exact h.1)
  | no a b yes ht ih => exact ih (by simp [Scc.Lower.heldRetOk] at h; exact h.2)

/-- **`ContNR` at every term of `TailAt2 p j`**, the `j`th compiled
block's body passing `heldRetOk` (`contNR_of_tail`). -/
theorem contNR_tailAt2 {p : Prog} {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (hok : Scc.Lower.heldRetOk d.body = true) {t : Expr} (ht : TailAt2 p j t) : ContNR t :=
  contNR_of_tail (ht d hd) hok

/-- **A guard `P → no bare ret` at a `+` and its continuation** (`addC2_ofQ`'s
`hQ` at `Q t := P → ∀ r, t ≠ .ret r`), from `ContNR` at the walk's terms. -/
theorem ContNR.qAdd {T : Expr → Prop} {P : Prop} (hT : ∀ t, T t → ContNR t) :
    ∀ x a b e, T (.let_ x (.add a b) e) →
      (P → ∀ r, Expr.let_ x (.add a b) e ≠ .ret r) ∧ (P → ∀ r, e ≠ .ret r) :=
  fun x a b e h => ⟨fun _ _ h => (nomatch h), fun _ => (hT _ h).1 x a b e rfl⟩

/-- **The guard at a `-` and its continuation** (`subC2_ofQ`'s `hQ`). -/
theorem ContNR.qSub {T : Expr → Prop} {P : Prop} (hT : ∀ t, T t → ContNR t) :
    ∀ x a b e, T (.let_ x (.sub a b) e) →
      (P → ∀ r, Expr.let_ x (.sub a b) e ≠ .ret r) ∧ (P → ∀ r, e ≠ .ret r) :=
  fun x a b e h => ⟨fun _ _ h => (nomatch h), fun _ => (hT _ h).2.1 x a b e rfl⟩

/-- **The guard at an `if` and its `else`** (`ifC2_ofQ`'s `hQ`). -/
theorem ContNR.qIf {T : Expr → Prop} {P : Prop} (hT : ∀ t, T t → ContNR t) :
    ∀ a b y n, T (.ifeq a b y n) → (P → ∀ r, Expr.ifeq a b y n ≠ .ret r) ∧ (P → ∀ r, n ≠ .ret r) :=
  fun a b y n h => ⟨fun _ _ h => (nomatch h), fun _ => (hT _ h).2.2 a b y n rfl⟩

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.
/-- info: 'Spike.Lib.LowerNode.contNR_of_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.contNR_of_tail

/-- info: 'Spike.Lib.LowerNode.contNR_tailAt2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.contNR_tailAt2
