/-
**A literal held tail follows the output extern** (under `heldRetOk`
accepting a literal only after `print` with its one index): at every
`TailOf` a body passing `heldRetOk` of the shape `let x = call g is … in
ret k`, `g` is `print` and `is` has one index. This is the premise `hlitP`
of `mainCallWSF_ofPlaceOKHV` (x86-64 `HeldPostX`, AArch64 `HeldPostA`),
from `main`'s body passing `heldRetOk` (`mainRetOk`).

- `hlitP_of_heldRetOk`: at a body passing `heldRetOk`;
- `hlitP_of_mainRetOk`: at `main`'s body of a program passing `mainRetOk`.
-/
import Spike.Lib.Src.CallOrder2

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm

/-- **A literal held tail of a `heldRetOk` body follows `print` with one
index** (induction on `TailOf`: `heldRetOk` descends through `let`s,
`split`s, `unpack`s and both branches of an `ifeq`, a `ret` after a `let`
having no tail but itself). -/
theorem hlitP_of_heldRetOk {x g : String} {is : List String} {a : At} {ts : List Ty} {k : Nat} {e : Expr}
    (ht : TailOf (.let_ x (.call g is a ts) (.ret (.lit k))) e) (h : Scc.Lower.heldRetOk e = true) :
    g = "print" ∧ is.length = 1 := by
  induction ht with
  | refl =>
    simp only [Scc.Lower.heldRetOk, Bool.and_eq_true, beq_iff_eq] at h
    exact h
  | let_ y op ht ih =>
    rename_i e
    cases e with
    | ret b => cases ht
    | _ => cases op <;> simp only [Scc.Lower.heldRetOk] at h <;> exact ih h
  | split _ _ _ _ ih => exact ih (by simpa [Scc.Lower.heldRetOk] using h)
  | unpack _ _ _ _ ih => exact ih (by simpa [Scc.Lower.heldRetOk] using h)
  | unpackT => simp [Scc.Lower.heldRetOk] at h
  | yes _ _ _ _ ih =>
    simp only [Scc.Lower.heldRetOk, Bool.and_eq_true] at h
    exact ih h.1
  | no _ _ _ _ ih =>
    simp only [Scc.Lower.heldRetOk, Bool.and_eq_true] at h
    exact ih h.2

/-- **`hlitP` at `main`'s body** (`hlitP_of_heldRetOk` from `mainRetOk`). -/
theorem hlitP_of_mainRetOk {p : Prog} (hm : Scc.Lower.mainRetOk p = true) {d : Decl}
    (hd : p.find? (·.name == "main") = some d) :
    ∀ x g is a ts k, TailOf (.let_ x (.call g is a ts) (.ret (.lit k))) d.body → g = "print" ∧ is.length = 1 :=
  fun _ _ _ _ _ _ ht => hlitP_of_heldRetOk ht (by simpa [Scc.Lower.mainRetOk, hd] using hm)

end Spike.Lib.LowerNode

/-- info: 'Spike.Lib.LowerNode.hlitP_of_heldRetOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.hlitP_of_heldRetOk

/-- info: 'Spike.Lib.LowerNode.hlitP_of_mainRetOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.hlitP_of_mainRetOk
