import Scc.Lower.InvBody
import Scc.Lower.Split

/-!
# The split leaves `Accepted0` programs unchanged

The IR function of an `Accepted0` code block (`func0`) is one block of at
most `maxAdds0` = 508 `addChk`s (one unit each) and a `ret` of one word (two
units), with no parameters: 510 units, within `maxBlockLen` = 512.  So the
split pass (`Scc.Lower.splitFuncMarks`) leaves it and its placement trace as
they are (`splitFuncMarks_func0`), and the whole-program theorems of
`Scc/Lower/InvProg.lean` keep their statements.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.Inv

theorem instsWeight_addChk : ∀ (is : List Inst), (∀ i ∈ is, ∃ d p q, i = .addChk d p q) →
    instsWeight is = is.length
  | [], _ => rfl
  | i :: is, h => by
    obtain ⟨d, p, q, rfl⟩ := h i (by simp)
    have := instsWeight_addChk is fun j hj => h j (by simp [hj])
    simp only [instsWeight, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    rw [this]; simp [instWeight]; omega

/-- **`func0` of an `Accepted0` body is within the bound.** -/
theorem blocksOk_func0 {d : Decl} (hd : Accepted0 [d] = true) {r : Res} (name : Sym)
    (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r) : blocksOk (func0 name r) = true := by
  obtain ⟨ha, hn⟩ := lower0_insts_addChk _ _ _ _ hr
  obtain ⟨w, hw⟩ := accepted0_ret_singleton hd hr
  have hadds := lower0_next_adds _ _ _ _ hr
  have hmax := accepted0_adds hd
  simp only [blocksOk, func0, blockWeight, termWeight, hw, instsWeight_addChk _ ha, List.length_nil,
    List.length_singleton, List.all_nil, Bool.and_true, decide_eq_true_eq]
  simp only [maxAdds0] at hmax
  simp only [maxBlockLen]
  omega

/-- **`split_id` for `Accepted0`**: the split leaves the lowering of an
`Accepted0` code block and its trace unchanged. -/
theorem splitFuncMarks_func0 {d : Decl} (hd : Accepted0 [d] = true) {r : Res} (name : Sym)
    (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r) :
    splitFuncMarks (func0 name r, marks0 d) = (func0 name r, marks0 d) :=
  splitFuncMarks_id (blocksOk_func0 hd name hr)

end Scc.Lower.Inv
