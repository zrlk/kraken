import Spike.Lib.LowerA64.ProgC

/-!
# Every function of an `Accepted1` program one segment (AArch64)

`Spike/Lib/LowerA64/FnC.lean` and `Spike/Lib/LowerA64/ProgC.lean`: the
prologue with its parameter spill at a node with the thread pointer, the
function's segment from its body's, the body's from the call brackets, the
induction over the call order; the axioms of the pieces, and the spill's
shape at a code block with no `Int` parameter.
-/

namespace Spike.Test.LowerA64ProgC

open Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.prologue_body_segTP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prologue_body_segTP

/-- info: 'Spike.Lib.LowerA64.paramSpill_of_spills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paramSpill_of_spills

/-- info: 'Spike.Lib.LowerA64.fnSpecC_of_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnSpecC_of_body

/-- info: 'Spike.Lib.LowerA64.bodySpecC_of_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bodySpecC_of_call

/-- info: 'Spike.Lib.LowerA64.fnSpecC_allI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnSpecC_allI

/-- No parameter, no spill: `ParamSpill` at `[]`. -/
example (cx : Scc.Emit.A64.FnCtx) : ParamSpill cx [] [] := .inl ⟨rfl, rfl⟩

/-- A code block whose parameter is not an `Int` has no parameter register. -/
example (d : CoreTerm.Decl) (h : (d.argTy == .int) = false) : Scc.Lower.Inv.params1R d = [] := by
  simp [Scc.Lower.Inv.params1R, h]

end Spike.Test.LowerA64ProgC
