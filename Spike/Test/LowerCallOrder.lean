import Spike.Lib.LowerCallOrder

/-!
# An `Accepted1` program calls only earlier code blocks

`Spike/Lib/LowerCallOrder.lean`: the order of the induction over a
program's declarations; the axioms of the pieces.
-/

namespace Spike.Test.LowerCallOrder

open Spike.Lib.LowerCallOrder

/-- info: 'Spike.Lib.LowerCallOrder.body1_callee_walkC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms body1_callee_walkC

/-- info: 'Spike.Lib.LowerCallOrder.callee_earlier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms callee_earlier

/-- info: 'Spike.Lib.LowerCallOrder.specs_of_callOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms specs_of_callOrder

/-- info: 'Spike.Lib.LowerCallOrder.walkC_retOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms walkC_retOne

/-- info: 'Spike.Lib.LowerCallOrder.specs_of_callOrderLt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms specs_of_callOrderLt

/-- info: 'Spike.Lib.LowerCallOrder.body1_call_walkC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms body1_call_walkC

end Spike.Test.LowerCallOrder
