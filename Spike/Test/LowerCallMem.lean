import Spike.Lib.LowerCallMem

/-!
# A call at a point of the walk is emitted

`Spike/Lib/LowerCallMem.lean`: the axioms of `lowerC_callMem`.
-/

namespace Spike.Test.LowerCallMem

open Spike.Lib.LowerShape

/-- info: 'Spike.Lib.LowerShape.lowerC_callMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerC_callMem

/-- info: 'Spike.Lib.LowerShape.lowerC_addMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerC_addMem

end Spike.Test.LowerCallMem
