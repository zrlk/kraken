import Spike.Lib.LowerX64.ProgCB

/-!
# Every x86-64 function's segment from the premises at the contexts

`Spike/Lib/LowerX64/ProgCB.lean`: the induction with the calls from
`callC_of` and the callees' segments from their `FnSpecC`; the axioms of
the pieces.
-/

namespace Spike.Test.LowerX64ProgCB

/-- info: 'Spike.Lib.LowerX64.CalleePre.seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.CalleePre.seg

/-- info: 'Spike.Lib.LowerX64.fnSpecC_all_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.fnSpecC_all_ofPre

/-- info: 'Spike.Lib.LowerX64.at_rsp0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.at_rsp0

end Spike.Test.LowerX64ProgCB
