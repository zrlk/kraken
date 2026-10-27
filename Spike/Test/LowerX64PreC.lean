import Spike.Lib.LowerX64.PreC

/-!
# The premises at the contexts from the placement check (x86-64)

`Spike/Lib/LowerX64/PreC.lean`: a code block's `CallPre`, a callee's
`CalleePre` and every code block's `FnSpecC` at the contexts `CxOkC`; the
axioms of the pieces.
-/

namespace Spike.Test.LowerX64PreC

/-- info: 'Spike.Lib.LowerX64.Pairwise2.get?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.Pairwise2.get?

/-- info: 'Spike.Lib.LowerX64.callPre_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.callPre_of

/-- info: 'Spike.Lib.LowerX64.argTy_callee' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.argTy_callee

/-- info: 'Spike.Lib.LowerX64.calleePre_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.calleePre_of

/-- info: 'Spike.Lib.LowerX64.fnSpecC_all_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.fnSpecC_all_ofPlaceOK

end Spike.Test.LowerX64PreC
