import Spike.Lib.LowerA64.PreC

/-!
# The premises at the contexts (AArch64)

`Spike/Lib/LowerA64/PreC.lean`: a code block's call premise `CallPre` and a
callee's `CalleePre` at the contexts `CxOkC` from the placement check, for
code facts with no frames limit, and every code block's `FnSpecC`; the
axioms.
-/

namespace Spike.Test.LowerA64PreC

/-- info: 'Spike.Lib.LowerA64.limBv_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.limBv_of_le

/-- info: 'Spike.Lib.LowerA64.argTy_callee' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.argTy_callee

/-- info: 'Spike.Lib.LowerA64.callPre_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.callPre_of

/-- info: 'Spike.Lib.LowerA64.calleePre_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.calleePre_of

/-- info: 'Spike.Lib.LowerA64.fnSpecC_all_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.fnSpecC_all_ofPlaceOK

end Spike.Test.LowerA64PreC
