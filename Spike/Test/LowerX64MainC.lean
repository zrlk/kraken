import Spike.Lib.LowerX64.MainC

/-!
# The user `main` from the placement check (x86-64)

`Spike/Lib/LowerX64/MainC.lean`: the aborts of the code blocks at their
contexts, held back at the consumer's start, never end; `main`'s context,
`CalleePre` and return at `scc_rt_main`'s call; the user `main` as
`scc_rt_main`'s user function at depth; the axioms of the pieces.
-/

namespace Spike.Test.LowerX64MainC

/-- info: 'Spike.Lib.LowerX64.abC_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.abC_lag

/-- info: 'Spike.Lib.LowerX64.mainCtxB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainCtxB

/-- info: 'Spike.Lib.LowerX64.argTy_main' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.argTy_main

/-- info: 'Spike.Lib.LowerX64.mainPre_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainPre_of

/-- info: 'Spike.Lib.LowerX64.uPostS_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.uPostS_ret

/-- info: 'Spike.Lib.LowerX64.userMainSW_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.userMainSW_of

/-- info: 'Spike.Lib.LowerX64.fnCodes_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.fnCodes_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.userMainSW_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.userMainSW_ofPlaceOK

end Spike.Test.LowerX64MainC
