import Spike.Lib.LowerX64.CallSite1

/-!
The axioms of each function's and each call site's placement facts of an
`Accepted1` program from `PlaceOK` (x86-64, `Spike/Lib/LowerX64/CallSite1.lean`).
-/

namespace Spike.Lib.LowerX64.TestCallSite1

open Spike.Lib.LowerX64

/--
info: 'Spike.Lib.LowerX64.fnPh1_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fnPh1_ofPlaceOK

/--
info: 'Spike.Lib.LowerX64.callSite1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms callSite1

/--
info: 'Spike.Lib.LowerX64.call_blockAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms call_blockAt

/-- `classify` reads a `callq` to a label as the consumer's call. -/
example : Spike.Lib.X64.classify (Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel "g"))) = some (.call "g") :=
  classify_callq "g"

end Spike.Lib.LowerX64.TestCallSite1
