import Spike.Lib.LowerX64.FnC

/-!
# An x86-64 function with calls

`Spike/Lib/LowerX64/FnC.lean`: the prologue then the body with calls, as
one segment from the entry to the body's exits; the axioms of the pieces.
-/

namespace Spike.Test.LowerX64FnC

open Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.prologue_body_segT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prologue_body_segT

/-- info: 'Spike.Lib.LowerX64.fnC_segS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnC_segS

/-- info: 'Spike.Lib.LowerX64.prologue_body_segTP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prologue_body_segTP

/-- info: 'Spike.Lib.LowerX64.fnC_segSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnC_segSP

end Spike.Test.LowerX64FnC
