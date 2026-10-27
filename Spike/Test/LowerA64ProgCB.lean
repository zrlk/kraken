import Spike.Lib.LowerA64.ProgCB

/-!
# Every function's segment from the calls' and the callees' premises (AArch64)

`Spike/Lib/LowerA64/ProgCB.lean`: the axioms of the pieces, and a call
premise from a body segment that needs no callee (e.g. a code block with
no call).
-/

namespace Spike.Test.LowerA64ProgCB

open Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.CalleePre.seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CalleePre.seg

/-- info: 'Spike.Lib.LowerA64.at_sp0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms at_sp0

/-- info: 'Spike.Lib.LowerA64.fnSpecC_all_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnSpecC_all_ofPre

/-- A body segment at a context is a call premise at every callee room. -/
example {W K p lbl ms exe prog endPc RaOk Cd i T d} {c : FnCode exe prog endPc RaOk Cd i T d} {R F fs fp ra tp G0 Ab}
    (h : BodyAt W K p lbl ms c R F fs fp ra tp G0 Ab) (D : Int) :
    CallPre W K p lbl ms c R F fs fp ra tp G0 Ab D := fun _ => h

end Spike.Test.LowerA64ProgCB
