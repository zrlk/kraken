import Spike.Lib.SegGood1

/-!
# A segment at depth keeps its pairs `Good1`

`Spike/Lib/SegGood1.lean`: the axioms of the pieces.
-/

namespace Spike.Test.SegGood1

/-- info: 'Spike.Lib.Good1.not_xchg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.Good1.not_xchg

/-- info: 'Spike.Lib.Out.good1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.Out.good1

/-- info: 'Spike.Lib.SegWS.good1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.SegWS.good1

end Spike.Test.SegGood1
