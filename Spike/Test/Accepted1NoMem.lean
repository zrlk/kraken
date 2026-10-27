import Spike.Lib.Accepted1NoMem

/-!
# An `Accepted1` program with calls has no memory operation

`Spike/Lib/Accepted1NoMem.lean`: the axioms of the pieces.
-/

namespace Spike.Test.Accepted1NoMem

/-- info: 'Spike.Lib.Accepted1Src.body1_noMemE' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.Accepted1Src.body1_noMemE

/-- info: 'Spike.Lib.Accepted1Src.decls1_noMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.Accepted1Src.decls1_noMem

/-- info: 'Spike.Lib.Accepted1Src.accepted1_noMem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.Accepted1Src.accepted1_noMem

end Spike.Test.Accepted1NoMem
