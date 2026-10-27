import Spike.Lib.X64SegInstS

/-!
The consumer's obligations at any call depth from one segment on x86-64
(`Spike/Lib/X64SegInstS.lean`): the axioms of its theorems.
-/

namespace Spike.Lib.X64ConsumerS.TestSegInstS

open Spike.Lib.X64ConsumerS

/--
info: 'Spike.Lib.X64ConsumerS.inst_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inst_of_segWS

/--
info: 'Spike.Lib.X64ConsumerS.correctKSPE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correctKSPE

/--
info: 'Spike.Lib.X64ConsumerS.writeNoPromS_of_wrIn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms writeNoPromS_of_wrIn

end Spike.Lib.X64ConsumerS.TestSegInstS
