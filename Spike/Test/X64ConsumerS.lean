import Spike.Lib.X64ConsumerS

/-!
The one-thread consumer at any call depth on x86-64
(`Spike/Lib/X64ConsumerS.lean`): the axioms of its theorems.
-/

namespace Spike.Lib.X64ConsumerS.Test

open Spike.Lib.X64ConsumerS

/--
info: 'Spike.Lib.X64ConsumerS.correctKS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correctKS

/--
info: 'Spike.Lib.X64ConsumerS.correctKOnS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correctKOnS

/--
info: 'Spike.Lib.X64ConsumerS.promSharedS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms promSharedS

/--
info: 'Spike.Lib.X64ConsumerS.pre_stepS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pre_stepS

end Spike.Lib.X64ConsumerS.Test
