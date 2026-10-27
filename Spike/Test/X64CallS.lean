import Spike.Lib.X64CallSA

/-!
Source calls on x86-64 (`Spike/Lib/X64CallS.lean`, `Spike/Lib/X64CallSA.lean`): the axioms of their theorems.
-/

namespace Spike.Lib.X64.Flow.TestCallS

open Spike.Lib.X64.Flow

/--
info: 'Spike.Lib.X64.Flow.call_ndS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms call_ndS

/--
info: 'Spike.Lib.X64.Flow.call_nd_FWKS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms call_nd_FWKS

/--
info: 'Spike.Lib.X64.Flow.call_ndSA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms call_ndSA

/--
info: 'Spike.Lib.X64.Flow.call_ndSF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms call_ndSF

end Spike.Lib.X64.Flow.TestCallS
