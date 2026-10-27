import Spike.Lib.X64PlacedS
import Spike.Lib.LowerX64.BodyWS1
import Spike.Lib.X64SFactsS1

/-!
The suspended frames' placement on x86-64 (`Spike/Lib/X64PlacedS.lean`) and
an `Accepted1` body's blocks at depth (`Spike/Lib/LowerX64/BodyWS1.lean`),
`SFactsS` at the suspended frames (`SFactsS.ofSFactsAt`):
the axioms of their theorems.
-/

namespace Spike.Test.X64BodyWS1

/--
info: 'Spike.Lib.X64ConsumerS.PlacedS.ofFrames' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.PlacedS.ofFrames

/--
info: 'Spike.Lib.X64ConsumerS.PlacedS.frames' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.PlacedS.frames

/--
info: 'Spike.Lib.X64ConsumerS.FramesPlacedIn.of_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.FramesPlacedIn.of_eq

/--
info: 'Spike.Lib.X64ConsumerS.FramesPlacedIn.push' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.FramesPlacedIn.push

/--
info: 'Spike.Lib.X64ConsumerS.FramesPlacedIn.toFramesPlaced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.FramesPlacedIn.toFramesPlaced

/--
info: 'Spike.Lib.X64ConsumerS.EnvSmallS.push' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.EnvSmallS.push

/--
info: 'Spike.Lib.LowerX64.bodyWS0_lag' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.bodyWS0_lag

/--
info: 'Spike.Lib.LowerX64.blkW_bodyS1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.blkW_bodyS1

/--
info: 'Spike.Lib.X64ConsumerS.SFactsS.ofSFactsAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.SFactsS.ofSFactsAt

end Spike.Test.X64BodyWS1
