import Spike.Lib.X64SFactsS1
import Spike.Lib.LowerX64.StartSegS

/-!
The x86-64 start chain at depth (`Spike/Lib/Rt/X64SegsS.lean`,
`Spike/Lib/LowerX64/StartSegS.lean`) and `SFactsS` at the empty frames
(`Spike/Lib/X64SFactsS1.lean`): the axioms of their theorems.
-/

namespace Spike.Test.X64StartSegS

/--
info: 'Spike.Lib.X64ConsumerS.SFactsS.ofSFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.SFactsS.ofSFacts

/--
info: 'Spike.Lib.X64ConsumerS.SFactsS.ofSFacts0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.SFactsS.ofSFacts0

/--
info: 'Spike.Lib.X64.Rt.mainU_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.Rt.mainU_segWS

/--
info: 'Spike.Lib.X64.Rt.startSwitchU_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.Rt.startSwitchU_segWS

/--
info: 'Spike.Lib.X64.Rt.startU_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.Rt.startU_segWS

/--
info: 'Spike.Lib.X64.Rt.entry_segWS'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.Rt.entry_segWS'

/--
info: 'Spike.Lib.LowerX64.x64_start_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.x64_start_segWS

/--
info: 'Spike.Lib.X64ConsumerS.msAgree_msOfS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64ConsumerS.msAgree_msOfS

/--
info: 'Spike.Lib.X64.Rt.xExitTail_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.Rt.xExitTail_segWS

end Spike.Test.X64StartSegS
