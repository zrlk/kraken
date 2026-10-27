import Spike.Lib.Src.Walk2Of
import Spike.Lib.LowerA64.Walk2Of

/-! Axiom guards for the walk facts of an `Accepted2` block from `Accepted2`. -/

open Spike.Lib.LowerNode

/-- info: 'Spike.Lib.LowerNode.callTs_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms callTs_ofAccepted2

/-- info: 'Spike.Lib.LowerNode.decl2_setup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decl2_setup

/-- info: 'Spike.Lib.LowerNode.walk_relB_decl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms walk_relB_decl

/-- info: 'Spike.Lib.LowerNode.callArg_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms callArg_ofAccepted2

/-- info: 'Spike.Lib.LowerNode.retOne_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms retOne_ofAccepted2

/-- info: 'Spike.Lib.LowerNode.walk2_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms walk2_ofAccepted2

/-- info: 'Spike.Lib.LowerNode.locBaseReg_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locBaseReg_ofAccepted2

/-- info: 'Spike.Lib.LowerNode.litPts_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms litPts_ofAccepted2

/-- info: 'Spike.Lib.LowerNode.countsB_ofAccepted2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms countsB_ofAccepted2

/-- info: 'Spike.Lib.LowerNode.xchgsB_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms xchgsB_ofAccepted2

/-- info: 'Spike.Lib.LowerA64.retOk_ofAccepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.retOk_ofAccepted2
