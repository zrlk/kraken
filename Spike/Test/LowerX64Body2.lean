import Spike.Lib.LowerX64.Body2
import Spike.Lib.LowerX64.Body2Seg
import Spike.Lib.X64XchgSeg
import Spike.Lib.Src.NJBXchg2
import Spike.Lib.Src.XchgB
import Spike.Lib.Src.GroupPl
import Spike.Lib.Src.XchgSiteB
import Spike.Lib.LowerX64.LaneC2

/-! Axiom guards for the x86-64 `Accepted2` body's code, nodes, walk facts and induction. -/

open Spike.Lib.LowerX64 Spike.Lib.LowerNode

/-- info: 'Spike.Lib.LowerX64.codeC2_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2_append

/-- info: 'Spike.Lib.LowerX64.RetJ.toJ2' depends on axioms: [propext] -/
#guard_msgs in #print axioms RetJ.toJ2

/-- info: 'Spike.Lib.LowerNode.litPt_of_B' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms litPt_of_B

/-- info: 'Spike.Lib.LowerX64.body2_segS_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body2_segS_of

/-- info: 'Spike.Lib.X64.Flow.XchgSeg.xchg_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.XchgSeg.xchg_segW

/-- info: 'Spike.Lib.LowerNode.NJB.xchg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NJB.xchg2

/-- info: 'Spike.Lib.LowerNode.xchgsB_of_body2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms xchgsB_of_body2

/-- info: 'Spike.Lib.LowerNode.pairSmall_head' depends on axioms: [propext] -/
#guard_msgs in #print axioms pairSmall_head

/-- info: 'Spike.Lib.LowerNode.sevalAt_ofEnv2G_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sevalAt_ofEnv2G_one

/-- info: 'Spike.Lib.LowerNode.xchg_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms xchg_site

/-- info: 'Spike.Lib.LowerX64.lane_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lane_segW

/-- info: 'Spike.Lib.LowerX64.laneC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms laneC_of
