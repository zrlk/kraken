import Spike.Lib.LowerA64.Body2
import Spike.Lib.LowerA64.Body2Seg
import Spike.Lib.LowerA64.XchgOff
import Spike.Lib.LowerA64.LaneSeg
import Spike.Lib.LowerA64.LaneC2
import Spike.Lib.LowerA64.Body2SegOf

/-! Axiom guards for the AArch64 `Accepted2` body's code, nodes and induction. -/

open Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.CodeC2_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CodeC2_append

/-- info: 'Spike.Lib.LowerA64.RetJ.toJ2' depends on axioms: [propext] -/
#guard_msgs in #print axioms RetJ.toJ2

/-- info: 'Spike.Lib.LowerA64.ExitC2.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ExitC2.trans

/-- info: 'Spike.Lib.LowerA64.body2_segS_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body2_segS_of

/-- info: 'Spike.Lib.A64.Flow.XchgSeg.xchg_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.XchgSeg.xchg_segW

/-- info: 'Spike.Lib.LowerA64.ldrOff_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ldrOff_form

/-- info: 'Spike.Lib.LowerA64.strOff_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms strOff_form

/-- info: 'Spike.Lib.LowerA64.lane_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lane_segW

/-- info: 'Spike.Lib.LowerA64.laneC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms laneC_of

/-- info: 'Spike.Lib.LowerA64.addC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addC2_of

/-- info: 'Spike.Lib.LowerA64.subC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subC2_of

/-- info: 'Spike.Lib.LowerA64.ifC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ifC2_of

/-- info: 'Spike.Lib.LowerA64.retC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms retC2_of

/-- info: 'Spike.Lib.LowerA64.pureMv2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pureMv2_of

/-- info: 'Spike.Lib.LowerA64.splitMv2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms splitMv2_of

/-- info: 'Spike.Lib.LowerA64.unpackMv2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unpackMv2_of

/-- info: 'Spike.Lib.LowerA64.body2_segS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body2_segS
