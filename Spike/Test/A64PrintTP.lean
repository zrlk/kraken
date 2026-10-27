import Spike.Lib.A64PrintTP

/-! Axiom guards for `print`'s call keeping the thread pointer and for the
empty-slice call (AArch64). -/

open Spike.Lib.A64.Flow


/-- info: 'Spike.Lib.A64.Flow.print_call_emptyW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_call_emptyW

/-- info: 'Spike.Lib.A64.Flow.PrintAW.noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PrintAW.noMsr

/-- info: 'Spike.Lib.A64.Flow.print_svc_noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_svc_noMsr

/-- info: 'Spike.Lib.A64.Flow.print_call_segWB_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_call_segWB_tp

/-- info: 'Spike.Lib.A64.Flow.print_call_emptyW_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_call_emptyW_tp

/-- info: 'Spike.Lib.A64.Flow.print_call_segW_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_call_segW_tp

/-- info: 'Spike.Lib.A64.Flow.print_callW'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_callW'

/-- info: 'Spike.Lib.A64.Flow.print_call_segW'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_call_segW'

/-- info: 'Spike.Lib.A64.Flow.print_call_emptyW'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_call_emptyW'

/-- info: 'Spike.Lib.A64.Flow.print_call_segW_tp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_call_segW_tp'

/-- info: 'Spike.Lib.A64.Flow.print_call_emptyW_tp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms print_call_emptyW_tp'
