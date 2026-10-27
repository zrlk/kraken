/-
**`print` with the refusal's data** (`Spike/Lib/A64PrintAb.lean`,
`Spike/Lib/A64PrintCallAb.lean`): the callee spec `seg_printAb_ofW`, its
system call and refusal lemmas, and the call segments built on it rest on
the standard axioms only (`refusal_of_refused` without `Classical.choice`).
-/
import Spike.Lib.A64PrintCallAb

namespace Spike.Lib.A64.PrintAb.Test

open Spike.Lib.A64.Flow

/-- info: 'Spike.Lib.A64.PrintAb.seg_printAb_ofW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrintAb.seg_printAb_ofW

/-- info: 'Spike.Lib.A64.PrintAb.hsvc_of_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrintAb.hsvc_of_emit

/-- info: 'Spike.Lib.A64.PrintAb.refusal_of_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PrintAb.refusal_of_refused

/-- info: 'Spike.Lib.A64.Flow.print_call_segAbW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms print_call_segAbW

/-- info: 'Spike.Lib.A64.Flow.print_call_abort_segAbW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms print_call_abort_segAbW

end Spike.Lib.A64.PrintAb.Test
