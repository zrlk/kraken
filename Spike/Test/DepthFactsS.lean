import Spike.Lib.DepthFactsS
import Spike.Lib.X64CallS
import Spike.Lib.X64ConsumerS

/-!
# The source halves of `SFactsS` through a call bracket

`Spike/Lib/DepthFactsS.lean`: the axioms of the pieces, and the x86-64
`CallTo` and `EnvSmallS` are the neutral ones by `id` (the AArch64 twins
alike).
-/

namespace Spike.Test.DepthFactsS

open CoreLang CoreTerm Spike.Lib

/-- x86-64's `CallTo` is `SrcCallTo`. -/
example {p : Prog} {c cE : Ctl} {fr : TermRun.Frame} (h : Spike.Lib.X64.Flow.CallTo p c cE fr) :
    SrcCallTo p c cE fr := h

/-- x86-64's `EnvSmallS` is its body. -/
example {env : TermRun.Env} {fs : List TermRun.Frame} (h : Spike.Lib.X64ConsumerS.EnvSmallS env fs) :
    EnvSmall env ∧ ∀ f ∈ fs, EnvSmall f.env := h

/-- info: 'Spike.Lib.SrcCallTo.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.SrcCallTo.step

/-- info: 'Spike.Lib.good1_callTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.good1_callTo

/-- info: 'Spike.Lib.good1_retTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.good1_retTo

/-- info: 'Spike.Lib.envNum_entry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.envNum_entry

/-- info: 'Spike.Lib.envSmall_entry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.envSmall_entry

/-- info: 'Spike.Lib.framesSmall_callTo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.framesSmall_callTo

/-- info: 'Spike.Lib.envSmallS_callTo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.envSmallS_callTo

/-- info: 'Spike.Lib.envSmall_retTo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.envSmall_retTo

/-- info: 'Spike.Lib.envSmallS_retTo' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spike.Lib.envSmallS_retTo

/-- info: 'Spike.Lib.noRet_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms Spike.Lib.noRet_cons

/-- info: 'Spike.Lib.cell_of_good1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.cell_of_good1

/-- info: 'Spike.Lib.noAlloc_of_good1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.noAlloc_of_good1

end Spike.Test.DepthFactsS
