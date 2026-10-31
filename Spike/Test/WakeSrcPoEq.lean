import Spike.Lib.WakeA64

/-!
# AArch64's local source parameters are the upstream ones

`Spike.Lib.WakeT1.srcPo` (the source parameters of AArch64's `WakeA64.wakeS`) is a
local copy of the T1 patch to `Scc/Sem/SrcOut.lean`, since merged as
`Scc.Sem.SrcSem.srcPo`; x86-64's `Spike.Test.WakeLinkedX64.wakeSX` uses the upstream
one. They are the same definition: both wake statements are about one
source semantics.
-/

namespace Spike.Test.WakeSrcPoEq

/-- **The local `progInitT` is the upstream `progInit`.** -/
theorem progInit_eq : Spike.Lib.WakeT1.progInitT = Scc.Sem.SrcSem.progInit := rfl

/-- **The local `srcPo` is the upstream `srcPo`.** -/
theorem srcPo_eq : Spike.Lib.WakeT1.srcPo = Scc.Sem.SrcSem.srcPo := rfl

end Spike.Test.WakeSrcPoEq

/-- info: 'Spike.Test.WakeSrcPoEq.srcPo_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeSrcPoEq.srcPo_eq
