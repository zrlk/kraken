/-
**The clone path's blocks are wake.w's x86-64 code**: the checks of
`X64WakeClone.wcCloneIn`, `X64WakeParent.parentIn` and
`X64WakeChild.childIn` on `SccCode.wakeCells` (`Spike/Lib/X64WakeCode.lean`,
generated from wake.w), by the kernel. With `Lays exe SccCode.wakeCells kp`
they discharge the `hin` premises of `wake_wc_clone_segW`, `seg_parent` and
`seg_child`.
-/
import Spike.Lib.X64WakeCode
import Spike.Lib.X64WakeCloneSeg
import Spike.Lib.X64WakeParent
import Spike.Lib.X64WakeChild

namespace Spike.Lib.X64.WakePh

theorem wake_wcCloneIn : WcClone.wcCloneIn SccCode.wakeCells = true := by decide +kernel

theorem wake_parentIn : Parent.parentIn SccCode.wakeCells = true := by decide +kernel

theorem wake_childIn : Child.childIn SccCode.wakeCells = true := by decide +kernel

/-- info: 'Spike.Lib.X64.WakePh.wake_wcCloneIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wake_wcCloneIn

/-- info: 'Spike.Lib.X64.WakePh.wake_parentIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wake_parentIn

/-- info: 'Spike.Lib.X64.WakePh.wake_childIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wake_childIn

end Spike.Lib.X64.WakePh
