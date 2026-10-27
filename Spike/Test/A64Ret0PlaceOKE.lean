import Spike.Test.A64Ret0PlaceOKELit

/-!
# `PlaceOK` of `ret0.w` on scc's own output

`placeOK` (`Scc/Cert/PlaceOKA64.lean`) decided by the kernel on
`Out.ofEmitted (lowerAll cfg ret0Src)`: the instruction list, the data
sections and the placement data all computed by scc's pipeline and
`placeDataOf`, with no table as an input. The output is written out as a
literal (`ret0L`, equal to it by `ret0_out_eq`,
`Spike/Test/A64Ret0PlaceOKELit.lean`), and the components are decided on
the literal one declaration each (peak RssAnon under 1 GB each), then
combined by `placeOK_of`.
-/

namespace Spike.Test.A64Ret0PlaceOKE

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

set_option maxRecDepth 100000

/-- A1 of `ret0.w`'s output: the static link, the entry stack clear of it. -/
theorem ret0_part1 : a1 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A2 of `ret0.w`'s output: the loader's checks, the abort labels, the image. -/
theorem ret0_part2 : a2 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A3 of `ret0.w`'s output: the computed block table at its places. -/
theorem ret0_part3 : a3 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A4 of `ret0.w`'s output: the one-word fragment, the stack need. -/
theorem ret0_part4 : a4 Config.canonical ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A5 of `ret0.w`'s output: the block table covered at its offsets. -/
theorem ret0_part5 : a5 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A6 of `ret0.w`'s output: the block table in its phases. -/
theorem ret0_part6 : a6 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A7 of `ret0.w`'s output: the runtime's code. -/
theorem ret0_part7 : a7 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A8 of `ret0.w`'s output: the runtime's data words. -/
theorem ret0_part8 : a8 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A9 of `ret0.w`'s output: `main`'s lowered code block at its context. -/
theorem ret0_part9 : a9 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A11 of `ret0.w`'s output: the runtime's fixed code. -/
theorem ret0_part11 : a11 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A12 of `ret0.w`'s output: the code of every user function. -/
theorem ret0_part12 : a12 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- **`ret0.w`'s `PlaceOK` on scc's own output.** -/
theorem ret0_placeOK : placeOK Config.canonical ret0O = true := by
  rw [ret0_out_eq]
  exact placeOK_of ret0_part1 ret0_part2 ret0_part3 ret0_part4 ret0_part5 ret0_part6 ret0_part7 ret0_part8
    ret0_part9 ret0_part11 ret0_part12

end Spike.Test.A64Ret0PlaceOKE
