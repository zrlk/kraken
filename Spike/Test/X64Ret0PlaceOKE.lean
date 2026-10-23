import Spike.Test.X64Ret0PlaceOKELit

/-!
# `PlaceOK` of `ret0.w` on scc's own x86-64 output

The x86-64 twin of `Spike/Test/A64Ret0PlaceOKE.lean`: `placeOK`
(`Scc/Cert/PlaceOKX64.lean`) decided by the kernel on
`Out.ofEmitted (lowerAll cfg ret0Src) sizes labelOffs`: the code cells, the
data sections and the placement data all computed by scc's pipeline and
`placeDataOf`, with no table as an input. The sizes and label offsets are
the assembler's for `scc`'s listing (`SccCode.ret0Asm`; untrusted, checked
by A2). The output is written out as a literal (`ret0L`, equal to it by
`ret0_out_eq`, `Spike/Test/X64Ret0PlaceOKELit.lean`), and the components
are decided on the literal one declaration each, then combined by
`placeOK_of`, so that no single decision holds the whole check.
-/

namespace Spike.Test.X64Ret0PlaceOKE

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

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

/-- A6 of `ret0.w`'s output: the block table in its phases, the runtime's
phase facts. -/
theorem ret0_part6 : a6 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A7 of `ret0.w`'s output: the runtime's code. -/
theorem ret0_part7 : a7 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A8 of `ret0.w`'s output: the runtime's data words. -/
theorem ret0_part8 : a8 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A9 of `ret0.w`'s output: `main`'s lowered code block, its phase facts. -/
theorem ret0_part9 : a9 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- A11 of `ret0.w`'s output: the runtime's fixed code, `scc_rt_main`'s
phase facts. -/
theorem ret0_part11 : a11 ret0L (tablesOf Config.canonical ret0L) = true := by decide +kernel

/-- **`ret0.w`'s `PlaceOK` on scc's own x86-64 output.** -/
theorem ret0_placeOK : placeOK Config.canonical ret0O = true := by
  rw [ret0_out_eq]
  exact placeOK_of ret0_part1 ret0_part2 ret0_part3 ret0_part4 ret0_part5 ret0_part6 ret0_part7 ret0_part8
    ret0_part9 ret0_part11

end Spike.Test.X64Ret0PlaceOKE
