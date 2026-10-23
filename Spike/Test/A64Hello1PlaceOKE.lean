import Spike.Test.A64Hello1PlaceOKELit

/-!
# `PlaceOK` of `hello1.w` on scc's own output

`placeOK` (`Scc/Cert/PlaceOKA64.lean`) decided by the kernel on
`Out.ofEmitted (lowerAll cfg hello1Src)`, as `Spike/Test/A64Ret0PlaceOKE.lean`
for `ret0.w`: the instruction list, the data sections and the placement data
all computed by scc's pipeline and `placeDataOf`, with no table as an input.
`hello1.w` has a setup block and the output extern `print` (whose signature
the kernel compares through `Frontend.printSig`/`printOwnSig`). The
output is written out as a literal (`hello1L`, equal to it by
`hello1_out_eq`, `Spike/Test/A64Hello1PlaceOKELit.lean`), and the
components are decided on the literal one declaration each. A11 fails: the
setup block's tail has no `MainCode` yet, so `PlaceOK` is `false`
(`hello1_placeOK`).

The source program is a term (`Spike.Lib.Hello1Src.hello1Src`), checked
against the frontend's reading of `Scc/Test/hello1.w` by `#guard`: the
kernel does not run the frontend's parser, which is `partial`.
-/

namespace Spike.Test.A64Hello1PlaceOKE

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

set_option maxRecDepth 100000

theorem hello1_part1 : a1 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part2 : a2 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part3 : a3 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part4 : a4 Config.canonical hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part5 : a5 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part6 : a6 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part7 : a7 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part8 : a8 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
/-- A9 (no `func0`-shaped function: `wc_main` calls). -/
theorem hello1_part9 : a9 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel

/-- A11 of `hello1.w`'s output fails: `scc_rt_main`'s tail is after a setup
block, and A11 has no `MainCode` for it yet. -/
theorem hello1_part11 : a11 hello1L (tablesOf Config.canonical hello1L) = false := by decide +kernel

/-- **`hello1.w`'s `PlaceOK` on scc's own output is `false`** (A11). -/
theorem hello1_placeOK : placeOK Config.canonical hello1O = false := by
  rw [hello1_out_eq]
  exact placeOK_eq_false_of_a11 hello1_part11

end Spike.Test.A64Hello1PlaceOKE
