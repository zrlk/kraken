import Spike.Test.X64Hello1PlaceOKELit
import Scc.Cert.A12StageX64

/-!
# `PlaceOK` of `hello1.w` on scc's own x86-64 output

The x86-64 twin of `Spike/Test/A64Hello1PlaceOKE.lean`, with `hello1.w`'s
source program as a term (`Spike.Lib.Hello1Src`): `placeOK`
(`Scc/Cert/PlaceOKX64.lean`) decided by the kernel on
`Out.ofEmitted (lowerAll cfg hello1Src) sizes labelOffs`: the code cells, the
data sections and the placement data all computed by scc's pipeline and
`placeDataOf`, with no table as an input. The sizes and label offsets are
the assembler's for `scc`'s listing (`SccCode.hello1Asm`; untrusted, checked
by A2). The output is written out as a literal (`hello1L`, equal to it by
`hello1_out_eq`, `Spike/Test/X64Hello1PlaceOKELit.lean`), and the
components are decided on the literal one declaration each, A11 at
`scc_rt_main`'s tail after a setup block (`setupOk`), so `PlaceOK` holds
(`placeOK_of`). `hello1.w` is outside `Accepted0`: placement only, no
correctness claim.
-/

namespace Spike.Test.X64Hello1PlaceOKE

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

set_option maxRecDepth 100000

theorem hello1_part1 : a1 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part2 : a2 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part3 : a3 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part4 : a4 Config.canonical hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part5 : a5 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part7 : a7 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part8 : a8 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel

theorem hello1_part6 : a6 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel
theorem hello1_part9 : a9 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel

/-- A11 of `hello1.w`'s output: the runtime's fixed code with `scc_rt_main`
after its setup block, its phase facts. -/
theorem hello1_part11 : a11 hello1L (tablesOf Config.canonical hello1L) = true := by decide +kernel

/-- A12 of `hello1.w`'s output: the code and phase facts of every
stack-checked function (by its two keyed parts, `Scc/Cert/A12StageX64.lean`). -/
theorem hello1_part12 : a12 hello1L (tablesOf Config.canonical hello1L) = true :=
  a12_of_split (by decide +kernel) (by decide +kernel)

/-- **`hello1.w`'s `PlaceOK` on scc's own x86-64 output.** -/
theorem hello1_placeOK : placeOK Config.canonical hello1O = true := by
  rw [hello1_out_eq]
  exact placeOK_of hello1_part1 hello1_part2 hello1_part3 hello1_part4 hello1_part5 hello1_part6 hello1_part7
    hello1_part8 hello1_part9 hello1_part11 hello1_part12

end Spike.Test.X64Hello1PlaceOKE
