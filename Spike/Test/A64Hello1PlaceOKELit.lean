import Scc.Cert.PlaceDataA64
import Scc.Cert.OutLitA64
import Spike.Lib.Hello1Src

/-!
# `hello1.w`'s output as a literal

scc's AArch64 output for `hello1.w` (`hello1O`) and its value written out
at elaboration time (`hello1L`, `scc_lit%`), equal by one kernel run of the
pipeline (`hello1_out_eq`), apart from `PlaceOK`'s parts
(`Spike/Test/A64Hello1PlaceOKE.lean`), as `Spike/Test/A64Ret0PlaceOKELit.lean`
for `ret0.w`.
-/

namespace Spike.Test.A64Hello1PlaceOKE

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.Hello1Src (hello1Src)

/-- scc's AArch64 output for `hello1.w` as `PlaceOK` reads it. -/
def hello1O : Out := Out.ofEmitted (Scc.Lower.A64.lowerAll { arch := .arm } hello1Src)

/-- `hello1O` as a literal: its value computed at elaboration time. -/
def hello1L : Out := scc_lit% hello1O

/-- The literal is the pipeline's output (one kernel run of `lowerAll`). -/
theorem hello1_out_eq : hello1O = hello1L := by kernel_rfl

end Spike.Test.A64Hello1PlaceOKE
