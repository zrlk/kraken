import Scc.Cert.PlaceDataX64
import Scc.Cert.OutLitX64
import Spike.Lib.Hello1Src
import Spike.Lib.X64Hello1Code

/-!
# `hello1.w`'s x86-64 output as a literal

The x86-64 twin of `Spike/Test/A64Hello1PlaceOKELit.lean`: scc's x86-64
output for `hello1.w` (`hello1O`, computed by `lowerAll` and `Out.ofEmitted`
at the assembler's sizes and label offsets, `SccCode.hello1Asm`) and its
value written out at elaboration time (`hello1L`, `scc_lit%`), equal by one
kernel run of the pipeline (`hello1_out_eq`), in a file of its own:
`Spike/Test/X64Hello1PlaceOKE.lean` decides `PlaceOK`'s parts on the
literal, one declaration each.
-/

namespace Spike.Test.X64Hello1PlaceOKE

set_option maxRecDepth 100000

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- scc's x86-64 output for `hello1.w` as `PlaceOK` reads it, at the
assembler's sizes and label offsets. -/
def hello1O : Out :=
  Out.ofEmitted (Scc.Lower.X64.lowerAll { arch := .x64 } Spike.Lib.Hello1Src.hello1Src)
    SccCode.hello1Asm.sizes SccCode.hello1Asm.labelOffs

/-- `hello1O` as a literal: its value computed at elaboration time. -/
def hello1L : Out := scc_lit% hello1O

/-- The literal is the pipeline's output (one kernel run of `lowerAll`). -/
theorem hello1_out_eq : hello1O = hello1L := by kernel_rfl

end Spike.Test.X64Hello1PlaceOKE
