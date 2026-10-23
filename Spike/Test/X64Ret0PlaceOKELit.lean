import Scc.Cert.PlaceDataX64
import Scc.Cert.OutLitX64
import Spike.Lib.Ret0Src
import Spike.Lib.X64Ret0Code

/-!
# `ret0.w`'s x86-64 output as a literal

The x86-64 twin of `Spike/Test/A64Ret0PlaceOKELit.lean`: scc's x86-64
output for `ret0.w` (`ret0O`, computed by `lowerAll` and `Out.ofEmitted` at
the assembler's sizes and label offsets, `SccCode.ret0Asm`) and its value
written out at elaboration time (`ret0L`, `scc_lit%`), equal by one kernel
run of the pipeline (`ret0_out_eq`), in a file of its own:
`Spike/Test/X64Ret0PlaceOKE.lean` decides `PlaceOK`'s parts on the literal,
one declaration each.
-/

namespace Spike.Test.X64Ret0PlaceOKE

set_option maxRecDepth 100000

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- scc's x86-64 output for `ret0.w` as `PlaceOK` reads it, at the
assembler's sizes and label offsets. -/
def ret0O : Out :=
  Out.ofEmitted (Scc.Lower.X64.lowerAll { arch := .x64 } Spike.Lib.Ret0Src.ret0Src)
    SccCode.ret0Asm.sizes SccCode.ret0Asm.labelOffs

/-- `ret0O` as a literal: its value computed at elaboration time. -/
def ret0L : Out := scc_lit% ret0O

/-- The literal is the pipeline's output (one kernel run of `lowerAll`). -/
theorem ret0_out_eq : ret0O = ret0L := by kernel_rfl

end Spike.Test.X64Ret0PlaceOKE
