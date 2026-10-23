import Scc.Cert.PlaceDataA64
import Scc.Cert.OutLitA64
import Spike.Lib.Ret0Src

/-!
# `ret0.w`'s output as a literal

scc's AArch64 output for `ret0.w` (`ret0O`, computed by `lowerAll` and
`Out.ofEmitted`) and its value written out at elaboration time (`ret0L`,
`scc_lit%`), equal by one kernel run of the pipeline (`ret0_out_eq`), in a
file of its own: `Spike/Test/A64Ret0PlaceOKE.lean` decides `PlaceOK`'s parts
on the literal, each well within the kernel's memory, apart from the
pipeline's run (peak RssAnon about 2.9 GB here, under 1 GB per part there).
-/

namespace Spike.Test.A64Ret0PlaceOKE

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- scc's AArch64 output for `ret0.w` as `PlaceOK` reads it. -/
def ret0O : Out := Out.ofEmitted (Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Ret0Src.ret0Src)

/-- `ret0O` as a literal: its value computed at elaboration time. -/
def ret0L : Out := scc_lit% ret0O

/-- The literal is the pipeline's output (one kernel run of `lowerAll`). -/
theorem ret0_out_eq : ret0O = ret0L := by kernel_rfl

end Spike.Test.A64Ret0PlaceOKE
