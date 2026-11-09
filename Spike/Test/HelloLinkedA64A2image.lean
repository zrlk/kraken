import Spike.Test.HelloLinkedA64Elf
import Scc.Cert.A2StageA64

/-! # `hello.w` on AArch64: a part of placement component A2 at `Λe`

A2 split into its keyed parts (`Scc.Cert.PlaceOK.A64.a2fast`), one `decide +kernel` per module
(the kernel's cache is per declaration); assembled in `Spike/Test/HelloLinkedA64A2.lean`. -/

namespace Spike.Test.HelloLinkedA64

open Spike.Lib.A64.HelloPh.RootLit (oH)

/-- **A2 at `Λe`: the image, keyed** (kernel-checked). -/
theorem hello_a2image : Scc.Cert.PlaceOK.A64.imageInK oH.prog oH.secs Λe = true := by decide +kernel

end Spike.Test.HelloLinkedA64
