import Spike.Test.HelloLinkedA64Elf

/-! # `hello.w` on AArch64: placement component A8 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/HelloLinkedA64Elf.lean`). -/

namespace Spike.Test.HelloLinkedA64

open Spike.Lib.A64.HelloPh.RootLit (pcfgH oH)

/-- **A8 of hello's output at `Λe`** (kernel-checked). -/
theorem hello_a8 : Scc.Cert.PlaceOK.A64.a8 oH ⟨Λe⟩ = true := by decide +kernel

end Spike.Test.HelloLinkedA64
