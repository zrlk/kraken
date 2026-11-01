import Spike.Test.HelloLinkedA64Elf

/-! # `hello.w` on AArch64: placement component A1 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/HelloLinkedA64Elf.lean`). -/

namespace Spike.Test.HelloLinkedA64

open Spike.Lib.A64.HelloPh.RootLit (pcfgH oH)

/-- **A1 of hello's output at `Λe`** (kernel-checked). -/
theorem hello_a1 : Scc.Cert.PlaceOK.A64.a1 oH ⟨Λe⟩ = true := by decide +kernel

end Spike.Test.HelloLinkedA64
