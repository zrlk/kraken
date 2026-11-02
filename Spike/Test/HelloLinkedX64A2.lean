import Spike.Test.HelloLinkedX64Elf

/-! # `hello.w` on x86-64: placement component A2 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/HelloLinkedX64Elf.lean`). Unlike AArch64, whose `PlaceW`
subset is A1, A2, A4, A6, A8, x86-64's `PlaceWX` takes every component of `placeOK2At`. -/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.HelloPh.RootLit (oH pcfgH)

/-- **A2 of hello's output at `Λe`** (kernel-checked). -/
theorem hello_a2 : Scc.Cert.PlaceOK.X64.a2 oH ⟨Λe⟩ = true := by decide +kernel

end Spike.Test.HelloLinkedX64
