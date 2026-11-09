import Spike.Test.HelloLinkedA64A2load
import Spike.Test.HelloLinkedA64A2abort
import Spike.Test.HelloLinkedA64A2image

/-! # `hello.w` on AArch64: placement component A2 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/HelloLinkedA64Elf.lean`); A2 itself from its keyed parts
(`HelloLinkedA64A2load`, `…A2abort`, `…A2image`; `Scc.Cert.PlaceOK.A64.a2_of_fast`). -/

namespace Spike.Test.HelloLinkedA64

open Spike.Lib.A64.HelloPh.RootLit (pcfgH oH)

/-- **A2 of hello's output at `Λe`** (kernel-checked). -/
theorem hello_a2 : Scc.Cert.PlaceOK.A64.a2 oH ⟨Λe⟩ = true :=
  Scc.Cert.PlaceOK.A64.a2_of_fast (by
    simp only [Scc.Cert.PlaceOK.A64.a2fast, hello_a2load, hello_a2abort, hello_a2image, Bool.and_self])

end Spike.Test.HelloLinkedA64
