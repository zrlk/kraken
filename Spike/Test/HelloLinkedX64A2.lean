import Spike.Test.HelloLinkedX64A2size
import Spike.Test.HelloLinkedX64A2nodup
import Spike.Test.HelloLinkedX64A2quad
import Spike.Test.HelloLinkedX64A2rest
import Spike.Test.HelloLinkedX64A2abort
import Spike.Test.HelloLinkedX64A2image

/-! # `hello.w` on x86-64: placement component A2 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/HelloLinkedX64Elf.lean`); A2 itself from its parts
(`HelloLinkedX64A2size` … `HelloLinkedX64A2image`; `Scc.Cert.Link.X64.loadOk_ofR`,
`Scc.Cert.PlaceOK.X64.a2_of_partsAt`). Unlike AArch64, whose `PlaceW`
subset is A1, A2, A4, A6, A8, x86-64's `PlaceWX` takes every component of `placeOK2At`. -/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.HelloPh.RootLit (oH pcfgH)

/-- **A2 of hello's output at `Λe`** (kernel-checked). -/
theorem hello_a2 : Scc.Cert.PlaceOK.X64.a2 oH ⟨Λe⟩ = true :=
  Scc.Cert.PlaceOK.X64.a2_of_partsAt
    (Scc.Cert.Link.X64.loadOk_ofR hello_a2size hello_a2nodup hello_a2quad hello_a2rest) hello_a2abort hello_a2image

end Spike.Test.HelloLinkedX64
