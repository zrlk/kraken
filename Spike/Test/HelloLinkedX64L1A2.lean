import Spike.Test.HelloLinkedX64L1A2size
import Spike.Test.HelloLinkedX64L1A2nodup
import Spike.Test.HelloLinkedX64L1A2quad
import Spike.Test.HelloLinkedX64L1A2rest
import Spike.Test.HelloLinkedX64L1A2abort
import Spike.Test.HelloLinkedX64L1A2image

/-! # `hello.w` on x86-64: placement component A2 at the layout `Λ1`

One `decide +kernel` per module (`Spike/Test/HelloLinkedX64.lean`'s `Λ1`); A2 itself from its parts
(`HelloLinkedX64L1A2size` … `HelloLinkedX64L1A2image`; `Scc.Cert.Link.X64.loadOk_ofR`,
`Scc.Cert.PlaceOK.X64.a2_of_partsAt`). Unlike AArch64, whose `PlaceW`
subset is A1, A2, A4, A6, A8, x86-64's `PlaceWX` takes every component of `placeOK2At`. -/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.HelloPh.RootLit (oH pcfgH)

/-- **A2 of hello's output at `Λ1`** (kernel-checked). -/
theorem hello1_a2 : Scc.Cert.PlaceOK.X64.a2 oH ⟨Λ1⟩ = true :=
  Scc.Cert.PlaceOK.X64.a2_of_partsAt
    (Scc.Cert.Link.X64.loadOk_ofR hello1_a2size hello1_a2nodup hello1_a2quad hello1_a2rest) hello1_a2abort
    hello1_a2image

end Spike.Test.HelloLinkedX64
