import Spike.Test.HelloLinkedA64
import Spike.Lib.HelloAssemblyI

/-! # `hello.w` on AArch64: the layout facts in the root's form

`hinit2` and `hA13_e` at `Le` are `RootLit.hello_root_lit`'s `hinit2`/`hA13` at `Λ0 := Λe`, `i0 := i0M Λe`
(`LH hp (IH0)`), by ascription. -/

namespace Spike.Test.HelloLinkedA64

example : (Spike.Lib.A64.PhRec.m0Of (Spike.Lib.HelloAssemblyI.LH placeW_e
    (Spike.Lib.A64.HelloPh.C0S.immsH Λe (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λe))).Λ
    Spike.Lib.A64.HelloPh.RootLit.oH.prog Spike.Lib.A64.HelloPh.RootLit.oH.secs).initVal
    ⟨Spike.Lib.HelloGOf2H.lim2AH (Spike.Lib.HelloAssemblyI.LH placeW_e
      (Spike.Lib.A64.HelloPh.C0S.immsH Λe (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λe))), 8⟩ = 0 := hinit2

example : Scc.Cert.Spawn.A64.a13data (Spike.Lib.HelloAssemblyI.LH placeW_e
    (Spike.Lib.A64.HelloPh.C0S.immsH Λe (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λe))).Λ
    Spike.Lib.A64.HelloPh.RootLit.oH.prog Spike.Lib.A64.HelloPh.RootLit.oH.secs = true := hA13_e

end Spike.Test.HelloLinkedA64
