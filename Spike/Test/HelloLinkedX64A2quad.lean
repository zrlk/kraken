import Spike.Test.HelloLinkedX64Elf

/-! # `hello.w` on x86-64: a part of placement component A2 at `Λe`

A2 split into the parts of `Scc.Cert.Link.X64.loadOk_ofR`, the abort labels and the image (as the
certificate's `prog_placeOK_2*`), one `decide +kernel` per module (the kernel's cache is per
declaration); assembled in `Spike/Test/HelloLinkedX64A2.lean`. -/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.HelloPh.RootLit (oH)

/-- **A2 at `Λe`: the `.quad` labels resolve (code labels keyed, `Scc.Cert.Rt.X64.codeT_eq`)** (kernel-checked). -/
theorem hello_a2quad :
    Scc.Sem.quadsResolve Λe oH.secs.rodata (Scc.Sem.X64.codeLabel Λe.code.lo oH.prog) = true := by
  rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

end Spike.Test.HelloLinkedX64
