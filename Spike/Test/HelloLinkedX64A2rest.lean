import Spike.Test.HelloLinkedX64Elf

/-! # `hello.w` on x86-64: a part of placement component A2 at `Λe`

A2 split into the parts of `Scc.Cert.Link.X64.loadOk_ofR`, the abort labels and the image (as the
certificate's `prog_placeOK_2*`), one `decide +kernel` per module (the kernel's cache is per
declaration); assembled in `Spike/Test/HelloLinkedX64A2.lean`. -/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.HelloPh.RootLit (oH)

/-- **A2 at `Λe`: `.rodata` and the data symbols against the layout and the code** (kernel-checked). -/
theorem hello_a2rest :
    (Scc.Sem.rodataFits Λe oH.secs.rodata && Scc.Sem.symsAgree Λe oH.secs.rodata &&
      Scc.Sem.symsAbove Λe.code.lo (Scc.Sem.X64.codeEnd Λe.code.lo oH.prog) (Scc.Sem.loadSyms Λe oH.secs.rodata) &&
      Scc.Cert.Link.X64.symsAround Λe.code.lo oH.prog (Scc.Sem.loadSyms Λe oH.secs.rodata) &&
      Scc.Cert.Link.X64.noClash Λe.code.lo oH.prog (Scc.Sem.loadSyms Λe oH.secs.rodata) &&
      decide (Scc.Sem.X64.codeEnd Λe.code.lo oH.prog < 2 ^ 64)) = true := by
  decide +kernel

end Spike.Test.HelloLinkedX64
