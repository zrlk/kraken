import Spike.Test.HelloLinkedX64

/-! # `hello.w` on x86-64: a part of placement component A2 at `Λ1`

A2 split into the parts of `Scc.Cert.Link.X64.loadOk_ofR`, the abort labels and the image (as the
certificate's `prog_placeOK_2*`), one `decide +kernel` per module (the kernel's cache is per
declaration); assembled in `Spike/Test/HelloLinkedX64L1A2.lean`. -/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.HelloPh.RootLit (oH)

/-- **A2 at `Λ1`: `.rodata` and the data symbols against the layout and the code** (kernel-checked). -/
theorem hello1_a2rest :
    (Scc.Sem.rodataFits Λ1 oH.secs.rodata && Scc.Sem.symsAgree Λ1 oH.secs.rodata &&
      Scc.Sem.symsAbove Λ1.code.lo (Scc.Sem.X64.codeEnd Λ1.code.lo oH.prog) (Scc.Sem.loadSyms Λ1 oH.secs.rodata) &&
      Scc.Cert.Link.X64.symsAround Λ1.code.lo oH.prog (Scc.Sem.loadSyms Λ1 oH.secs.rodata) &&
      Scc.Cert.Link.X64.noClash Λ1.code.lo oH.prog (Scc.Sem.loadSyms Λ1 oH.secs.rodata) &&
      decide (Scc.Sem.X64.codeEnd Λ1.code.lo oH.prog < 2 ^ 64)) = true := by
  decide +kernel

end Spike.Test.HelloLinkedX64
