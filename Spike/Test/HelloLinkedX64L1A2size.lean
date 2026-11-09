import Spike.Test.HelloLinkedX64

/-! # `hello.w` on x86-64: a part of placement component A2 at `Λ1`

A2 split into the parts of `Scc.Cert.Link.X64.loadOk_ofR`, the abort labels and the image (as the
certificate's `prog_placeOK_2*`), one `decide +kernel` per module (the kernel's cache is per
declaration); assembled in `Spike/Test/HelloLinkedX64L1A2.lean`. -/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.HelloPh.RootLit (oH)

/-- **A2 at `Λ1`: the code sizes against the assembler's label offsets** (kernel-checked). -/
theorem hello1_a2size :
    Scc.Cert.Link.X64.sizeOkW (Int64.ofNat Λ1.code.lo) oH.prog oH.labelOffs = true := by
  decide +kernel

end Spike.Test.HelloLinkedX64
