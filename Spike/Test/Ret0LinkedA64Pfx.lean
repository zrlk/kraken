import Spike.Test.Ret0LinkedA64

/-!
# `Ret0LinkedA64` exercises the prefix

At the `ld.lld` executable's layout `Λe` the canonical loader places a data
symbol below the code: `scc_stackmap`, a `.rodata` label, reaches the loader
through `loadSyms` (the reader leaves `.rodata` labels out of `Λe.symbols`),
so the cells before the code (`belowLen`) are not empty and the runtime
layout's prefix is positive. Checked by evaluation and by the kernel.
-/

namespace Spike.Test.Ret0LinkedA64Pfx

open Spike.Test.Ret0LinkedA64 (Λe)
open SccCertificate (outLit)

-- The `.rodata` labels are not in `Λe.symbols`, but the loader places them: `scc_stackmap` below the code.
#guard !(Λe.symbols.any (·.1 == "scc_stackmap"))
#guard (Scc.Sem.loadSyms Λe outLit.secs.rodata).any fun p => p.1 == "scc_stackmap" && p.2 < Λe.code.lo

/-- The loader places cells before the code at `Λe` (kernel-checked). -/
theorem ret0_belowLen_pos :
    0 < Scc.Cert.Rt.A64.belowLen Λe.code.lo (Scc.Sem.loadSyms Λe outLit.secs.rodata) := by
  decide +kernel

end Spike.Test.Ret0LinkedA64Pfx
