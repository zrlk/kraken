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
  -- The kernel decides only that some placed symbol lies below the code (no `mergeSort`, which
  -- `placeBelow` uses and the kernel does not reduce); `placeBelow_spec` does the rest.
  have H : ((Scc.Sem.loadSyms Λe outLit.secs.rodata).any fun p => decide (p.2 < Λe.code.lo)) = true := by
    decide +kernel
  obtain ⟨p, hp, hlt⟩ := List.any_eq_true.mp H
  have hb : p ∈ Scc.Sem.symsBelow Λe.code.lo (Scc.Sem.loadSyms Λe outLit.secs.rodata) :=
    Scc.Cert.PlaceSyms.mem_symsBelow.2 ⟨hp, of_decide_eq_true hlt⟩
  have h1 := Scc.Cert.PlaceSyms.exeStart_le_of_mem hb
  have h2 := (Scc.Cert.PlaceSyms.placeBelow_spec (Directive.byteArray (.mk #[])) Directive.label Λe.code.lo
    (Scc.Sem.loadSyms Λe outLit.secs.rodata)).2
  have h3 := of_decide_eq_true hlt
  unfold Scc.Cert.Rt.A64.belowLen
  rcases hl : Scc.Sem.placeBelow (Directive.byteArray (.mk #[])) Directive.label Λe.code.lo
      (Scc.Sem.loadSyms Λe outLit.secs.rodata) with _ | ⟨x, xs⟩
  · rw [hl] at h2
    simp only [List.map_nil, List.sum_nil, Nat.zero_add] at h2
    omega
  · simp

end Spike.Test.Ret0LinkedA64Pfx
