import Spike.Test.Ret0LinkedA64GBase

/-!
# `ret0.w` after the granule pass: the placement components at the linked layout

A1–A9, A11 and A12 of the output with the tail at `ΛG`, each by
`decide +kernel` (A2 by its keyed form, `Scc/Cert/A2StageA64.lean`); split
from `Ret0LinkedA64G` to bound one module's memory.
-/

namespace Spike.Test.Ret0LinkedA64G

open Scc.Cert.PlaceOK
open SccCertificate (outLit placeCfg)

theorem ret0G_a1 : A64.a1 outF ⟨ΛG⟩ = true := by decide +kernel
theorem ret0G_a2 : A64.a2 outF ⟨ΛG⟩ = true := A64.a2_of_fast (by decide +kernel)
theorem ret0G_a3 : A64.a3 outF ⟨ΛG⟩ = true := by decide +kernel
theorem ret0G_a4 : A64.a4 placeCfg outF ⟨ΛG⟩ = true := by decide +kernel
theorem ret0G_a5 : A64.a5 outF ⟨ΛG⟩ = true := by decide +kernel
theorem ret0G_a6 : A64.a6 outF ⟨ΛG⟩ = true := by decide +kernel
theorem ret0G_a7 : A64.a7 outF ⟨ΛG⟩ = true := by decide +kernel
theorem ret0G_a8 : A64.a8 outF ⟨ΛG⟩ = true := by decide +kernel
theorem ret0G_a9 : A64.a9 outF ⟨ΛG⟩ = true := by decide +kernel
theorem ret0G_a11 : A64.a11 outF ⟨ΛG⟩ = true := by decide +kernel
theorem ret0G_a12 : A64.a12 outF ⟨ΛG⟩ = true := by decide +kernel

end Spike.Test.Ret0LinkedA64G
