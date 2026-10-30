import Spike.Test.WakeLinkedA64Elf

/-! # `wake.w` on AArch64: placement component A4 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/WakeLinkedA64Elf.lean`). -/

namespace Spike.Test.WakeLinkedA64

open SccCertificate (outLit placeCfg)

/-- **A4 of wake's output at `Λe`** (kernel-checked). -/
theorem wake_a4 : Scc.Cert.PlaceOK.A64.a4 placeCfg outLit ⟨Λe⟩ = true := by decide +kernel

end Spike.Test.WakeLinkedA64
