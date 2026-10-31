import Spike.Test.WakeLinkedX64Elf

/-! # `wake.w` on x86-64: placement component A1 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/WakeLinkedX64Elf.lean`). -/

namespace Spike.Test.WakeLinkedX64

open SccCertificate (outLit placeCfg)

/-- **A1 of wake's output at `Λe`** (kernel-checked). -/
theorem wake_a1 : Scc.Cert.PlaceOK.X64.a1 outLit ⟨Λe⟩ = true := by decide +kernel

end Spike.Test.WakeLinkedX64
