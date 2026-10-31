import Spike.Test.WakeLinkedX64Elf

/-! # `wake.w` on x86-64: placement component A8 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/WakeLinkedX64Elf.lean`). -/

namespace Spike.Test.WakeLinkedX64

open SccCertificate (outLit placeCfg)

/-- **A8 of wake's output at `Λe`** (kernel-checked). -/
theorem wake_a8 : Scc.Cert.PlaceOK.X64.a8 outLit ⟨Λe⟩ = true := by decide +kernel

end Spike.Test.WakeLinkedX64
