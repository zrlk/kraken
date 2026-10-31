import Spike.Test.WakeLinkedX64Elf

/-! # `wake.w` on x86-64: placement component A12p at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/WakeLinkedX64Elf.lean`). -/

namespace Spike.Test.WakeLinkedX64

open SccCertificate (outLit placeCfg)

/-- **A12's phase part (spawn-aware) of wake's output at `Λe`** (kernel-checked). -/
theorem wake_a12p : Scc.Cert.Spawn.X64.a12ph' outLit ⟨Λe⟩ = true := by decide +kernel

end Spike.Test.WakeLinkedX64
