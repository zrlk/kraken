import Spike.Test.WakeLinkedX64Elf

/-! # `wake.w` on x86-64: placement component A13 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/WakeLinkedX64Elf.lean`). -/

namespace Spike.Test.WakeLinkedX64

open SccCertificate (outLit placeCfg)

/-- **A13 (the spawn sites and their data) of wake's output at `Λe`** (kernel-checked). -/
theorem wake_a13 : Scc.Cert.Spawn.X64.a13 outLit ⟨Λe⟩ = true := by decide +kernel

end Spike.Test.WakeLinkedX64
