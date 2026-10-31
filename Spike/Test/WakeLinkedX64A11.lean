import Spike.Test.WakeLinkedX64Elf

/-! # `wake.w` on x86-64: placement component A11 at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/WakeLinkedX64Elf.lean`). -/

namespace Spike.Test.WakeLinkedX64

open SccCertificate (outLit placeCfg)

/-- **A11' (the spawn-aware `.setup` tail) of wake's output at `Λe`** (kernel-checked). -/
theorem wake_a11 : Scc.Cert.Spawn.X64.a11' outLit ⟨Λe⟩ = true := by decide +kernel

end Spike.Test.WakeLinkedX64
