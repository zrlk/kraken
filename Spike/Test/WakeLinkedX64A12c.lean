import Spike.Test.WakeLinkedX64Elf

/-! # `wake.w` on x86-64: placement component A12c at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/WakeLinkedX64Elf.lean`). -/

namespace Spike.Test.WakeLinkedX64

open SccCertificate (outLit placeCfg)

/-- **A12's code part (spawn-aware) of wake's output at `Λe`** (kernel-checked). -/
theorem wake_a12c : Scc.Cert.Spawn.X64.a12code' outLit = true := by decide +kernel

end Spike.Test.WakeLinkedX64
