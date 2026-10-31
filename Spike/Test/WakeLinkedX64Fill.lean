import Spike.Test.WakeLinkedX64Elf

/-! # `wake.w` on x86-64: placement component Fill at the executable's layout `Λe`

One `decide +kernel` per module (`Spike/Test/WakeLinkedX64Elf.lean`). -/

namespace Spike.Test.WakeLinkedX64

open SccCertificate (outLit placeCfg)

/-- **the code filling `.text` of wake's output at `Λe`** (kernel-checked). -/
theorem wake_codeFills : Scc.Cert.E2E.X64.codeFills outLit Λe = true := by decide +kernel

end Spike.Test.WakeLinkedX64
