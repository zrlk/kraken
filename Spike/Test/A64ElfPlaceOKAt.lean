import Spike.Test.Cert.A64Ret0Cert
import Scc.Test.ElfTest
import Scc.Cert.E2EA64

/-!
# `placeOKAt` at the layout read off the linked AArch64 `ret0`

`Scc/Test/elf/a` is `ret0` (the certificate's text, the regions moved to the
end of `.bss`) linked by `ld.lld` with `ins.ld`. Its layout, read by the ELF
reader (`Scc.Test.Elf.a64`), passes `placeOKAt` with the certificate's
output: the code ends exactly at the end of `.text` (the shared end-to-end
guard `Scc.Cert.E2E.A64.e2eOk`, `placeOKAt` and `codeFills`), and the abort
labels are the runtime's (`abortStd`). Perturbed layouts fail closed.

The last test checks that the reader refuses a file whose entry point
(`e_entry`) is not the start of `.text`, where A1 puts `_start`.
-/

namespace Spike.Test.A64ElfPlaceOKAt

open Scc.Cert.PlaceOK

/-- The layout read off `Scc/Test/elf/a`. -/
def Λe : Scc.Sem.Layout := Scc.Test.Elf.a64.1

#guard Scc.Cert.E2E.A64.e2eOk SccCertificate.placeCfg Λe SccCertificate.outLit

-- A code region one instruction long: `codeFits` still passes, the end-to-end guard does not.
#guard A64.placeOKAt SccCertificate.placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size + 4⟩ }
  SccCertificate.outLit
#guard !Scc.Cert.E2E.A64.e2eOk SccCertificate.placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size + 4⟩ }
  SccCertificate.outLit

-- A code region one instruction short: `codeFits` fails.
#guard !A64.placeOKAt SccCertificate.placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size - 4⟩ }
  SccCertificate.outLit

-- An abort label that is not the runtime's: `abortStd` fails.
#guard !A64.placeOKAt SccCertificate.placeCfg
  { Λe with abortLbl := fun k => if k == .heap then "scc_rt_abort_overflow_exit" else Scc.Cert.Link.abortName k }
  SccCertificate.outLit

-- The code base off by one instruction: `_start` is not at it.
#guard !A64.placeOKAt SccCertificate.placeCfg { Λe with code := ⟨Λe.code.lo + 4, Λe.code.size⟩ }
  SccCertificate.outLit

-- `e_entry` (offset 24) moved off `.text`'s start: refused.
/-- info: the entry point 2163092 is not the start of .text (2163088) -/
#guard_msgs in
#eval Scc.Test.Elf.verdict "Scc/Test/elf/a" fun b => pure (Scc.Test.Elf.put64 b 24 0x210194)

end Spike.Test.A64ElfPlaceOKAt
