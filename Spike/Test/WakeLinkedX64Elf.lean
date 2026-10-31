import Spike.Test.Cert.X64WakeCert
import Scc.Test.ElfTest
import Scc.Cert.SpawnX64
import Scc.Cert.E2EX64

/-!
# `wake.w` on x86-64: the linked executable and its layout `Λe`

The x86-64 twin of `Spike/Test/WakeLinkedA64Elf.lean`.

`Scc/Test/elf/wakex64/wake` is `wake.w`'s certificate text
(`SccCertificate.asm`, written verbatim to `wake.s` next to it, checked
below), assembled by GNU `as` (object `wake.o`) and linked by GNU
`ld -static` with its default script, as `Scc/Test/run.sh` links x86-64
binaries (`Scc/Test/elf.sh --relink` rebuilds it). It runs and exits with 0.
The executable is pinned by (`path`, `sha`): the layout `Λe` is read off the
file at elaboration time (`scc_elf_layout%`, fail closed) and checked against
`sha`. The placement components at `Λe` are decided in `WakeLinkedX64A1` …
(one `decide +kernel` per module).

`wake.w` is outside `Accepted0` (`SccCertificate.prog_not_accepted`).
-/

namespace Spike.Test.WakeLinkedX64

open SccCertificate (asm outLit)

/-- The executable's path. -/
def path : String := "Scc/Test/elf/wakex64/wake"

/-- The executable's SHA-256. -/
def sha : String := "4e03ea547bb951eadf5d644865f05acbe8a7b29ba0f36f50fc4a0137a1ed243e"

-- The executable is the one linked (evaluation, not a proof).
/-- info: true -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile path) == sha)

-- The text linked is the certificate's `asm`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile (path ++ ".s")) == asm)

-- The reader accepts the executable.
/-- info: accepted -/
#guard_msgs in
#eval Scc.Test.Elf.verdict path pure

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`:
read at elaboration time, the reader evaluated by the elaborator). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/wakex64/wake"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == sha

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- `ld`'s default layout: `.text` at `0x401000`, `.rodata` and every data symbol above the code.
#guard Λe.code.lo == 0x401000
#guard Λe.code.lo % 16 == 0
#guard Λe.code.lo + Λe.code.size ≤ Λe.rodata.lo
#guard (Scc.Sem.loadSyms Λe outLit.secs.rodata).all (Λe.code.lo ≤ ·.2)

-- Every placement component holds at `Λe` (evaluation; each is kernel-checked in its own module).
open Scc.Cert.PlaceOK.X64 Scc.Cert.Spawn.X64 in
/-- info: [true, true, true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval [a1 outLit ⟨Λe⟩, a2 outLit ⟨Λe⟩, a3 outLit ⟨Λe⟩, a4 SccCertificate.placeCfg outLit ⟨Λe⟩,
  a5 outLit ⟨Λe⟩, a6 outLit ⟨Λe⟩, a7 outLit ⟨Λe⟩, a8 outLit ⟨Λe⟩, a9 outLit ⟨Λe⟩, a11' outLit ⟨Λe⟩,
  a12code' outLit, a12ph' outLit ⟨Λe⟩, a13 outLit ⟨Λe⟩, Scc.Cert.E2E.X64.codeFills outLit Λe]

end Spike.Test.WakeLinkedX64
