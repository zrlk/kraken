import Scc.Test.ElfTest
import Scc.Cert.E2EX64
import Spike.Test.HelloLinkedX64

/-!
# `hello.w` on x86-64: the linked executable and its layout `Λe`

The x86-64 twin of `Spike/Test/HelloLinkedA64Elf.lean`.

`Scc/Test/elf/hellox64/hello` is hello's listing `SccCode.helloAsm` (written verbatim to `hello.s` next to it,
checked below), assembled by GNU `as` and linked by GNU `ld -static` with its default script, as
`Scc/Test/run.sh` links x86-64 binaries and as `Scc/Test/elf.sh` records. It runs, prints `Hello, world` and
exits with 0.

This module holds **the executable's path and SHA-256, in one place** (`path`, `sha`): the layout `Λe` is read off
the file at elaboration time (`scc_elf_layout%`, fail closed) and checked against `sha`. The placement components at
`Λe` are decided in `HelloLinkedX64A1` … `HelloLinkedX64A13` (one `decide +kernel` per module), the layout facts
and `layoutEX_e` in `HelloLinkedX64Le`.

Unlike AArch64 (`.text` forced to `WakePh.lo`, `.rodata` below it), the link uses `ld`'s default script: `.text`
at `0x401000` (`X64.HelloPh.lo`), `.rodata` and every data symbol above the code. Unlike x86-64 wake
(`WakeLinkedX64Elf`, checked against the certificate's `asm` and `outLit`), the text and the output are the
listing's (`SccCode.helloText`, `RootLit.oH`): this module does not import hello's certificate.
-/

namespace Spike.Test.HelloLinkedX64

open Spike.Lib.X64.HelloPh.RootLit (oH pcfgH)

/-- The executable's path. -/
def path : String := "Scc/Test/elf/hellox64/hello"

/-- The executable's SHA-256. -/
def sha : String := "8fb245f06bdc23695fb87a76688e9f66cfe38e95d0f0eab3d81fa637e8842ef8"

-- The executable is the one linked (evaluation, not a proof).
/-- info: true -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile path) == sha)

-- The text linked is the listing, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile (path ++ ".s")) == SccCode.helloText)

-- The reader accepts the executable.
/-- info: accepted -/
#guard_msgs in
#eval Scc.Test.Elf.verdict path pure

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`: read at elaboration time, the reader
evaluated by the elaborator). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/hellox64/hello"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == sha

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- `ld`'s default layout: `.text` at `0x401000`, `.rodata` and every data symbol above the code.
#guard Λe.code.lo == 0x401000
#guard Λe.code.lo % 16 == 0
#guard Λe.code.lo + Λe.code.size ≤ Λe.rodata.lo
#guard (Scc.Sem.loadSyms Λe oH.secs.rodata).all (Λe.code.lo ≤ ·.2)

-- Every placement component holds at `Λe`, and the listing fills the code region (evaluation; each component is
-- kernel-checked in its own module).
open Scc.Cert.PlaceOK.X64 Scc.Cert.Spawn.X64 in
/-- info: [true, true, true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval [a1 oH ⟨Λe⟩, a2 oH ⟨Λe⟩, a3 oH ⟨Λe⟩, a4 pcfgH oH ⟨Λe⟩, a5 oH ⟨Λe⟩, a6 oH ⟨Λe⟩, a7 oH ⟨Λe⟩, a8 oH ⟨Λe⟩,
  a9 oH ⟨Λe⟩, a11' oH ⟨Λe⟩, a12code' oH, a12ph' oH ⟨Λe⟩, a13 oH ⟨Λe⟩, Scc.Cert.E2E.X64.codeFills oH Λe]

end Spike.Test.HelloLinkedX64
