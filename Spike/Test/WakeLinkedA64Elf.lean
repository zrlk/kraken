import Spike.Test.Cert.A64WakeCert
import Scc.Test.ElfTest

/-!
# `wake.w` on AArch64: the linked executable and its layout `Λe`

`Scc/Test/elf/wakea64/wake` is `wake.w`'s certificate text
(`SccCertificate.asm` of `Spike/Test/Cert/A64WakeCert.lean`, written verbatim
to `wake.s` next to it, checked below), assembled and linked as
`Scc/Test/run.sh` links AArch64 binaries: `clang --target=aarch64-linux-gnu
-march=armv8.4-a -nostdlib -static -fuse-ld=lld`, `ld.lld`'s default script
(`.rodata` below `.text`, a build-id note). It runs (`qemu-aarch64`), prints
nothing and exits with 0.

This module holds **the executable's path and SHA-256, in one place**
(`path`, `sha`): the layout `Λe` is read off the file at elaboration time
(`scc_elf_layout%`, fail closed) and checked against `sha`. The placement
components at `Λe` are decided in `WakeLinkedA64A1` … `WakeLinkedA64A8` (one
`decide +kernel` per module: each peaks near 3.6 GB), the root's instance in
`WakeLinkedA64`.
-/

namespace Spike.Test.WakeLinkedA64

open SccCertificate (asm)

/-- The executable's path. -/
def path : String := "Scc/Test/elf/wakea64/wake"

/-- The executable's SHA-256. -/
def sha : String := "a5cd1cd92de17388dfbda041fb069ea874e180324f7af8714ed4cb02c01de223"

-- The executable is the one linked (evaluation, not a proof).
/-- info: true -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile path) == sha)

-- The text linked is the certificate's `asm`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile (path ++ ".s")) == asm)

-- `.text` is 16-aligned: the reader accepts the executable.
/-- info: accepted -/
#guard_msgs in
#eval Scc.Test.Elf.verdict path pure

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`:
read at elaboration time, the reader evaluated by the elaborator). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/wakea64/wake"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == sha

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- `ld.lld`'s layout: `.text` at `0x210550` (`WakePh.lo`), 16-aligned, `.rodata` below it.
#guard Λe.code.lo == 0x210550
#guard Λe.code.lo % 16 == 0
#guard Λe.rodata.lo + Λe.rodata.size ≤ Λe.code.lo

end Spike.Test.WakeLinkedA64
