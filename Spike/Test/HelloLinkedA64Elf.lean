import Scc.Test.ElfTest
import Spike.Lib.A64HelloRootLit

/-!
# `hello.w` on AArch64: the linked executable and its layout `Λe`

`Scc/Test/elf/helloa64/hello` is hello's listing `SccCode.helloAsm` (written verbatim to `hello.s` next to it,
checked below), assembled and linked as `Scc/Test/run.sh` links hello on AArch64 (`Scc/Test/a64link.sh`: `clang
--target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld` with `.text` pinned at `0x210550`
(`WakePh.lo`, the base of hello's phase chain), the build-id note and `.rodata` at `ld.lld`'s default addresses below
it), as `Scc/Test/elf.sh` records. It runs (`qemu-aarch64`), prints `Hello, world` and exits with 0.

This module holds **the executable's path and SHA-256, in one place** (`path`, `sha`): the layout `Λe` is read off
the file at elaboration time (`scc_elf_layout%`, fail closed) and checked against `sha`. The placement components at
`Λe` are decided in `HelloLinkedA64A1` … `HelloLinkedA64A8` (one `decide +kernel` per module, each ≤ 1.2 GB
RssAnon), the layout facts in `HelloLinkedA64`, the root's instance in `HelloLinkedA64Root`.
-/

namespace Spike.Test.HelloLinkedA64

/-- The executable's path. -/
def path : String := "Scc/Test/elf/helloa64/hello"

/-- The executable's SHA-256. -/
def sha : String := "3ccb878eb218d2988d1a564d7b414e7e6872b6024c0d71fa3079330055dbd2d3"

-- The executable is the one linked (evaluation, not a proof).
/-- info: true -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile path) == sha)

-- The text linked is the listing, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile (path ++ ".s")) == SccCode.helloAsm)

-- `.text` is 16-aligned: the reader accepts the executable.
/-- info: accepted -/
#guard_msgs in
#eval Scc.Test.Elf.verdict path pure

/-- The layout of the linked executable and its SHA-256. -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/helloa64/hello"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == sha

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- `.text` at `0x210550` (`WakePh.lo`), 16-aligned, `.rodata` below it.
#guard Λe.code.lo == 0x210550
#guard Λe.code.lo % 16 == 0
#guard Λe.rodata.lo + Λe.rodata.size ≤ Λe.code.lo

end Spike.Test.HelloLinkedA64
