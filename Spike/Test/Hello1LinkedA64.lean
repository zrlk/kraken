import Spike.Test.Cert.A64Hello1Cert
import Scc.Test.ElfTest
import Scc.Cert.E2EA64

/-!
# `hello1.w` on AArch64 at the linked executable's layout (placement only)

`hello1.w` is outside `Accepted0` (`SccCertificate.prog_not_accepted`): it is
**uncertified**, and no correctness theorem is stated for it, here or
anywhere. This file is a placement test only.

`Scc/Test/elf/hello1a64/hello1` is `hello1.w`'s certificate text
(`SccCertificate.asm`, written verbatim to `hello1.s` next to it, checked
below), assembled and linked as `Scc/Test/run.sh` links AArch64 binaries:
`clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static
-fuse-ld=lld`, `ld.lld`'s default script, which puts `.rodata` (the stack
map `scc_stackmap`, whose `.quad`s name code labels) below `.text` and adds
a build-id note. It runs (`qemu-aarch64`), prints `Hello, world` and exits
with 0.

The emitter opens `.text` with `.p2align 4`, so `ld.lld` puts it at
`0x210410` and the reader accepts the file (checked below; with the old
`.p2align 2` it was at `0x210408` and refused by `Link.wfB`, which asks each
region to be 16-aligned). Its layout `Λe` is read off the file at
elaboration time (`scc_elf_layout%`, fail closed). At `Λe`, each by
`decide +kernel`:

* A1–A9 of the certificate's output hold (`hello1_a1_9`), A2 with `.rodata`,
  its label `scc_stackmap` and the stack map's `.quad`s of code labels below
  the code (`Link.A64.loadOk`: `symsAround`, `noClash`);
* the code fills `.text` exactly (`hello1_codeFills`, `E2E.A64.codeFills`);
* A11 fails (`hello1_a11`): `hello1`'s `.setup` tail has no `MainCode` yet,
  as at the static link (`SccCertificate.prog_placeOK_11`);
* so `placeOKAt` is `false` at `Λe` (`hello1_not_placeOKAt`, through
  `placeOKAt_eq_false_of_a11`), and so is the end-to-end guard `e2eOk`:
  every component but the known fragment limit A11 passes at a real
  `ld.lld` layout. (AArch64's components are A1–A9 and A11.)

Independent of the fixture: the loader check A2 refuses `hello1`'s output
with its `.rodata` label renamed like a code label once `.rodata` lies below
the code (`Link.A64.noClash`), and accepts it with `.rodata` above the code
(the last tests).
-/

namespace Spike.Test.Hello1LinkedA64

open Scc.Cert.PlaceOK
open SccCertificate (asm out outLit out_eq placeCfg)

-- The executable is the one linked (evaluation, not a proof).
/-- info: 60378da86d54bf83b96b4f0880fde7bb3d5a6885a084d5e257ef1ffb4177f313 -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile "Scc/Test/elf/hello1a64/hello1"))

-- The text linked is the certificate's `asm`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/hello1a64/hello1.s") == asm)

-- `.text` is 16-aligned (at `0x210410`): the reader accepts the executable.
/-- info: accepted -/
#guard_msgs in
#eval Scc.Test.Elf.verdict "Scc/Test/elf/hello1a64/hello1" pure

/-! ### The placement check at the executable's layout -/

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`:
read at elaboration time, the reader evaluated by the elaborator). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/hello1a64/hello1"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == "60378da86d54bf83b96b4f0880fde7bb3d5a6885a084d5e257ef1ffb4177f313"

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- `ld.lld`'s default layout: `.rodata`, and the data symbol `scc_stackmap` in it, below the code.
#guard Λe.rodata.lo + Λe.rodata.size ≤ Λe.code.lo
#guard Λe.code.lo % 16 == 0
#guard (Scc.Sem.loadSyms Λe outLit.secs.rodata).filter (·.2 < Λe.code.lo) == [("scc_stackmap", Λe.rodata.lo)]

/-- **A1–A9 of `hello1`'s output at `Λe`** (kernel-checked). -/
theorem hello1_a1_9 : (A64.a1 outLit ⟨Λe⟩ && A64.a2 outLit ⟨Λe⟩ && A64.a3 outLit ⟨Λe⟩ &&
    A64.a4 placeCfg outLit ⟨Λe⟩ && A64.a5 outLit ⟨Λe⟩ && A64.a6 outLit ⟨Λe⟩ && A64.a7 outLit ⟨Λe⟩ &&
    A64.a8 outLit ⟨Λe⟩ && A64.a9 outLit ⟨Λe⟩) = true := by
  decide +kernel

/-- **The code fills `.text`** at `Λe` (kernel-checked). -/
theorem hello1_codeFills : Scc.Cert.E2E.A64.codeFills outLit Λe = true := by
  decide +kernel

/-- **A11 fails at `Λe`** (kernel-checked): the `.setup` tail. -/
theorem hello1_a11 : A64.a11 outLit ⟨Λe⟩ = false := by
  decide +kernel

/-- **`placeOKAt` of `hello1`'s output is `false` at `Λe`**, by A11 only. -/
theorem hello1_not_placeOKAt : A64.placeOKAt placeCfg Λe out = false := by
  rw [out_eq]
  exact A64.placeOKAt_eq_false_of_a11 hello1_a11

-- And by evaluation: the end-to-end guard fails, for `placeOKAt`.
#guard !Scc.Cert.E2E.A64.e2eOk placeCfg Λe outLit

/-! ### A `.rodata` label named like a code label, below the code -/

/-- The static link's layout (`tablesOf`). -/
abbrev Λs : Scc.Sem.Layout := (A64.tablesOf placeCfg outLit).Λ

/-- `Λs` with `.rodata` moved below the code, where `ld.lld` puts it. -/
abbrev Λlo : Scc.Sem.Layout := { Λs with rodata := ⟨0x200000, 0x1000⟩ }

/-- `scc_stackmap` renamed `_start`, the program's first code label. -/
def ren : Kraken.DataImage.Item → Kraken.DataImage.Item
  | .label "scc_stackmap" => .label "_start"
  | i => i

/-- `hello1`'s output with its `.rodata` label renamed (`ren`). -/
def outRen : A64.Out := { outLit with secs := { outLit.secs with rodata := outLit.secs.rodata.map ren } }

-- `.rodata` and its one label `scc_stackmap` below the code at `Λlo`; `_start` a code label.
#guard Λlo.rodata.lo + Λlo.rodata.size ≤ Λlo.code.lo
#guard (Scc.Sem.loadSyms Λlo outLit.secs.rodata).filter (·.2 < Λlo.code.lo) == [("scc_stackmap", 0x200000)]
#guard (Scc.Cert.Link.A64.codeOf Λlo.code.lo outLit.prog "_start").isSome

-- A2 accepts the output with `.rodata` below the code; renamed like a code label it is refused,
-- by `noClash` (its first half: the label's cell would come before the code and shadow `_start`).
-- With `.rodata` above the code the renamed output is accepted: the code label comes first.
#guard A64.a2 outLit ⟨Λlo⟩
#guard !A64.a2 outRen ⟨Λlo⟩
#guard !Scc.Cert.Link.A64.noClash Λlo.code.lo outRen.prog (Scc.Sem.loadSyms Λlo outRen.secs.rodata)
#guard A64.a2 outRen ⟨Λs⟩

end Spike.Test.Hello1LinkedA64
