import Spike.Test.Cert.A64Hello1Cert
import Scc.Test.ElfTest
import Scc.Cert.E2EA64

/-!
# `hello1.w` on AArch64 at the linked executable's layout

`hello1.w` is outside `Accepted0` (`SccCertificate.prog_not_accepted`) and
`certify.sh` does not certify it. Its correctness theorem `hello1_finalCA`
(`Spike/Test/A64Hello1FinalCA.lean`) is stated at this file's layout `Λe` and
uses the placement facts below.

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
* A11 holds (`hello1_a11`): `hello1`'s `.setup` tail, `scc_rt_main` with
  its two calls and four setup words marshalled (`Spike.Lib.A64.Rt.setupOk`
  at `setupMC 4`);
* so `placeOKAt` holds at `Λe` (`hello1_placeOKAt`, `placeOKAt_of`): every
  component passes at a real `ld.lld` layout. A12 holds too (`hello1_a12`).

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

/-! One kernel check per component: a single `decide +kernel` over the
conjunction peaks above 4 GB, each component alone at most about 3 GB. -/

theorem hello1_a1 : A64.a1 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a2 : A64.a2 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a3 : A64.a3 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a4 : A64.a4 placeCfg outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a5 : A64.a5 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a6 : A64.a6 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a7 : A64.a7 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a8 : A64.a8 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a9 : A64.a9 outLit ⟨Λe⟩ = true := by decide +kernel

/-- **A1–A9 of `hello1`'s output at `Λe`** (kernel-checked, componentwise). -/
theorem hello1_a1_9 : (A64.a1 outLit ⟨Λe⟩ && A64.a2 outLit ⟨Λe⟩ && A64.a3 outLit ⟨Λe⟩ &&
    A64.a4 placeCfg outLit ⟨Λe⟩ && A64.a5 outLit ⟨Λe⟩ && A64.a6 outLit ⟨Λe⟩ && A64.a7 outLit ⟨Λe⟩ &&
    A64.a8 outLit ⟨Λe⟩ && A64.a9 outLit ⟨Λe⟩) = true := by
  simp only [hello1_a1, hello1_a2, hello1_a3, hello1_a4, hello1_a5, hello1_a6, hello1_a7, hello1_a8,
    hello1_a9, Bool.and_self]

/-- **The code fills `.text`** at `Λe` (kernel-checked). -/
theorem hello1_codeFills : Scc.Cert.E2E.A64.codeFills outLit Λe = true := by
  decide +kernel

/-- **A11 holds at `Λe`** (kernel-checked): the `.setup` tail at `setupMC 4`. -/
theorem hello1_a11 : A64.a11 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- **A12 holds at `Λe`** (kernel-checked): the code and phases of every
stack-checked function. -/
theorem hello1_a12 : A64.a12 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- **`placeOKAt` of `hello1`'s output holds at `Λe`**, from its components. -/
theorem hello1_placeOKAt : A64.placeOKAt placeCfg Λe out = true := by
  rw [out_eq]
  exact A64.placeOKAt_of hello1_a1 hello1_a2 hello1_a3 hello1_a4 hello1_a5 hello1_a6 hello1_a7 hello1_a8
    hello1_a9 hello1_a11 hello1_a12

/-- **The end-to-end guard holds at `Λe`** (`placeOKAt` and the code filling `.text`). -/
theorem hello1_e2eOk : Scc.Cert.E2E.A64.e2eOk placeCfg Λe outLit = true := by
  have h := hello1_placeOKAt
  rw [out_eq] at h
  simp only [Scc.Cert.E2E.A64.e2eOk, h, hello1_codeFills, Bool.and_self]

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
