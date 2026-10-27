import Spike.Test.Cert.X64Hello1Cert
import Scc.Test.ElfTest
import Scc.Cert.E2EX64

/-!
# `hello1.w` on x86-64 at the linked executable's layout

`hello1.w` is outside `Accepted0` (`SccCertificate.prog_not_accepted`). Its
correctness theorem `hello1_finalC_gen` (`Spike/Test/X64Hello1FinalC.lean`)
holds at any layout passing the placement check; `hello1_finalC` is it at
this file's layout `Λe`, using the placement facts below. `certify.sh`
instantiates `hello1_finalC_gen` at a fresh build's layout. The x86-64 twin of
`Spike/Test/Hello1LinkedA64.lean`.

`Scc/Test/elf/hello1x64/hello1` is `hello1.w`'s certificate text
(`SccCertificate.asm`, written verbatim to `hello1.s` next to it, checked
below), assembled by GNU `as` and linked by GNU `ld -static` with its
default script (no linker script), as `Scc/Test/run.sh` links x86-64
binaries and as `ret0x64/ret0` is linked (`Spike/Test/Ret0LinkedX64.lean`).
It runs, prints `Hello, world` and exits with 0. `ld` puts `.text` at
`0x401000` and `.rodata` above it. Its layout `Λe` is read off the file at
elaboration time (`scc_elf_layout%`, fail closed). At `Λe`, each by
`decide +kernel`:

* the code the loader lays out from the certificate's output ends exactly
  where the executable's code region does (`hello1_codeEnd`, through the
  shared end-to-end guard `Scc.Cert.E2E.X64.codeFills`);
* A1–A9, A11 and A12 of the certificate's output hold, one declaration
  each;
* so `placeOKAt` holds at `Λe` (`hello1_placeOKAt`, `placeOKAt_of`) and the
  end-to-end guard with it (`hello1_e2eOk`): every component passes at a
  real `ld` layout.

Perturbed layouts fail the check (the last tests). `Scc/Test/elf.sh
--relink` rebuilds the executable from `hello1.s`.
-/

namespace Spike.Test.Hello1LinkedX64

open Scc.Cert.PlaceOK
open SccCertificate (asm out outLit out_eq placeCfg)

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`:
read at elaboration time, the reader evaluated by the elaborator). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/hello1x64/hello1"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == "e1b2ff37c7cb558ff8e7a35c4bf1ea1c7ed2f78a438c5ae5dbae8ce8b901bd11"

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- The text linked is the certificate's `asm`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/hello1x64/hello1.s") == asm)

-- The reader accepts the executable.
/-- info: accepted -/
#guard_msgs in
#eval Scc.Test.Elf.verdict "Scc/Test/elf/hello1x64/hello1" pure

-- `ld`'s default layout: `.text` at `0x401000`, `.rodata` and every data symbol above the code.
#guard Λe.code.lo == 0x401000
#guard Λe.code.lo + Λe.code.size ≤ Λe.rodata.lo
#guard (Scc.Sem.loadSyms Λe outLit.secs.rodata).all (Λe.code.lo ≤ ·.2)

/-! ### The placement check at the executable's layout -/

/-- **The code ends where the executable's code region does**: the code the
canonical loader lays out from `outLit` from `Λe.code.lo` fills `.text`
exactly (kernel-checked). -/
theorem hello1_codeEnd : Scc.Sem.X64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size :=
  Scc.Cert.E2E.X64.codeEnd_eq_of_codeFills hello1_codeFills
where
  /-- The code fills `.text` at `Λe` (kernel-checked). -/
  hello1_codeFills : Scc.Cert.E2E.X64.codeFills outLit Λe = true := by decide +kernel

/-! One kernel check per component. -/

theorem hello1_a1 : X64.a1 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a2 : X64.a2 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a3 : X64.a3 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a4 : X64.a4 placeCfg outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a5 : X64.a5 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a6 : X64.a6 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a7 : X64.a7 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a8 : X64.a8 outLit ⟨Λe⟩ = true := by decide +kernel
theorem hello1_a9 : X64.a9 outLit ⟨Λe⟩ = true := by decide +kernel

/-- **A11 holds at `Λe`** (kernel-checked): `hello1`'s `.setup` tail,
`scc_rt_main` with its two calls and four setup words marshalled
(`Spike.Lib.X64.Rt.setupOk` at `setupMC 4`). -/
theorem hello1_a11 : X64.a11 outLit ⟨Λe⟩ = true := by decide +kernel

/-- A12's code part of `outLit` (kernel-checked; `Scc/Cert/A12StageX64.lean`). -/
theorem hello1_a12c : X64.a12code outLit = true := by decide +kernel

/-- A12's phase part of `outLit` at `Λe` (kernel-checked). -/
theorem hello1_a12p : X64.a12ph outLit ⟨Λe⟩ = true := by decide +kernel

/-- A12 of `outLit` at `Λe`: the code and phases of every stack-checked
function. -/
theorem hello1_a12 : X64.a12 outLit ⟨Λe⟩ = true :=
  X64.a12_of_split hello1_a12c hello1_a12p

/-- **`placeOKAt` of `hello1`'s output holds at `Λe`**, from its components
(`placeOKAt_of`). -/
theorem hello1_placeOKAt : X64.placeOKAt placeCfg Λe out = true := by
  rw [out_eq]
  exact X64.placeOKAt_of hello1_a1 hello1_a2 hello1_a3 hello1_a4 hello1_a5 hello1_a6 hello1_a7 hello1_a8
    hello1_a9 hello1_a11 hello1_a12

/-- **The end-to-end guard holds at `Λe`** (`placeOKAt` and the code filling
`.text`). -/
theorem hello1_e2eOk : Scc.Cert.E2E.X64.e2eOk placeCfg Λe outLit = true := by
  have h := hello1_placeOKAt
  rw [out_eq] at h
  simp only [Scc.Cert.E2E.X64.e2eOk, h, hello1_codeEnd.hello1_codeFills, Bool.and_self]

/--
info: 'Spike.Test.Hello1LinkedX64.hello1_e2eOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_e2eOk

/-! ### Perturbed layouts fail closed -/

-- A code region one byte short: `codeFits` (A1) fails.
#guard !X64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size - 1⟩ } outLit

-- A code region one byte long: `codeFits` (A1) still passes, the end-to-end guard does not.
#guard X64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size + 1⟩ } outLit
#guard !Scc.Cert.E2E.X64.e2eOk placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size + 1⟩ } outLit

-- The code base one byte off: `_start` is not at it.
#guard !X64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo + 1, Λe.code.size⟩ } outLit

end Spike.Test.Hello1LinkedX64
