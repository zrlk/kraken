import Spike.Test.Ret0ReleaseX64
import Scc.Test.ElfTest
import Scc.Cert.E2EX64

/-!
# `ret0.w` on x86-64, end to end at the linked executable's layout

`Scc/Test/elf/ret0x64/ret0` is `ret0.w`'s certificate text
(`SccCertificate.asm`, written verbatim to `ret0.s` next to it, checked
below), assembled by GNU `as` and linked by GNU `ld -static` with its
default script (no linker script), as `Scc/Test/run.sh` links x86-64
binaries; it runs and exits with 42. Its layout `Λe` is read off the ELF
file at elaboration time by the
reader (`scc_elf_layout%`, `Scc/Cert/Elf.lean`, fail closed). At `Λe`:

* the code the loader lays out from the certificate's output ends exactly
  where the executable's code region does (`ret0_codeEnd`, kernel-checked,
  through the shared end-to-end guard `Scc.Cert.E2E.X64.codeFills`);
* the placement check passes (`ret0_placeOKAt`: each component decided by
  `decide +kernel`, combined by `placeOKAt_of`);
* so the release theorem applies (`ret0_linked_correct`:
  `Ret0ReleaseX64.ret0_correct` at `Λe`), its only premise left the
  certificate's parse check `hpa`.

Perturbed layouts fail the check, and the reader refuses the file with its
entry point moved off `.text`'s start (the last tests). `Scc/Test/elf.sh
--relink` rebuilds the executable from `ret0.s`.
-/

namespace Spike.Test.Ret0LinkedX64

open Scc.Cert.PlaceOK
open SccCertificate (asm sizes labelOffs out outLit out_eq placeCfg)

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`:
read at elaboration time, the reader evaluated by the elaborator). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/ret0x64/ret0"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == "f202a51eacf84e00d088804784ef574adf1039d12f1beed89a2f22e526d23679"

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- The text linked is the certificate's `asm`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/ret0x64/ret0.s") == asm)

/-- **The code ends where the executable's code region does**: the code the
canonical loader lays out from `outLit` from `Λe.code.lo` fills `.text`
exactly (kernel-checked). -/
theorem ret0_codeEnd : Scc.Sem.X64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size :=
  Scc.Cert.E2E.X64.codeEnd_eq_of_codeFills (by decide +kernel)

-- The end-to-end guard: the placement check and the code filling `.text` (evaluation).
#guard Scc.Cert.E2E.X64.e2eOk placeCfg Λe outLit

/-- A1, A2, A4 and A7 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_1 : (X64.a1 outLit ⟨Λe⟩ && X64.a2 outLit ⟨Λe⟩ &&
    X64.a4 placeCfg outLit ⟨Λe⟩ && X64.a7 outLit ⟨Λe⟩) = true := by
  decide +kernel

/-- A3 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_3 : X64.a3 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A5 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_5 : X64.a5 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A6 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_6 : X64.a6 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A8 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_8 : X64.a8 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A9 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_9 : X64.a9 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A11 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_11 : X64.a11 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A12's code part of `outLit` (kernel-checked; `Scc/Cert/A12StageX64.lean`). -/
theorem ret0_placeOKAt_12c : X64.a12code outLit = true := by
  decide +kernel

/-- A12's phase part of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_12p : X64.a12ph outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A12 of `outLit` at `Λe`: the code of every stack-checked function. -/
theorem ret0_placeOKAt_12 : X64.a12 outLit ⟨Λe⟩ = true :=
  X64.a12_of_split ret0_placeOKAt_12c ret0_placeOKAt_12p

-- A12 numbers each function's local labels `.Lf.xN` from the IR (`starts`,
-- prefix sums of `fnLabs`); that is the emitter's numbering (evaluation).
#guard match outLit.place.ir with
  | some ir => Scc.Cert.Code1X64.startsOk ir
  | none => false

/-- **`placeOKAt` of `scc`'s output at the executable's layout**, from its
components (`placeOKAt_of`). -/
theorem ret0_placeOKAt : X64.placeOKAt placeCfg Λe out = true := by
  have h1 := ret0_placeOKAt_1
  simp only [Bool.and_eq_true] at h1
  rw [out_eq]
  exact X64.placeOKAt_of h1.1.1.1 h1.1.1.2 ret0_placeOKAt_3 h1.1.2 ret0_placeOKAt_5 ret0_placeOKAt_6 h1.2
    ret0_placeOKAt_8 ret0_placeOKAt_9 ret0_placeOKAt_11 ret0_placeOKAt_12

/-- **`ret0.w` compiled for x86-64 is correct at the linked executable's
layout**, at every admissible entry state, for every budget `B` and memory
model `arch`: `Ret0ReleaseX64.ret0_correct` at `Λe`, given the
certificate's parse check `hpa`. -/
theorem ret0_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main } B
      ⟨asm, sizes, labelOffs⟩ :=
  Spike.Test.Ret0ReleaseX64.ret0_correct Λe B arch ret0_placeOKAt hpa

/-- **The entry quantifier is not vacuous at `Λe`**: the 64 KiB stack at
`2 ^ 32` is admissible there. -/
theorem ret0_linked_witness :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main } :=
  Spike.Test.Ret0ReleaseX64.ok_witness_of_placeOKAt ret0_placeOKAt

/--
info: 'Spike.Test.Ret0LinkedX64.ret0_linked_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ret0_linked_correct

/-! ### Perturbed layouts fail closed -/

-- A code region one byte short: `codeFits` (A1) fails.
#guard !X64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size - 1⟩ } outLit

-- A code region one byte long: `codeFits` (A1) still passes, the end-to-end guard does not.
#guard X64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size + 1⟩ } outLit
#guard !Scc.Cert.E2E.X64.e2eOk placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size + 1⟩ } outLit

-- An abort label that is not the runtime's: `abortStd` (A2) fails.
#guard !X64.placeOKAt placeCfg
  { Λe with abortLbl := fun k => if k == .heap then "scc_rt_abort_overflow_exit" else Scc.Cert.Link.abortName k }
  outLit

-- The code base one byte off: `_start` is not at it.
#guard !X64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo + 1, Λe.code.size⟩ } outLit

-- `e_entry` (offset 24) one byte past the start of `.text`, where A1 puts `_start`: the reader refuses
-- the file.
/-- info: the entry point 4198401 is not the start of .text (4198400) -/
#guard_msgs in
#eval Scc.Test.Elf.verdict "Scc/Test/elf/ret0x64/ret0" fun b => pure (Scc.Test.Elf.put64 b 24 0x401001)

/-- A code region one byte short fails `placeOKAt` (kernel-checked, through
A1: `placeOKAt_eq_false_of_a1`). -/
example : X64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size - 1⟩ } outLit = false :=
  X64.placeOKAt_eq_false_of_a1 (by decide +kernel)

end Spike.Test.Ret0LinkedX64
