import Spike.Test.Ret0ReleaseA64
import Scc.Test.ElfTest

/-!
# `ret0.w` on AArch64, end to end at the linked executable's layout

`Scc/Test/elf/ret0a64/ret0` is `ret0.w`'s certificate text
(`SccCertificate.asm`, written verbatim to `ret0.s` next to it, checked
below), assembled and linked as `Scc/Test/run.sh` links AArch64 binaries:
`clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static
-fuse-ld=lld`, `ld.lld`'s default script (no linker script), which puts
`.rodata` (with the certificate's stack map `scc_stackmap`) below `.text`
and adds a build-id note. It runs (`qemu-aarch64`) and exits with 42. Its
layout `Λe` is read off the ELF file at elaboration time by the reader
(`scc_elf_layout%`, `Scc/Cert/Elf.lean`, fail closed). At `Λe`:

* the code the loader lays out from the certificate's output ends exactly
  where the executable's code region does (`ret0_codeEnd`, kernel-checked);
* the placement check passes (`ret0_placeOKAt`: each component decided by
  `decide +kernel`, combined by `placeOKAt_of`), with the data symbol
  `scc_stackmap` below the code (checked below);
* so the release theorem applies (`ret0_linked_correct`:
  `Ret0ReleaseA64.ret0_correct` at `Λe`), its only premise left the
  certificate's parse check `hpa`.

Perturbed layouts fail the check, and the reader refuses the file with its
entry point moved off `.text`'s start (the last tests). `Scc/Test/elf.sh
--relink` rebuilds the executable from `ret0.s`.
-/

namespace Spike.Test.Ret0LinkedA64

open Scc.Cert.PlaceOK
open SccCertificate (asm out outLit out_eq placeCfg)

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`:
read at elaboration time, the reader evaluated by the elaborator). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/ret0a64/ret0"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == "2fcc55b698bcad17c8ccfee85ff9ba8a2456db847e66996d726a72ad73bf3bd5"

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- The text linked is the certificate's `asm`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/ret0a64/ret0.s") == asm)

-- `ld.lld`'s default layout: `.rodata`, and the data symbol `scc_stackmap` in it, below the code.
#guard Λe.rodata.lo + Λe.rodata.size ≤ Λe.code.lo
#guard Λe.code.lo % 16 == 0

/-- **The code ends where the executable's code region does**: the code the
canonical loader lays out from `outLit` from `Λe.code.lo` fills `.text`
exactly (kernel-checked). -/
theorem ret0_codeEnd : Scc.Sem.A64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size := by
  decide +kernel

/-- A1, A2, A4 and A7 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_1 : (A64.a1 outLit ⟨Λe⟩ && A64.a2 outLit ⟨Λe⟩ &&
    A64.a4 placeCfg outLit ⟨Λe⟩ && A64.a7 outLit ⟨Λe⟩) = true := by
  decide +kernel

/-- A3 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_3 : A64.a3 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A5 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_5 : A64.a5 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A6 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_6 : A64.a6 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A8 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_8 : A64.a8 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A9 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_9 : A64.a9 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A11 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_11 : A64.a11 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A12 of `outLit` at `Λe` (kernel-checked). -/
theorem ret0_placeOKAt_12 : A64.a12 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- **`placeOKAt` of `scc`'s output at the executable's layout**, from its
components (`placeOKAt_of`). -/
theorem ret0_placeOKAt : A64.placeOKAt placeCfg Λe out = true := by
  have h1 := ret0_placeOKAt_1
  simp only [Bool.and_eq_true] at h1
  rw [out_eq]
  exact A64.placeOKAt_of h1.1.1.1 h1.1.1.2 ret0_placeOKAt_3 h1.1.2 ret0_placeOKAt_5 ret0_placeOKAt_6 h1.2
    ret0_placeOKAt_8 ret0_placeOKAt_9 ret0_placeOKAt_11 ret0_placeOKAt_12

/-- **`ret0.w` compiled for AArch64 is correct at the linked executable's
layout**, at every admissible entry state, for every budget `B` and memory
model `arch`: `Ret0ReleaseA64.ret0_correct` at `Λe`, given the certificate's
parse check `hpa`. -/
theorem ret0_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo asm out.prog out.secs = true) :
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main } B
      asm :=
  Spike.Test.Ret0ReleaseA64.ret0_correct Λe B arch ret0_placeOKAt hpa

/-- **The entry quantifier is not vacuous at `Λe`**: the 64 KiB stack at
`2 ^ 32` is admissible there. -/
theorem ret0_linked_witness :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseA64.main } :=
  Spike.Test.Ret0ReleaseA64.ok_witness_of_placeOKAt ret0_placeOKAt

/--
info: 'Spike.Test.Ret0LinkedA64.ret0_linked_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ret0_linked_correct

/--
info: 'Spike.Test.Ret0LinkedA64.ret0_linked_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ret0_linked_witness

/-! ### Perturbed layouts fail closed -/

-- A code region one instruction short: `codeFits` (A1) fails.
#guard !A64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size - 4⟩ } outLit

-- An abort label that is not the runtime's: `abortStd` (A2) fails.
#guard !A64.placeOKAt placeCfg
  { Λe with abortLbl := fun k => if k == .heap then "scc_rt_abort_overflow_exit" else Scc.Cert.Link.abortName k }
  outLit

-- The code base one instruction off: `_start` is not at it.
#guard !A64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo + 4, Λe.code.size⟩ } outLit

-- `e_entry` (offset 24) one instruction past the start of `.text`, where A1 puts `_start`: the reader
-- refuses the file.
/-- info: the entry point 2163572 is not the start of .text (2163568) -/
#guard_msgs in
#eval Scc.Test.Elf.verdict "Scc/Test/elf/ret0a64/ret0" fun b => pure (Scc.Test.Elf.put64 b 24 0x210374)

/-- A code region one instruction short fails `placeOKAt` (kernel-checked,
through A1: `placeOKAt_eq_false_of_a1`). -/
example : A64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size - 4⟩ } outLit = false :=
  A64.placeOKAt_eq_false_of_a1 (by decide +kernel)

end Spike.Test.Ret0LinkedA64
