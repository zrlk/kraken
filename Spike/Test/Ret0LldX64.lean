import Spike.Test.Ret0ReleaseX64
import Scc.Test.ElfTest
import Scc.Cert.E2EX64

/-!
# `ret0.w` on x86-64, end to end at an `ld.lld`-linked executable's layout

`Scc/Test/elf/ret0x64lld/ret0` is the same text as
`Spike/Test/Ret0LinkedX64.lean`'s (`ret0.s` next to it is
`SccCertificate.asm`, checked below), assembled by GNU `as` and linked by
`ld.lld -static` with its default script (no linker script); it runs and
exits with 42. `ld.lld`'s default script puts `.rodata` *below* the code, so
the runtime's read-only data symbols lie below `.text` (checked below). The
reader accepts that (`Scc.Cert.Elf.refuseBelowCode` is off), and x86-64's
loader check (A2, `Link.X64.loadOk`) accepts it
(`Rt.X64.symsAround`, two-sided). At the layout `Λe` read off the file
(`scc_elf_layout%`):

* the code fills `.text` exactly (`lld_codeEnd`, kernel-checked, through
  `Scc.Cert.E2E.X64.codeFills`);
* every component of the placement check passes (`lld_placeOKAt`, each by
  `decide +kernel`, combined by `placeOKAt_of`);
* so the release theorem applies (`lld_linked_correct`:
  `Ret0ReleaseX64.ret0_correct` at `Λe`), its only premise left the
  certificate's parse check `hpa`.

`Scc/Test/elf.sh --relink` rebuilds the executable from `ret0.s`.
-/

namespace Spike.Test.Ret0LldX64

open Scc.Cert.PlaceOK
open SccCertificate (asm sizes labelOffs out outLit out_eq placeCfg)

/-- The layout of the `ld.lld`-linked executable and its SHA-256
(`scc_elf_layout%`: read at elaboration time). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/ret0x64lld/ret0"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == "56c8308203ba1acd4b83f29ab376a96272362c865cbe16db88ffc7e82ef17f3e"

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- The text linked is the certificate's `asm`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/ret0x64lld/ret0.s") == asm)

-- Not vacuous: `.rodata` ends at or below the code's start, and the symbols the loader places
-- (`loadSyms`: the `.rodata` labels at their image addresses among them) include one below the code
-- (evaluation).
#guard Λe.rodata.lo + Λe.rodata.size ≤ Λe.code.lo
#guard (Scc.Sem.loadSyms Λe outLit.secs.rodata).any fun s => s.2 < Λe.code.lo

/-- **The code ends where the executable's code region does**: the code the
canonical loader lays out from `outLit` from `Λe.code.lo` fills `.text`
exactly (kernel-checked). -/
theorem lld_codeEnd : Scc.Sem.X64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size :=
  Scc.Cert.E2E.X64.codeEnd_eq_of_codeFills (by decide +kernel)

-- The end-to-end guard: the placement check and the code filling `.text` (evaluation).
#guard Scc.Cert.E2E.X64.e2eOk placeCfg Λe outLit

/-- A1, A2, A4 and A7 of `outLit` at `Λe` (kernel-checked). -/
theorem lld_placeOKAt_1 : (X64.a1 outLit ⟨Λe⟩ && X64.a2 outLit ⟨Λe⟩ &&
    X64.a4 placeCfg outLit ⟨Λe⟩ && X64.a7 outLit ⟨Λe⟩) = true := by
  decide +kernel

/-- A3 of `outLit` at `Λe` (kernel-checked). -/
theorem lld_placeOKAt_3 : X64.a3 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A5 of `outLit` at `Λe` (kernel-checked). -/
theorem lld_placeOKAt_5 : X64.a5 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A6 of `outLit` at `Λe` (kernel-checked). -/
theorem lld_placeOKAt_6 : X64.a6 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A8 of `outLit` at `Λe` (kernel-checked). -/
theorem lld_placeOKAt_8 : X64.a8 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A9 of `outLit` at `Λe` (kernel-checked). -/
theorem lld_placeOKAt_9 : X64.a9 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A11 of `outLit` at `Λe` (kernel-checked). -/
theorem lld_placeOKAt_11 : X64.a11 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- **`placeOKAt` of `scc`'s output at the executable's layout**, from its
components (`placeOKAt_of`). -/
theorem lld_placeOKAt : X64.placeOKAt placeCfg Λe out = true := by
  have h1 := lld_placeOKAt_1
  simp only [Bool.and_eq_true] at h1
  rw [out_eq]
  exact X64.placeOKAt_of h1.1.1.1 h1.1.1.2 lld_placeOKAt_3 h1.1.2 lld_placeOKAt_5 lld_placeOKAt_6 h1.2
    lld_placeOKAt_8 lld_placeOKAt_9 lld_placeOKAt_11

/-- **`ret0.w` compiled for x86-64 is correct at the linked executable's
layout**, at every admissible entry state, for every budget `B` and memory
model `arch`: `Ret0ReleaseX64.ret0_correct` at `Λe`, given the
certificate's parse check `hpa`. -/
theorem lld_linked_correct (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨asm, sizes, labelOffs⟩ out.prog out.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main } B
      ⟨asm, sizes, labelOffs⟩ :=
  Spike.Test.Ret0ReleaseX64.ret0_correct Λe B arch lld_placeOKAt hpa

/-- **The entry quantifier is not vacuous at `Λe`**: the 64 KiB stack at
`2 ^ 32` is admissible there. -/
theorem lld_linked_witness :
    Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λe with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main } :=
  Spike.Test.Ret0ReleaseX64.ok_witness_of_placeOKAt lld_placeOKAt

/--
info: 'Spike.Test.Ret0LldX64.lld_linked_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lld_linked_correct

/-! ### Perturbed layouts fail closed -/

-- A code region one byte short: `codeFits` (A1) fails.
#guard !X64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo, Λe.code.size - 1⟩ } outLit

-- The code base one byte off: `_start` is not at it.
#guard !X64.placeOKAt placeCfg { Λe with code := ⟨Λe.code.lo + 1, Λe.code.size⟩ } outLit

end Spike.Test.Ret0LldX64
