import Spike.Test.Cert.X64Frame0Cert
import Scc.Test.ElfTest
import Scc.Cert.E2EX64

/-!
# A zero-frame function on x86-64: `placeOK` and `placeOKAt` of `frame0.w`

`Spike/Gen/frame0.w` is `def main(u : Unit) : Int = ret 42`: no `+`, so
`main` has no IR register and no call, and its frame
(`Scc.Emit.X64.frameOf`) is 0 bytes. The emitter writes the prologue's
`subq $0, %rsp` even then (GNU `as`: `48 83 ec 00`, 4 bytes), the form the
prologue check expects (`prologueIn`, `xFr`, `Spike/Lib/X64CodeSegs.lean`).
Before this, the `subq` was left out at frame 0 and every such program
failed A9 (`fnCodeOk`, `fnPhOk`), fail closed.

`Spike/Test/Cert/X64Frame0Cert.lean` is `scc --arch x64 --cert`'s
certificate for it (its `prog_placeOK`: `placeOK` at the canonical tables).
`Scc/Test/elf/frame0x64/frame0` is its text (`frame0.s` next to it, checked
below), assembled by GNU `as` and linked by GNU `ld -static` as
`Scc/Test/run.sh` links x86-64 binaries; it exits with 42. At the layout read
off that file (`scc_elf_layout%`) the code fills `.text` exactly and
`placeOKAt` holds, each component decided by `decide +kernel`.
-/

namespace Spike.Test.Frame0LinkedX64

open Scc.Cert.PlaceOK
open SccCertificate (asm out outLit out_eq placeCfg)

/-- **`placeOK` of the zero-frame program's output** (the certificate's
kernel decision). -/
example : X64.placeOK placeCfg out = true := SccCertificate.prog_placeOK

-- The zero-frame prologue (evaluation): `main`'s check, then `subq $0, %rsp`, then its body.
/-- info: true -/
#guard_msgs in
#eval IO.println ((asm.splitOn "jb .Lwc_main.stk\n\tsubq $0, %rsp\n.Lwc_main.entry:").length == 2)

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/frame0x64/frame0"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == "2ad728ee19b7ec8ff1e7140856e6ea54971b25a598f114da4a6d260867bec6a2"

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

-- The text linked is the certificate's `asm`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/frame0x64/frame0.s") == asm)

/-- The code the canonical loader lays out from `outLit` fills `.text`
exactly (kernel-checked). -/
theorem frame0_codeEnd : Scc.Sem.X64.codeEnd Λe.code.lo outLit.prog = Λe.code.lo + Λe.code.size :=
  Scc.Cert.E2E.X64.codeEnd_eq_of_codeFills (by decide +kernel)

-- The end-to-end guard: the placement check and the code filling `.text` (evaluation).
#guard Scc.Cert.E2E.X64.e2eOk placeCfg Λe outLit

/-- A1, A2, A4 and A7 of `outLit` at `Λe` (kernel-checked). -/
theorem frame0_placeOKAt_1 : (X64.a1 outLit ⟨Λe⟩ && X64.a2 outLit ⟨Λe⟩ &&
    X64.a4 placeCfg outLit ⟨Λe⟩ && X64.a7 outLit ⟨Λe⟩) = true := by
  decide +kernel

/-- A3 of `outLit` at `Λe` (kernel-checked). -/
theorem frame0_placeOKAt_3 : X64.a3 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A5 of `outLit` at `Λe` (kernel-checked). -/
theorem frame0_placeOKAt_5 : X64.a5 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A6 of `outLit` at `Λe` (kernel-checked). -/
theorem frame0_placeOKAt_6 : X64.a6 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A8 of `outLit` at `Λe` (kernel-checked). -/
theorem frame0_placeOKAt_8 : X64.a8 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A9 of `outLit` at `Λe`: the lowered code blocks, the zero-frame prologue
among them (kernel-checked). -/
theorem frame0_placeOKAt_9 : X64.a9 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A11 of `outLit` at `Λe` (kernel-checked). -/
theorem frame0_placeOKAt_11 : X64.a11 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A12's code part of `outLit` (kernel-checked; `Scc/Cert/A12StageX64.lean`). -/
theorem frame0_placeOKAt_12c : X64.a12code outLit = true := by
  decide +kernel

/-- A12's phase part of `outLit` at `Λe` (kernel-checked). -/
theorem frame0_placeOKAt_12p : X64.a12ph outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A12 of `outLit` at `Λe`: the code of every stack-checked function. -/
theorem frame0_placeOKAt_12 : X64.a12 outLit ⟨Λe⟩ = true :=
  X64.a12_of_split frame0_placeOKAt_12c frame0_placeOKAt_12p

-- A12 numbers each function's local labels `.Lf.xN` from the IR (`starts`,
-- prefix sums of `fnLabs`); that is the emitter's numbering (evaluation).
#guard match outLit.place.ir with
  | some ir => Scc.Cert.Code1X64.startsOk ir
  | none => false

/-- **`placeOKAt` of the zero-frame program's output at the executable's
layout**, from its components (`placeOKAt_of`). -/
theorem frame0_placeOKAt : X64.placeOKAt placeCfg Λe out = true := by
  have h1 := frame0_placeOKAt_1
  simp only [Bool.and_eq_true] at h1
  rw [out_eq]
  exact X64.placeOKAt_of h1.1.1.1 h1.1.1.2 frame0_placeOKAt_3 h1.1.2 frame0_placeOKAt_5 frame0_placeOKAt_6 h1.2
    frame0_placeOKAt_8 frame0_placeOKAt_9 frame0_placeOKAt_11 frame0_placeOKAt_12

/--
info: 'Spike.Test.Frame0LinkedX64.frame0_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms frame0_placeOKAt

end Spike.Test.Frame0LinkedX64
