import Spike.Test.Call1LinkedA64
import Spike.Lib.LowerA64.Correct1Tail

/-!
# `call1.w` on AArch64 after the granule pass, at the linked executable's layout (placement only)

`Scc/Test/elf/call1a64g/call1` is `scc --granule`'s text for `call1.w`
(`call1.s` next to it), linked as `Call1LinkedA64`'s. The text is the
certificate's `asm` with the pass's tail before `scc_text_end` (a `.zero`
filler, `.Lgw0:` and the descriptor word) and the `.text.scc_galign` section
after it (`asmG`, checked below). Its parse is the certificate's cells with
the end label replaced by the tail `tailG` (checked below), and the same
data sections: the output `outF := withTail outLit tailG`.

As in `Call1LinkedA64`, no correctness theorem is stated (`call1.w` is
outside `Accepted0` and has two code blocks). At the executable's layout
`ΛG`, each by `decide +kernel`: every component of `placeOKAt` of `outF`
holds, A12 included (`call1G_placeOKAt`). With one instruction of `pick`'s
`then` block replaced, A12 fails, and so does `placeOKAt`
(`perturbedG_not_placeOKAt`), while A9 still passes (`perturbedG_a9`).
-/

namespace Spike.Test.Call1LinkedA64G

open Scc.Cert.PlaceOK
open SccCertificate (asm out outLit out_eq placeCfg)
open Spike.Lib.LowerA64 (withTail)

-- The executable is the one linked (evaluation, not a proof).
/-- info: 6a3c9302d52960bc986b5e7591af9f63be94d1b71f9aad241b3f0689479be349 -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile "Scc/Test/elf/call1a64g/call1"))

/-- The granule pass's tail as cells: the filler, `.Lgw0`, the descriptor
word (a text `.quad` reads as 8 zero bytes, `Scc/Sem/TextA64.lean`) and the
end label. -/
def tailG : List Directive :=
  [.zeros 60528, .label ".Lgw0", .byteArray ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩, .label "scc_text_end"]

/-- The post-pass text: the certificate's with the tail before the end
label and the alignment section after it. -/
def asmG : String :=
  asm.replace "scc_text_end:\n"
    ("\t.zero 60528\n.Lgw0:\n\t.quad scc_gc_desc - .\nscc_text_end:\n" ++
      "\t.section .text.scc_galign,\"ax\",%progbits\n\t.p2align 16\n\t.text\n")

-- The text linked is `asmG`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/call1a64g/call1.s") == asmG)

-- The reader accepts the executable.
/-- info: accepted -/
#guard_msgs in
#eval Scc.Test.Elf.verdict "Scc/Test/elf/call1a64g/call1" pure

/-- The output with the tail. -/
abbrev outF : A64.Out := withTail outLit tailG

-- The parse of the linked text is the certificate's cells before the end label, then `tailG`, and
-- the certificate's data sections (evaluation).
#guard outLit.prog.getLast? == some (.label "scc_text_end")
set_option maxRecDepth 100000 in
#guard Scc.Cert.Link.A64.parsesTo asmG outF.prog outF.secs

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/call1a64g/call1"

/-- The linked executable's layout. -/
abbrev ΛG : Scc.Sem.Layout := elf.1

-- The code base moved to a granule and `.text` is one granule.
#guard ΛG.code.lo % 0x10000 == 0 && ΛG.code.size == 0x10000

/-- **The code fills `.text`** at `ΛG` (kernel-checked). -/
theorem call1G_codeFills : Scc.Cert.E2E.A64.codeFills outF ΛG = true := by
  decide +kernel

/-- A1, A2 (by its keyed form), A4 and A7 of `outF` at `ΛG` (kernel-checked). -/
theorem call1G_placeOKAt_1 : (A64.a1 outF ⟨ΛG⟩ && A64.a2fast outF ⟨ΛG⟩ &&
    A64.a4 placeCfg outF ⟨ΛG⟩ && A64.a7 outF ⟨ΛG⟩) = true := by
  decide +kernel

theorem call1G_placeOKAt_3 : A64.a3 outF ⟨ΛG⟩ = true := by decide +kernel
theorem call1G_placeOKAt_5 : A64.a5 outF ⟨ΛG⟩ = true := by decide +kernel
theorem call1G_placeOKAt_6 : A64.a6 outF ⟨ΛG⟩ = true := by decide +kernel
theorem call1G_placeOKAt_8 : A64.a8 outF ⟨ΛG⟩ = true := by decide +kernel
theorem call1G_placeOKAt_9 : A64.a9 outF ⟨ΛG⟩ = true := A64.a9_of_fast (by decide +kernel)
theorem call1G_placeOKAt_11 : A64.a11 outF ⟨ΛG⟩ = true := by decide +kernel
theorem call1G_placeOKAt_12c : A64.a12code outF = true := by decide +kernel
theorem call1G_placeOKAt_12p : A64.a12ph outF ⟨ΛG⟩ = true := by decide +kernel

/-- A12 of `outF` at `ΛG`: the code of `pick` and `main`. -/
theorem call1G_placeOKAt_12 : A64.a12 outF ⟨ΛG⟩ = true :=
  A64.a12_of_split call1G_placeOKAt_12c call1G_placeOKAt_12p

/-- **`placeOKAt` of `scc`'s output with the tail at the post-pass
executable's layout**, from its components (`placeOKAt_of`). -/
theorem call1G_placeOKAt : A64.placeOKAt placeCfg ΛG (withTail out tailG) = true := by
  have h1 := call1G_placeOKAt_1
  simp only [Bool.and_eq_true] at h1
  rw [out_eq]
  exact A64.placeOKAt_of h1.1.1.1 (A64.a2_of_fast h1.1.1.2) call1G_placeOKAt_3 h1.1.2 call1G_placeOKAt_5
    call1G_placeOKAt_6 h1.2 call1G_placeOKAt_8 call1G_placeOKAt_9 call1G_placeOKAt_11 call1G_placeOKAt_12

/-! ### One instruction of `pick` perturbed -/

open Spike.Test.Call1LinkedA64 (thenAt)

/-- `outF` with `pick`'s `movz x9, #50` replaced by the instruction after
it (`movz x10, #8`), as `Call1LinkedA64.outBad`. -/
def outBadG : A64.Out := { outF with prog := outF.prog.set (thenAt + 1) (outF.prog[thenAt + 2]?.getD (.label "")) }

-- The perturbed cells are `Call1LinkedA64`'s: before the tail (evaluation).
#guard thenAt + 2 < outLit.prog.length - 1
#guard outF.prog[thenAt + 1]? != outF.prog[thenAt + 2]?

/-- **A12 catches the perturbed instruction** (kernel-checked). -/
theorem perturbedG_a12 : A64.a12 outBadG ⟨ΛG⟩ = false :=
  A64.a12fast_eq outBadG ⟨ΛG⟩ ▸ (by decide +kernel : A64.a12fast outBadG ⟨ΛG⟩ = false)

/-- **`placeOKAt` of the perturbed output is `false`**, by A12. -/
theorem perturbedG_not_placeOKAt : A64.placeOKAt placeCfg ΛG outBadG = false :=
  A64.placeOKAt_eq_false_of_a12 perturbedG_a12

/-- A9 alone does not see it (kernel-checked). -/
theorem perturbedG_a9 : A64.a9 outBadG ⟨ΛG⟩ = true :=
  A64.a9_of_fast (by decide +kernel)

end Spike.Test.Call1LinkedA64G

/-- info: 'Spike.Test.Call1LinkedA64G.call1G_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Test.Call1LinkedA64G.call1G_placeOKAt

/-- info: 'Spike.Test.Call1LinkedA64G.perturbedG_not_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Test.Call1LinkedA64G.perturbedG_not_placeOKAt
