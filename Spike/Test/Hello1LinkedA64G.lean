import Spike.Test.Hello1LinkedA64
import Spike.Test.A64Hello1FinalCAG

/-!
# `hello1.w` on AArch64 after the granule pass, at the linked executable's layout

`Scc/Test/elf/hello1a64g/hello1` is `scc --granule`'s text for `hello1.w`
(`hello1.s` next to it), linked as `Hello1LinkedA64`'s. The text is the
certificate's `asm` with the pass's tail before `scc_text_end` (a `.zero`
filler, `.Lgw0:` and the descriptor word) and the `.text.scc_galign` section
after it (`asmG`, checked below); its parse is the certificate's cells with
the end label replaced by the tail `tailG` and the same data sections.

At the executable's layout `ΛG`, each by `decide +kernel` (A2 by its keyed
form, `Scc/Cert/A2StageA64.lean`): A1–A9, A11 and A12 of the certificate's output and of the output with the tail. So
`placeOKAt` holds for both (`hello1G_placeOKAt`, `hello1G_placeOKAtF`), and
`hello1_finalCAG` is `hello1_finalCAG_of` at `ΛG`.
-/

namespace Spike.Test.Hello1LinkedA64G

open Scc.Cert.PlaceOK
open SccCertificate (asm out outLit out_eq placeCfg)
open Spike.Lib.LowerA64 (withTail tailLabsG)

-- The executable is the one linked (evaluation, not a proof).
/-- info: a64ed1fb622548cac8459210c1c5035b59de654fbb32ff5debee81b6f50a0bab -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile "Scc/Test/elf/hello1a64g/hello1"))

/-- The granule pass's tail as cells: the filler, `.Lgw0`, the descriptor
word (its bytes as the loader reads them) and the end label. -/
def tailG : List Directive :=
  [.zeros 60360, .label ".Lgw0", .byteArray ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩, .label "scc_text_end"]

/-- The post-pass text: the certificate's with the tail before the end
label and the alignment section after it. -/
def asmG : String :=
  asm.replace "scc_text_end:\n"
    ("\t.zero 60360\n.Lgw0:\n\t.quad scc_gc_desc - .\nscc_text_end:\n" ++
      "\t.section .text.scc_galign,\"ax\",%progbits\n\t.p2align 16\n\t.text\n")

-- The text linked is `asmG`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/hello1a64g/hello1.s") == asmG)

-- The reader accepts the executable.
/-- info: accepted -/
#guard_msgs in
#eval Scc.Test.Elf.verdict "Scc/Test/elf/hello1a64g/hello1" pure

-- The parse of the linked text is the certificate's cells before the end label, then the tail
-- `tailG`: the filler, `.Lgw0`, the descriptor word (a text `.quad` reads as 8 zero bytes,
-- `Scc/Sem/TextA64.lean`) and `scc_text_end` (evaluation; `hpa` below is the same fact).
#guard match Scc.Sem.A64.textProgram asmG with
  | .ok p => p.take (outLit.prog.length - 1) == outLit.prog.dropLast &&
      p.drop (outLit.prog.length - 1) == tailG
  | .error _ => false

/-- The output with the tail. -/
abbrev outF : A64.Out := withTail outLit tailG

/-! ### The placement check at the executable's layout -/

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/hello1a64g/hello1"

#guard elf.2 == "a64ed1fb622548cac8459210c1c5035b59de654fbb32ff5debee81b6f50a0bab"

/-- The linked executable's layout. -/
abbrev ΛG : Scc.Sem.Layout := elf.1

-- The code base moved to a granule (and `.text` is one granule).
#guard ΛG.code.lo % 0x10000 == 0 && ΛG.code.size == 0x10000

theorem hello1G_a1 : A64.a1 outLit ⟨ΛG⟩ = true := by decide +kernel
theorem hello1G_a2 : A64.a2 outLit ⟨ΛG⟩ = true := A64.a2_of_fast (by decide +kernel)
theorem hello1G_a3 : A64.a3 outLit ⟨ΛG⟩ = true := by decide +kernel
theorem hello1G_a4 : A64.a4 placeCfg outLit ⟨ΛG⟩ = true := by decide +kernel
theorem hello1G_a5 : A64.a5 outLit ⟨ΛG⟩ = true := by decide +kernel
theorem hello1G_a6 : A64.a6 outLit ⟨ΛG⟩ = true := by decide +kernel
theorem hello1G_a7 : A64.a7 outLit ⟨ΛG⟩ = true := by decide +kernel
theorem hello1G_a8 : A64.a8 outLit ⟨ΛG⟩ = true := by decide +kernel
theorem hello1G_a9 : A64.a9 outLit ⟨ΛG⟩ = true := by decide +kernel
theorem hello1G_a11 : A64.a11 outLit ⟨ΛG⟩ = true := by decide +kernel
theorem hello1G_a12 : A64.a12 outLit ⟨ΛG⟩ = true := by decide +kernel

/-- **`placeOKAt` of the certificate's output at `ΛG`**, from its components. -/
theorem hello1G_placeOKAt : A64.placeOKAt placeCfg ΛG out = true := by
  rw [out_eq]
  exact A64.placeOKAt_of hello1G_a1 hello1G_a2 hello1G_a3 hello1G_a4 hello1G_a5 hello1G_a6 hello1G_a7
    hello1G_a8 hello1G_a9 hello1G_a11 hello1G_a12

theorem hello1F_a1 : A64.a1 outF ⟨ΛG⟩ = true := by decide +kernel
theorem hello1F_a2 : A64.a2 outF ⟨ΛG⟩ = true := A64.a2_of_fast (by decide +kernel)
theorem hello1F_a3 : A64.a3 outF ⟨ΛG⟩ = true := by decide +kernel
theorem hello1F_a4 : A64.a4 placeCfg outF ⟨ΛG⟩ = true := by decide +kernel
theorem hello1F_a5 : A64.a5 outF ⟨ΛG⟩ = true := by decide +kernel
theorem hello1F_a6 : A64.a6 outF ⟨ΛG⟩ = true := by decide +kernel
theorem hello1F_a7 : A64.a7 outF ⟨ΛG⟩ = true := by decide +kernel
theorem hello1F_a8 : A64.a8 outF ⟨ΛG⟩ = true := by decide +kernel
theorem hello1F_a9 : A64.a9 outF ⟨ΛG⟩ = true := by decide +kernel
theorem hello1F_a11 : A64.a11 outF ⟨ΛG⟩ = true := by decide +kernel
theorem hello1F_a12 : A64.a12 outF ⟨ΛG⟩ = true := by decide +kernel

/-- **`placeOKAt` of the output with the tail at `ΛG`**, from its components. -/
theorem hello1G_placeOKAtF : A64.placeOKAt placeCfg ΛG outF = true :=
  A64.placeOKAt_of hello1F_a1 hello1F_a2 hello1F_a3 hello1F_a4 hello1F_a5 hello1F_a6 hello1F_a7
    hello1F_a8 hello1F_a9 hello1F_a11 hello1F_a12

/-! ### The tail's side conditions -/

theorem hello1G_last : outLit.prog.getLast? = some (.label "scc_text_end") := by decide +kernel

theorem hello1G_free : ∀ i, Directive.instr i ∈ outLit.prog.dropLast →
    Spike.Lib.A64LabelCongr.Directive.Free tailLabsG (.instr i) := by
  have h : (outLit.prog.dropLast.all fun d =>
      decide (Spike.Lib.A64LabelCongr.Directive.Free tailLabsG d)) = true := by decide +kernel
  intro i hi
  exact of_decide_eq_true (List.all_eq_true.mp h _ hi)

/-! ### The statement -/

/-- The compiler's output is the certificate's literal one. -/
theorem hello1_OA_eq :
    Scc.Cert.PlaceOK.A64.Out.ofEmitted
      (Scc.Lower.A64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o) = outLit :=
  Spike.Lib.LowerA64.hello1_out_eqA.trans out_eq

open Scc.Sem in
/-- **`hello1`'s AArch64 statement after the granule pass, at `ld`'s layout
`ΛG`**: `CorrectE` at the post-pass text `asmG`, from its parse `hpa` to
the output with the tail (`hello1_finalCAG_of` at `ΛG`; the `#guard` below
checks `hpa` by compiled evaluation). -/
theorem hello1_finalCAG (hpa : Scc.Cert.Link.A64.parsesTo asmG outF.prog outF.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1
      (SrcSem.source (SrcSem.srcP1o arch Spike.Test.Hello1MainSrc.hello1o) Spike.Test.Hello1MainSrc.hello1o)
      (Spike.Lib.LowerA64.lay2 ΛG Spike.Test.Hello1MainSrc.hello1o) B asmG := by
  have h0 : A64.placeOKAt placeCfg ΛG (Scc.Cert.PlaceOK.A64.Out.ofEmitted
      (Scc.Lower.A64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)) = true :=
    Spike.Lib.LowerA64.hello1_out_eqA ▸ hello1G_placeOKAt
  have hF : A64.placeOKAt placeCfg ΛG (Spike.Lib.LowerA64.outG tailG) = true := by
    rw [Spike.Lib.LowerA64.outG, hello1_OA_eq]; exact hello1G_placeOKAtF
  have hl : (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config
      Spike.Test.Hello1MainSrc.hello1o)).prog.getLast? = some (.label "scc_text_end") := by
    rw [hello1_OA_eq]; exact hello1G_last
  have hf : ∀ i, Directive.instr i ∈ (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll
      SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)).prog.dropLast →
      Spike.Lib.A64LabelCongr.Directive.Free tailLabsG (.instr i) := by
    rw [hello1_OA_eq]; exact hello1G_free
  have hpa' : Scc.Cert.Link.A64.parsesTo asmG (Spike.Lib.LowerA64.outG tailG).prog
      (Spike.Lib.LowerA64.outG tailG).secs = true := by
    rw [Spike.Lib.LowerA64.outG, hello1_OA_eq]; exact hpa
  exact Spike.Lib.LowerA64.hello1_finalCAG_of h0 hF hl
    (fun d hd l he => by simp only [tailG, List.mem_cons, List.not_mem_nil] at hd; rcases hd with rfl | rfl | rfl | rfl | h <;> simp_all [tailLabsG])
    (fun d hd i he => by simp only [tailG, List.mem_cons, List.not_mem_nil] at hd; rcases hd with rfl | rfl | rfl | rfl | h <;> simp_all)
    hf (fun k => by cases k <;> decide +kernel) hpa' hB

-- `hpa`, by compiled evaluation: exactly `hello1_finalCAG`'s hypothesis.
#guard Scc.Cert.Link.A64.parsesTo asmG outF.prog outF.secs

end Spike.Test.Hello1LinkedA64G

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.Hello1LinkedA64G.hello1_finalCAG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.Hello1LinkedA64G.hello1_finalCAG
