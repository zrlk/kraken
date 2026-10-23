import Spike.Lib.LowerX64.Correct
import Spike.Test.Cert.X64Ret0Cert

/-!
# The x86-64 compiler theorem at `ret0`'s certificate

`x64_scc_correct` instantiated with the facts `ret0`'s generated certificate
(`Spike/Test/Cert/X64Ret0Cert.lean`) proves: its acceptance
(`prog_accepted`) and its placement check at the assembler's sizes and label
offsets (`prog_placeOK`, at its configuration, the canonical one). What
remains are the theorem's temporary premises. On the text, the certificate's parse check is a
premise (`x64_scc_correct_text`).
-/

namespace Spike.Lib.LowerX64.Test

/-- The certificate's placement configuration (the theorems take any; this
one is the canonical one). -/
example : SccCertificate.placeCfg = Scc.Cert.PlaceOK.Config.canonical := rfl

/-- **`ret0`'s certificate gives the compiler theorem's premises.** -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch) :=
  x64_scc_correct (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B) (arch := arch)
    SccCertificate.prog_accepted
    SccCertificate.prog_placeOK

/-- **On `ret0`'s text**: the certificate's parse check (a compiled `#guard`,
the trust boundary) is the premise `hpa`. -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.out.prog SccCertificate.out.secs = true) :=
  x64_scc_correct_text (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B) (arch := arch)
    SccCertificate.prog_accepted
    SccCertificate.prog_placeOK hpa

/-- **At every admissible entry state** (`x64_scc_correctE_text`): on
`ret0`'s text, `Scc.Sem.X64.CorrectE` from the certificate's facts. -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.out.prog SccCertificate.out.secs = true) :=
  x64_scc_correctE_text (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B) (arch := arch)
    SccCertificate.prog_accepted
    SccCertificate.prog_placeOK hpa

/-- **Closed, at every admissible entry state** (`x64_scc_correctE_text_closed`):
on `ret0`'s text, `Scc.Sem.X64.CorrectE` from `Accepted0`, the placement
check and the parse check alone; `hgen` is discharged (`hgen_ofPlaceOK`). -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.out.prog SccCertificate.out.secs = true) :=
  x64_scc_correctE_text_closed (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B)
    (arch := arch) SccCertificate.prog_accepted SccCertificate.prog_placeOK hpa

/-- **`CorrectE` is not vacuous at `ret0`'s certificate**: the witness entry
state (the 64 KiB stack at `2 ^ 32`, not Linux's) is admissible at the
theorem's layout (at any immediates), from the placement check alone. -/
example (i : CoreTerm.Expr → String → Nat → Option Nat) : Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
    (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK (Scc.Cert.PlaceOK.X64.atTables SccCertificate.prog_placeOK) i).Λ :=
  Spike.Lib.X64.Rt.RuntimeLayout.witness_ok_ofPlaceOK _ _

example : (⟨⟨2 ^ 32, 65536⟩⟩ : Scc.Sem.Entry).stack.lo ≠ Scc.Sem.Entry.linux.stack.lo := by decide

/-- **The closed theorem at the witness entry state** (non-Linux stack): on
`ret0`'s text, `Correct` over the target at `⟨⟨2 ^ 32, 65536⟩⟩`, from the
certificate's facts and `witness_ok_ofPlaceOK`; no premise is left. -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.out.prog SccCertificate.out.secs = true) :=
  show Scc.Sem.Correct (Scc.Sem.X64.target (Scc.Sem.X64.kernel 1) ⟨⟨2 ^ 32, 65536⟩⟩)
      (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src) _ B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ from
  x64_scc_correctE_text_closed (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B)
    (arch := arch) SccCertificate.prog_accepted SccCertificate.prog_placeOK hpa _
    (Spike.Lib.X64.Rt.RuntimeLayout.witness_ok_ofPlaceOK
      (Scc.Cert.PlaceOK.X64.atTables SccCertificate.prog_placeOK) _)

end Spike.Lib.LowerX64.Test
