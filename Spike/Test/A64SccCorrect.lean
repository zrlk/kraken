import Spike.Lib.LowerA64.Correct
import Spike.Test.Cert.A64Ret0Cert

/-!
# The AArch64 compiler theorem at `ret0`'s certificate

`a64_scc_correct` instantiated with the facts `ret0`'s generated certificate
(`Spike/Test/Cert/A64Ret0Cert.lean`) proves: its acceptance
(`prog_accepted`) and its placement check (`prog_placeOK`, at its
configuration, the canonical one). What remains are the theorem's
temporary premises. On the text `asm`, the certificate's parse check is a
premise (`a64_scc_correct_text`).
-/

namespace Spike.Lib.LowerA64.Test

/-- The certificate's placement configuration (the theorems take any; this
one is the canonical one). -/
example : SccCertificate.placeCfg = Scc.Cert.PlaceOK.Config.canonical := rfl

/-- **`ret0`'s certificate gives the compiler theorem's premises.** -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch) :=
  a64_scc_correct (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B) (arch := arch)
    SccCertificate.prog_accepted
    SccCertificate.prog_placeOK

/-- **On `ret0`'s text**: the certificate's parse check (a compiled `#guard`,
the trust boundary) is the premise `hpa`. -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true) :=
  a64_scc_correct_text (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B) (arch := arch)
    SccCertificate.prog_accepted
    SccCertificate.prog_placeOK hpa

/-- **At every admissible entry state** (`a64_scc_correctE_text`): on
`ret0`'s text, `Scc.Sem.A64.CorrectE` from the certificate's facts. -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true) :=
  a64_scc_correctE_text (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B) (arch := arch)
    SccCertificate.prog_accepted
    SccCertificate.prog_placeOK hpa

/-- **Closed, at every admissible entry state** (`a64_scc_correctE_text_closed`):
on `ret0`'s text, `Scc.Sem.A64.CorrectE` from `Accepted0`, the placement
check and the parse check alone; `hgen` is discharged (`hgen_ofPlaceOK`). -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true) :=
  a64_scc_correctE_text_closed (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B)
    (arch := arch) SccCertificate.prog_accepted SccCertificate.prog_placeOK hpa

/-- **`CorrectE` is not vacuous at `ret0`'s certificate**: the witness entry
state (the 64 KiB stack at `2 ^ 32`, not Linux's) is admissible at the
theorem's layout (at any immediates), from the placement check alone. -/
example (i : CoreTerm.Expr → String → Nat → Option Nat) : Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables SccCertificate.prog_placeOK) i).Λ :=
  Spike.Lib.A64.Rt.RuntimeLayout.witness_ok_ofPlaceOK _ _

example : (⟨⟨2 ^ 32, 65536⟩⟩ : Scc.Sem.Entry).stack.lo ≠ Scc.Sem.Entry.linux.stack.lo := by decide

/-- **The closed theorem at the witness entry state** (non-Linux stack): on
`ret0`'s text, `Correct` over the target at `⟨⟨2 ^ 32, 65536⟩⟩`, from the
certificate's facts and `witness_ok_ofPlaceOK`; no premise is left. -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true) :=
  show Scc.Sem.Correct (Scc.Sem.A64.target (Scc.Sem.A64.kernel 1) ⟨⟨2 ^ 32, 65536⟩⟩)
      (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src) _ B SccCertificate.asm from
  a64_scc_correctE_text_closed (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B)
    (arch := arch) SccCertificate.prog_accepted SccCertificate.prog_placeOK hpa _
    (Spike.Lib.A64.Rt.RuntimeLayout.witness_ok_ofPlaceOK (Scc.Cert.PlaceOK.A64.atTables SccCertificate.prog_placeOK) _)

/-- **At any layout passing the placement check** (`a64_scc_correctE_text_closedAt`):
on `ret0`'s text, at the certificate's layout (`tablesOf placeCfg out`, where
`prog_placeOK` is the check), with no static label. -/
example (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true) :=
  a64_scc_correctE_text_closedAt (cfg := SccCertificate.config) (pcfg := SccCertificate.placeCfg) (B := B)
    (arch := arch) _ SccCertificate.prog_accepted (Scc.Cert.PlaceOK.A64.atTables SccCertificate.prog_placeOK) hpa

/-- `ret0`'s one declaration, `main`. -/
abbrev ret0Main : CoreTerm.Decl := SccCertificate.prog_src.head (by decide)

/-- **The same at the witness entry state** (non-Linux stack), at a layout
`Λ` passing the check: `Correct` at `⟨⟨2 ^ 32, 65536⟩⟩`, given it is
admissible there. -/
example (Λ : Scc.Sem.Layout) (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (h : Scc.Cert.PlaceOK.A64.placeOKAt SccCertificate.placeCfg Λ SccCertificate.out = true)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true)
    (hE : Scc.Sem.Entry.Ok ⟨⟨2 ^ 32, 65536⟩⟩
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf ret0Main }) :=
  a64_scc_correctE_text_closedAt (cfg := SccCertificate.config) (B := B) (arch := arch) Λ
    SccCertificate.prog_accepted h hpa _ hE

end Spike.Lib.LowerA64.Test
