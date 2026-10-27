import Spike.Lib.LowerA64.Correct
import Spike.Test.Cert.A64Hello1Cert

/-!
# The closed AArch64 compiler theorem does not reach `hello1`'s certificate

`a64_scc_correctE_text_closed` takes a one-declaration program `[d]` that is
`Accepted0` and whose output passes `placeOK`. `hello1.w`'s generated
certificate (`Spike/Test/Cert/A64Hello1Cert.lean`) proves the placement
(`prog_placeOK`) but not the rest: its source has three declarations
(`print`, `rodata`, `main`) and it is outside `Accepted0`
(`prog_not_accepted`). So the theorem is not applicable there (placement
holds, no correctness claim); these checks keep that visible until the
fragment grows.
-/

namespace Spike.Lib.LowerA64.Hello1Test

/-- `hello1`'s source is not of the theorem's shape `[d]`. -/
example : SccCertificate.prog_src.length = 3 := by decide +kernel

/-- **No program of the theorem's shape is `hello1`'s source.** -/
example : ∀ d : CoreTerm.Decl, SccCertificate.prog_src ≠ [d] := by
  intro d h
  have h3 : SccCertificate.prog_src.length = 3 := by decide +kernel
  rw [h] at h3
  simp at h3

/-- **`Accepted0` fails** on `hello1`'s source. -/
example : Scc.Lower.Accepted0 SccCertificate.prog_src ≠ true := by
  rw [SccCertificate.prog_not_accepted]; decide

/-- `placeOK` holds on `hello1`'s output at its configuration: only the
shape and `Accepted0` keep the theorem out. -/
example : Scc.Cert.PlaceOK.A64.placeOK SccCertificate.placeCfg SccCertificate.out = true :=
  SccCertificate.prog_placeOK

end Spike.Lib.LowerA64.Hello1Test
