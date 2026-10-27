/-
**`hello1` from the segment obligations** (x86-64): `hello1o`'s instance
of `x64_scc_correctE_text_closedAt2_at` (`Spike/Lib/LowerX64/Closed2At.lean`)
at `ld`'s layout of the linked executable, as `hello1_of_closed2`
(`Spike/Test/X64Hello1Closed2.lean`) instantiates `Closed2Stmt`: what is left
is `In2X` (`H0In`, `H1In`) at `hello1o`'s output and the parse check `hpa`.

- `hello1_of_closedAt2`: the statement at `hello1o` from `In2X` at its
  admissible entry states.
-/
import Spike.Lib.LowerX64.Closed2At
import Spike.Test.X64Hello1Closed2

namespace Spike.Lib.LowerX64

open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **`hello1` from its segment obligations**: `hello1o` is `Accepted2`
(`hello1o_accepted2`) with `mainRetOk` and `CfgNeedOk` by `decide`, its
output the certificate's (`hello1_out_eq`) passing the placement check at
`ld`'s layout `Λe` (`hello1_placeOKAt`); left, `In2X` at every admissible
entry state (`H`) and the parse `hpa` (the certificate's compiled `#guard`). -/
theorem hello1_of_closedAt2
    (H : ∀ E : Entry, E.Ok (lay2 Spike.Test.Hello1LinkedX64.Λe Spike.Test.Hello1MainSrc.hello1o) →
      ∀ h' : placeOKAt SccCertificate.placeCfg
        (lay2 Spike.Test.Hello1LinkedX64.Λe Spike.Test.Hello1MainSrc.hello1o)
        (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)
          SccCertificate.sizes SccCertificate.labelOffs) = true,
      In2X h' E)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch Spike.Test.Hello1MainSrc.hello1o)
        Spike.Test.Hello1MainSrc.hello1o)
      { Spike.Test.Hello1LinkedX64.Λe with
        static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me
          Spike.Test.Hello1LinkedX64.Λe Spike.Test.Hello1MainSrc.hello1o } B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  x64_scc_correctE_text_closedAt2_at Spike.Lib.LowerNode.hello1o_accepted2 (by decide)
    (hello1_out_eq ▸ Spike.Test.Hello1LinkedX64.hello1_placeOKAt) (by decide) H (hello1_out_eq ▸ hpa) hB

/--
info: 'Spike.Lib.LowerX64.hello1_of_closedAt2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_of_closedAt2

end Spike.Lib.LowerX64
