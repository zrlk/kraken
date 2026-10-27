/-
**`hello1` from the segment obligations** (AArch64): `hello1o`'s instance
of `a64_scc_correctE_text_closedAt2_at` (`Spike/Lib/LowerA64/Closed2AtA.lean`)
at any layout passing the placement check, as `hello1_of_closed2A`
(`Spike/Test/A64Hello1Closed2.lean`) instantiates `Closed2StmtA`: what is left
is `In2A` (`H0InA`, `H1InA`) at `hello1o`'s output and the parse check `hpa`.

- `hello1_of_closedAt2A`: the statement at `hello1o` from `In2A` at its
  admissible entry states.
-/
import Spike.Lib.LowerA64.Closed2AtA
import Spike.Test.A64Hello1Closed2

namespace Spike.Lib.LowerA64

open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- **`hello1` from its segment obligations**: `hello1o` is `Accepted2`
(`hello1o_accepted2`) with `mainRetOk` and `CfgNeedOkA` by `decide`, its
output passing the placement check at the layout (`h0`, at the compiler's
output); left, `In2A` at every admissible entry state (`H`) and the parse
`hpa` (the certificate's compiled `#guard`). -/
theorem hello1_of_closedAt2A {Λx : Scc.Sem.Layout}
    (h0 : placeOKAt SccCertificate.placeCfg Λx
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)) = true)
    (H : ∀ E : Entry, E.Ok (lay2 Λx Spike.Test.Hello1MainSrc.hello1o) →
      ∀ h' : placeOKAt SccCertificate.placeCfg
        (lay2 Λx Spike.Test.Hello1MainSrc.hello1o)
        (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)) = true,
      In2A h' E)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.A64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch Spike.Test.Hello1MainSrc.hello1o)
        Spike.Test.Hello1MainSrc.hello1o)
      { Λx with
        static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me
          Λx Spike.Test.Hello1MainSrc.hello1o } B
      SccCertificate.asm :=
  a64_scc_correctE_text_closedAt2_at Spike.Lib.LowerNode.hello1o_accepted2 (by decide)
    h0 (by decide) H (hello1_out_eqA ▸ hpa) hB

/--
info: 'Spike.Lib.LowerA64.hello1_of_closedAt2A' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_of_closedAt2A

end Spike.Lib.LowerA64
