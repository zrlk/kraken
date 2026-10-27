/-
**`hello1`'s AArch64 statement on the `WordsNone` chain from the landings'
open premises at a walk restriction** (plan b1): `hello1_of_closedBVBFAU`
(`Spike/Test/A64Hello1ClosedBVBF.lean`) at the landings `ElH`
(`Spike/Test/A64Hello1CxOkH.lean`) from `H1LandAWT`
(`Spike/Lib/LowerA64/H1LandAWT.lean`) at any walk restriction `Tr`: `H1InAW`
by `h1InAW_ofLandT` (the element types `hello1_hTnA`, the aborts
`hello1_hAbQA`), the setup call `HSBVFA` from `OpenAHA`
(`hello1_hSFA_ofPreH` at `openPHA_of_openAHA`,
`Spike/Test/A64Hello1HolesW.lean`).

- `hello1_finalAW_ofT`: `CorrectE` at the certificate's text from
  `H1LandAWT`, `OpenAHA` and the parse `hpa` at the landings `ElH`.
-/
import Spike.Test.A64Hello1HolesW
import Spike.Test.A64Hello1HAbQ
import Spike.Test.A64Hello1H1Of
import Spike.Lib.LowerA64.H1LandAWT

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (FragS)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "LeA" => Λx

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

/-- **`hello1`'s AArch64 statement from the landings' open premises at a
walk restriction `Tr` and the allocator's `W2` instance**
(`hello1_of_closedBVBFAU`: `H1InAW` by `h1InAW_ofLandT` at `hello1_hTnA`
and `hello1_hAbQA`, `HSBVFA` by `hello1_hSFA_ofPreH` at
`openPHA_of_openAHA`): `hello1_finalA`'s conclusion, the parse `hpa` at
the certificate's output `out`. -/
theorem hello1_finalAW_ofT
    (h0 : placeOKAt SccCertificate.placeCfg LeA OA = true)
    {Tr : Nat → Expr → Prop}
    (H1 : ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      H1LandAWT h' E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA)
        (CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2) (BotH h') (fun _ => True) Tr)
    (HA : ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenAHA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True))
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
      SccCertificate.asm :=
  hello1_of_closedBVBFAU h0 (fun E hE h' => ⟨ElH h' Spike.Lib.LowerNode.hello1o_accepted2,
    h1InAW_ofLandT h' (H1 E hE h') hello1_hTnA
      (fun J _ _ _ _ _ _ _ _ _ => hello1_hAbQA h' rfl Spike.Lib.LowerNode.hello1o_accepted2
        hello1_htyA.choose_spec (fun _ _ _ _ _ _ => trivial) J _ _),
    hello1_hSFA_ofPreH h' (openPHA_of_openAHA h' _ hello1_htyA.choose_spec (HA E hE h'))⟩) hpa hB

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_finalAW_ofT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalAW_ofT
