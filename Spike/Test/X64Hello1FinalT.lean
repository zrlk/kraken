/-
**`hello1`'s x86-64 statement from the landings' open premises on the
walk past the landed allocations** (b1): `hello1_of_closedBVBF`
(`Spike/Test/X64Hello1ClosedBVBF.lean`) at the landings `ElH`
(`Spike/Test/X64Hello1FinalW.lean`) from `H1RestXWT`
(`Spike/Lib/LowerX64/H1InLandWT.lean`): `H1InW` by `h1InW_ofLandT` at
`H1RestXWT.toOpen` (the element types `hello1_hTn`, the aborts ending
nowhere `hello1_hAbQ`), the setup call `HSBVF` from `OpenAWF` alone
(`hello1_hSF_ofPre` at `openPF_of_openAWF`,
`Spike/Test/X64Hello1HolesW.lean`), `main`'s call `hello1_hUBVF`.

`H1RestXW.hres` asks the full `ResumeCx2` at the extended placement, so
`NewBufC` at `rodata`'s own allocation there (unsatisfiable at a placed
label, see `Spike/Lib/LowerX64/H1InLandWT.lean`); `H1RestXWT` asks the
landing's context only on the walk past the landed allocation
(`ResumeCx2T` at `Tr`).

- `hello1_h1OpenXWT`: `H1OpenXWT` at `GX` from `H1RestXWT`;
- `hello1_finalW_ofT`: `CorrectE` at the certificate's text from
  `H1RestXWT`, `OpenAWF` and the parse `hpa`.
-/
import Spike.Lib.LowerX64.H1InLandWT
import Spike.Lib.LowerX64.H1RestXW
import Spike.Test.X64Hello1HolesW
import Spike.Test.X64Hello1HAbQ
import Spike.Test.X64Hello1H1Of

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (FragS)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "Le" => Λx

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

/-- **`H1OpenXWT` from `H1RestXWT`** at `hello1o` (`H1RestXWT.toOpen`: the
element types `hello1_hTn`, the aborts ending nowhere `hello1_hAbQ`). -/
theorem hello1_h1OpenXWT {E : Entry} (h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true)
    {Tr : Nat → Expr → Prop}
    (HR : H1RestXWT h E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le)
      (CxOkH h Spike.Lib.LowerNode.hello1o_accepted2) (BotH h) (fun _ => True) Tr) :
    ∃ Ab₀ : FragS isa, H1OpenXWT h E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le)
      (CxOkH h Spike.Lib.LowerNode.hello1o_accepted2) (BotH h) (fun _ => True) Ab₀ Tr :=
  ⟨_, HR.toOpen h hello1_hTn fun J _ _ _ _ _ _ _ _ _ =>
    hello1_hAbQ h rfl Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec
      (fun _ _ _ _ _ _ => trivial) J _ _⟩

/-- **`hello1`'s x86-64 statement from `H1RestXWT` and `OpenAWF`**
(`hello1_of_closedBVBF`: `H1InW` by `h1InW_ofLandT` at
`hello1_h1OpenXWT`, `HSBVF` by `hello1_hSF_ofPre` at `openPF_of_openAWF`,
`HUBVF` by `hello1_hUBVF`), at any restriction `Tr`. -/
theorem hello1_finalW_ofT
    (h0 : placeOKAt SccCertificate.placeCfg Le
      (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)
        SccCertificate.sizes SccCertificate.labelOffs) = true)
    {Tr : Nat → Expr → Prop}
    (HR : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      H1RestXWT h E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le)
        (CxOkH h Spike.Lib.LowerNode.hello1o_accepted2) (BotH h) (fun _ => True) Tr)
    (HA : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenAWF h Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h) (fun _ => True))
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.out.prog SccCertificate.out.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    Scc.Sem.X64.CorrectE 1
      (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1)
      { Le with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Le P1 } B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_of_closedBVBF h0 (fun E hE h => ⟨ElH h, fun _ => True,
    h1InW_ofLandT h (hello1_h1OpenXWT h (HR E hE h)).choose_spec,
    hello1_hSF_ofPre h (openPF_of_openAWF h _ hello1_hty.choose_spec (HA E hE h)),
    hello1_hUBVF h E _⟩) hpa hB

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_h1OpenXWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_h1OpenXWT

/-- info: 'Spike.Lib.LowerX64.hello1_finalW_ofT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_finalW_ofT
