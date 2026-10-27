/-
**`hello1`'s AArch64 holes reduced to the setup call's** (the twin of
`Spike/Test/X64Hello1Reduce.lean`): `main`'s call's open premises
`MainOpenUA` are closed (`hello1_mainPreUAT` at the branch targets' check
`hello1_mainTgA`, at the write tail `fun _ => True`), so `Hello1HolesA`
(`Spike/Test/A64Hello1Final.lean`) follows from the setup call's open
premises `OpenSA` and the landings' `H1RestA` (at `ElH`).

- `hello1_mainOpenUA`: `MainOpenUA` at `hello1o`, every entry and landing;
- `hello1_holesA_of`: `Hello1HolesA` from `OpenSA` and the landings' `H1RestA` (at `ElH`) at every
  admissible entry and placement;
- `hello1_holesA_ofP`: from the setup frame's remaining premises `OpenPA` (`openSA_of_openPA`) and `H1RestA`.
-/
import Spike.Test.A64Hello1Final
import Spike.Test.A64Hello1TgOk
import Spike.Test.A64Hello1SetupOpenOf

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (FragS)
open Spike.Lib.A64Consumer (Lbl Lsize)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

/-- **`MainOpenUA` at `hello1o`** at the write tail `fun _ => True`
(`hello1_mainPreUAT` at `hello1_mainTgA`; its landing premises are
trivial). -/
theorem hello1_mainOpenUA (h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) :
    MainOpenUA h E El (fun _ => True) :=
  fun _ _ _ _ _ _ _ _ _ hB J _ =>
    hello1_mainPreUAT h hB J (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (hello1_mainTgA h)

/-- **`Hello1HolesA` from the setup call's open premises and the
landings'** (at the landings `ElH`; `main`'s by `hello1_mainOpenUA`). -/
theorem hello1_holesA_of (hS : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
    ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenSA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True))
    (hL : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
        H1RestA h' E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA)
          (CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2) (BotH h') (fun _ => True)) :
    Hello1HolesA :=
  fun E hE h' => ⟨hS E hE h', hello1_mainOpenUA h' E _, hL E hE h'⟩

/-- **`Hello1HolesA` from the setup frame's remaining premises and the
landings'** (`OpenPA`: `SetupPreA`'s `hwn`, `hAW`, `habA`;
`hello1_holesA_of` at `openSA_of_openPA`). -/
theorem hello1_holesA_ofP (hP : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
    ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenPA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True))
    (hL : ∀ E : Entry, E.Ok (lay2 LeA P1A) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
        H1RestA h' E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA)
          (CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2) (BotH h') (fun _ => True)) :
    Hello1HolesA :=
  hello1_holesA_of (fun E hE h' => openSA_of_openPA h' (hP E hE h')) hL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_mainOpenUA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_mainOpenUA

/-- info: 'Spike.Lib.LowerA64.hello1_holesA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_holesA_of

/-- info: 'Spike.Lib.LowerA64.hello1_holesA_ofP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_holesA_ofP
