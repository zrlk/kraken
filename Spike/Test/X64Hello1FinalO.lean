/-
**`hello1`'s x86-64 statement in `hello1_final`'s form, from the open list**:
`hello1_final`'s conclusion and parse hypothesis `hpa` (at the certificate's
literal output `outLit`), its holes replaced by the `WordsNone` chain's open
premises `H1RestXWT` (at `Tr := fun j => TrNb (TailAt2 P1 j)`) and `OpenAWF`
(`hello1_finalW_ofT`, `Spike/Test/X64Hello1FinalT.lean`; `H1RestXW`'s `hres`
needs `NewBufC` at the extended placement, unsatisfiable, see
`Spike/Lib/LowerX64/H1InLandWT.lean`); `hpa` moved to the compiler's output
`out` by the kernel-checked `SccCertificate.out_eq`.

- `hello1_final'_gen`: the statement at every layout passing the placement check;
- `hello1_final'`: the statement (`hello1_final'_gen` at `ld`'s layout).
-/
import Spike.Test.X64Hello1FinalT
import Spike.Test.X64Hello1ResT
import Spike.Test.X64Hello1Final

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (FragS)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout of the generic statements: any layout at which the placement check passes (`hΛ`). -/
local notation "Lg" => Λx

/-- **`hello1_final'` at every layout at which the placement check passes** (`hΛ`, at the
compiler's output): `hello1_finalW_ofT` at `hΛ`. -/
theorem hello1_final'_gen
    (hΛ : placeOKAt SccCertificate.placeCfg Lg OX = true)
    (HR : ∀ E : Entry, E.Ok (lay2 Lg P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Lg P1) OX = true,
      H1RestXWT h E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Lg)
        (CxOkH h Spike.Lib.LowerNode.hello1o_accepted2) (BotH h) (fun _ => True)
        (fun j => TrNb (Spike.Lib.LowerNode.TailAt2 P1 j)))
    (HA : ∀ E : Entry, E.Ok (lay2 Lg P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Lg P1) OX = true,
      OpenAWF h Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h) (fun _ => True))
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Lg P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_finalW_ofT hΛ HR HA (SccCertificate.out_eq ▸ hpa) hB

/-- **`hello1`'s x86-64 statement, `hello1_final`'s conclusion and `hpa`**,
from the open list: the landings' remaining premises `H1RestXWT` (`hAW`,
`hTr`, `hresL`, `hresS`, `hbot`) at the restriction to the walk past
`rodata`'s allocation (`TrNb (TailAt2 P1 j)`) and the allocator's `W2`
instance at the setup frame `OpenAWF`, at every entry and placement check
(`hello1_final'_gen` at `ld`'s layout, `hello1_placeOKAt`). -/
theorem hello1_final'
    (HR : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      H1RestXWT h E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le)
        (CxOkH h Spike.Lib.LowerNode.hello1o_accepted2) (BotH h) (fun _ => True)
        (fun j => TrNb (Spike.Lib.LowerNode.TailAt2 P1 j)))
    (HA : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenAWF h Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h) (fun _ => True))
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_final'_gen (hello1_out_eq ▸ Spike.Test.Hello1LinkedX64.hello1_placeOKAt) HR HA hpa hB

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_final'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_final'

/-- info: 'Spike.Lib.LowerX64.hello1_final'_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_final'_gen
