/-
**`hello1`'s x86-64 statement from the per-allocation premises alone**:
`hello1_final'`'s conclusion and parse hypothesis `hpa`, its only open
premise the allocator's per-allocation `AllocPtW` at the landings'
contexts (`OpenAPt`): `hello1_finalTW` (`Spike/Test/X64Hello1ResI.lean`,
the landings' rest closed) at `OpenAWF` by `hello1_hAW_none`
(`Spike/Test/X64Hello1HAWNone.lean`).

- `hello1_finalC`: the statement, closed (`hello1_finalC_of` at `hello1_allocPt`).
- `hello1_finalC_of`: the statement from `OpenAPt` at every entry and
  placement check.
-/
import Spike.Test.X64Hello1ResI
import Spike.Test.X64Hello1HAWNone
import Spike.Test.X64Hello1AllocPt

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

/-- **`hello1`'s x86-64 statement, `hello1_final`'s conclusion and `hpa`,
from the per-allocation premises**: the allocator's per-allocation
`AllocPtW` at the landings' contexts (`OpenAPt` at the landings `ElH` and
the write tail `fun _ => True`) at every entry and placement check
(`hello1_finalTW` at `hello1_hAW_none`). -/
theorem hello1_finalC_of
    (HP : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenAPt h Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h) (fun _ => True))
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_finalTW (hello1_hAW_none HP) hpa hB

/-- **`hello1`'s x86-64 statement, closed**: `hello1_finalC_of` at the per-allocation
premises `hello1_allocPt`. -/
theorem hello1_finalC
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_finalC_of hello1_allocPt hpa hB

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_finalC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_finalC_of

/-- info: 'Spike.Lib.LowerX64.hello1_finalC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_finalC
