/-
**`hello1`'s AArch64 statement from the per-allocation premises alone**:
`hello1_finalA'`'s conclusion and parse hypothesis `hpa`, its only open
premise the allocator's per-allocation `AllocPtW` at the landings'
contexts (`OpenAPtA`): `hello1_finalTWA` (`Spike/Test/A64Hello1H1T.lean`,
the landings' rest closed) at `OpenAHA` by `hello1_hAW_noneA`
(`Spike/Test/A64Hello1HAWNone.lean`).

- `hello1_finalCA`: the statement, closed (`hello1_finalCA_of` at `hello1_openAPtA`).
- `hello1_finalCA_of`: the statement from `OpenAPtA` at every entry and
  placement check.
-/
import Spike.Test.A64Hello1H1T
import Spike.Test.A64Hello1HAWNone
import Spike.Test.A64Hello1HA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

/-- **`hello1`'s AArch64 statement, `hello1_finalA`'s conclusion and `hpa`,
from the per-allocation premises**: the allocator's per-allocation
`AllocPtW` at the landings' contexts (`OpenAPtA` at the landings `ElH` and
the write tail `fun _ => True`) at every entry and placement check
(`hello1_finalTWA` at `hello1_hAW_noneA`). -/
theorem hello1_finalCA_of
    (HP : ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenAPtA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True))
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
      SccCertificate.asm :=
  hello1_finalTWA (hello1_hAW_noneA HP) hpa hB

/-- **`hello1`'s AArch64 statement, closed**: `hello1_finalCA_of` at the per-allocation
premises `hello1_openAPtA`. -/
theorem hello1_finalCA
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
      SccCertificate.asm :=
  hello1_finalCA_of hello1_openAPtA hpa hB

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_finalCA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalCA_of

/-- info: 'Spike.Lib.LowerA64.hello1_finalCA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalCA
