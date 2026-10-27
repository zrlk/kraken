/-
**`hello1`'s AArch64 statement in `hello1_finalA`'s form, from the open
list**: `hello1_finalA`'s conclusion and parse hypothesis `hpa` (at the
certificate's literal output `outLit`), its holes replaced by the `WordsNone`
chain's open premises `H1LandAWT` (the landings at the walk restricted to
the points after `rodata`'s allocation, `TrNb`, plan b1) and `OpenAHA`
(`hello1_finalAW_ofT`, `Spike/Test/A64Hello1FinalT.lean`); `hpa` moved to the compiler's output
`out` by the kernel-checked `SccCertificate.out_eq`.

- `hello1_finalA'`: the statement.
-/
import Spike.Test.A64Hello1FinalT
import Spike.Test.A64Hello1ResL
import Spike.Test.A64Hello1Final

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (FragS)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "LeA" => Spike.Test.Hello1LinkedA64.Λe

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

/-- **`hello1`'s AArch64 statement, `hello1_finalA`'s conclusion and
`hpa`**, from the open list: the landings' remaining premises `H1LandAWT`
at `Tr := TrNb (TailAt2 P1A j)` (`hAW`, `hTr`, `hresL`, `hresS`, `hbot`) and the
allocator's `W2` instance at the setup frame `OpenAHA`, at every entry and
placement check (`hello1_finalAW_ofT`; `hpa` at `out` by
`SccCertificate.out_eq`). -/
theorem hello1_finalA'
    (H1 : ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      H1LandAWT h' E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA)
        (CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2) (BotH h') (fun _ => True)
        (fun j => TrNb (Spike.Lib.LowerNode.TailAt2 P1A j)))
    (HA : ∀ E : Entry, E.Ok (lay2 LeA P1A) → ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenAHA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True))
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
      SccCertificate.asm :=
  hello1_finalAW_ofT H1 HA (SccCertificate.out_eq ▸ hpa) hB

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_finalA'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalA'
