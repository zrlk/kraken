/-
**`hello1`'s top-level statement** (AArch64; the twin of
`Spike/Test/X64Hello1Final.lean`): `hello1_of_closedBVBA`'s holes
(`Spike/Test/A64Hello1ClosedBVB.lean`), with the parse of the text an explicit
hypothesis checked beside it.

**Trust line.** Every correctness and placement step is kernel-checked. The
text-to-program parse (`parsesTo`: Kraken's parser and the data-section
reader on the certificate's text) is checked by compiled evaluation: the
`#guard` below, on exactly the constants of `hello1_finalA`'s `hpa`, so a
change to the text that the parse does not match breaks this module's build.
This is the trust design of `Scc/Sem/LoadA64.lean` (the kernel cannot
evaluate the parser).

- `Hello1HolesA`: the open holes, at the landings `ElH` (`ElA` at the
  setup frame's contexts `CxOkH` and bottoms `BotH`): the setup call's
  open premises `OpenSA`, `main`'s call's `MainOpenUA` and the landings'
  `H1RestA` (`H1OpenA` at the contexts' aborts `AbH`, `h1OpenA_hello1`);
- `correct2_parsed_at`: the parsed form at any instance;
- `in2A_hello1`: `In2A` at `hello1o`'s output from the holes;
- `hello1_finalA`: **the statement**: `CorrectE` at the certificate's text
  `SccCertificate.asm`, from the holes and `hpa`;
- `hello1_finalPA`: the parse-free form: `Correct` at the target on parsed
  texts (`parsedTarget`) at the compiler's output, from the holes alone; it
  gives `hello1_finalA`'s conclusion through `correct_of_parsed` and `hpa`.
-/
import Spike.Test.A64Hello1ClosedBVB
import Spike.Test.A64Hello1HU
import Spike.Lib.LowerA64.H1InNoneA
import Spike.Test.A64Hello1H1Of

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

/-- **The holes of `hello1`'s statement**: at every admissible entry state
and placement, at the landings `ElH` (the setup frame's allocations'
landings, `Spike/Test/A64Hello1CxOkH.lean`) and the write tail
`fun _ => True`, the setup call's open premises `OpenSA`, `main`'s call's
`MainOpenUA` and the landings' `H1RestA` (`H1OpenA` but its element types
and contexts' aborts) at the setup frame's code `fnCode2OfPMe`, contexts
`CxOkH` and bottoms `BotH`. -/
def Hello1HolesA : Prop :=
  ∀ E : Entry, E.Ok (lay2 LeA P1A) →
    ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true,
      OpenSA h' Spike.Lib.LowerNode.hello1o_accepted2 E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2)
        (fun _ => True) ∧
      MainOpenUA h' E (ElH h' Spike.Lib.LowerNode.hello1o_accepted2) (fun _ => True) ∧
      H1RestA h' E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h' LeA)
        (CxOkH h' Spike.Lib.LowerNode.hello1o_accepted2) (BotH h') (fun _ => True)

/-- **`In2A` at `hello1o`'s output from the holes** (`in2A_ofBVB` at the
landings `ElH`: `H1InA` by `h1InA_ofLand` at `h1OpenA_hello1`, `hS` by `hello1_hSA`, `hU` by
`hello1_hUBVA`). -/
theorem in2A_hello1 (H : Hello1HolesA) :
    ∀ E : Entry, E.Ok (lay2 LeA P1A) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true, In2A h' E := by
  intro E hE h'
  obtain ⟨hO, hU, H1⟩ := H E hE h'
  exact in2A_ofBVB h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec (by decide) hE
    ⟨_, _, h1InA_ofLand h' (h1OpenA_hello1 h' _ H1), hello1_hSA h' hO, hello1_hUBVA h' hU⟩

/-- **The parsed form at an instance** (`a64_scc_correctE_text_closedAt2_at`'s
proof before `correct_of_parsed`): `Correct` at the target on parsed texts at
the output, from `In2A` at every admissible entry state. -/
theorem correct2_parsed_at {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {Λ : Scc.Sem.Layout} (hp : Scc.Lower.Accepted2 p = true)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (H : ∀ E : Entry, E.Ok (lay2 Λ p) →
      ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true, In2A h' E)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (lay2 Λ p)) :
    Correct (parsedTarget (kernel 1) E) (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      (lay2 Λ p) B ((Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog,
        (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs) :=
  correct2_of hp h (Spike.Lib.A64.Rt.ctrZ_ofPlaceOK h) hB hE (hnum2 hp h arch) (hd2 hp h)
    (hrd2 hp h arch)
    (rest2A_ofIn h hE (H E hE h))

/-- **`hello1`'s AArch64 statement on the parsed output**: at every
admissible entry state, `Correct` at the target on parsed texts at the
compiler's output for `hello1o` (its code and data sections), from the
holes. No assembly text and no parse hypothesis (`correct2_of` at
`hello1_placeOKAt`). -/
theorem hello1_finalPA (H : Hello1HolesA)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok (lay2 LeA P1A) →
      Correct (parsedTarget (kernel 1) E)
        (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
        ((OA).prog, (OA).secs) :=
  fun _ hE => correct2_parsed_at Spike.Lib.LowerNode.hello1o_accepted2
    (hello1_out_eqA ▸ Spike.Test.Hello1LinkedA64.hello1_placeOKAt) (in2A_hello1 H) hB hE

/-- **`hello1`'s AArch64 statement**: `CorrectE` at the certificate's
assembly text, from the open holes and the parse `hpa` of the text to the
certificate's literal output `outLit` (`hello1_of_closedAt2A`, `outLit` the
compiler's output by the kernel-checked `out_eq`). Every correctness and
placement step is kernel-checked; `hpa` is checked by compiled evaluation,
the `#guard` below on the same constants. -/
theorem hello1_finalA (H : Hello1HolesA)
    (hpa : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
      SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 LeA P1A) B
      SccCertificate.asm :=
  hello1_of_closedAt2A (in2A_hello1 H) (SccCertificate.out_eq ▸ hpa) hB

-- `hpa`, by compiled evaluation: exactly `hello1_finalA`'s hypothesis.
#guard Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog
  SccCertificate.outLit.secs

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_finalPA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_finalPA

/-- info: 'Spike.Lib.LowerA64.hello1_finalA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_finalA

end Spike.Lib.LowerA64
