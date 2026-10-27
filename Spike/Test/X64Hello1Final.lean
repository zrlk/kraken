/-
**`hello1`'s top-level statement** (x86-64; the twin of
`Spike/Test/A64Hello1Final.lean`): `hello1_of_closedBVB`'s holes
(`Spike/Test/X64Hello1ClosedBVB.lean`), with the parse of the text an explicit
hypothesis checked beside it.

**Trust line.** Every correctness and placement step is kernel-checked. The
text-to-program parse (`parsesTo`: Kraken's parser and the data-section
reader on the certificate's text) is checked by compiled evaluation: the
`#guard` below, on exactly the constants of `hello1_final`'s `hpa`, so a
change to the text that the parse does not match breaks this module's build.
This is the trust design of `Scc/Sem/LoadX64.lean` (the kernel cannot
evaluate the parser).

- `Hello1Holes`: the open holes, at no landings: the setup call's open
  premises `OpenS` and `main`'s call's `MainOpenU`;
- `correct2_parsed_at`: the parsed form at any instance;
- `in2X_hello1`: `In2X` at `hello1o`'s output from the holes;
- `hello1_final`: **the statement**: `CorrectE` at the certificate's text
  `⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩`, from the holes and `hpa`;
- `hello1_finalP`: the parse-free form: `Correct` at the target on parsed
  texts (`parsedTarget`) at the compiler's output, from the holes alone; it
  gives `hello1_final`'s conclusion through `correct_of_parsed` and `hpa`.
-/
import Spike.Test.X64Hello1ClosedBVB
import Spike.Test.X64Hello1HS
import Spike.Test.X64Hello1HU
import Spike.Lib.LowerX64.H1InNone

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

/-- **The holes of `hello1`'s statement**: at every admissible entry state
and placement, at no landings (`hello1o` allocates nothing, so `H1In` is
`h1In_none`), the write tail `fun _ => True`, the setup call's open
premises `OpenS` and `main`'s call's `MainOpenU`. -/
def Hello1Holes : Prop :=
  ∀ E : Entry, E.Ok (lay2 Le P1) →
    ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenS h' Spike.Lib.LowerNode.hello1o_accepted2 E (fun _ _ _ _ _ _ _ _ => False) (fun _ => True) ∧
      MainOpenU h' E (fun _ _ _ _ _ _ _ _ => False) (fun _ => True)

/-- **`In2X` at `hello1o`'s output from the holes** (`in2X_ofBVB` at no
landings: `H1In` by `h1In_none`, `hS` by `hello1_hS`, `hU` by
`hello1_hUBV`). -/
theorem in2X_hello1 (H : Hello1Holes) :
    ∀ E : Entry, E.Ok (lay2 Le P1) →
      ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true, In2X h' E := by
  intro E hE h'
  obtain ⟨hO, hU⟩ := H E hE h'
  exact in2X_ofBVB h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec (by decide) hE
    ⟨_, _, h1In_none h' E _, hello1_hS h' hO, hello1_hUBV h' hU⟩

/-- **The parsed form at an instance** (`x64_scc_correctE_text_closedAt2_at`'s
proof before `correct_of_parsed`): `Correct` at the target on parsed texts at
the output, from `In2X` at every admissible entry state. -/
theorem correct2_parsed_at {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}
    {Λ : Scc.Sem.Layout} {sizes : List Nat} {labelOffs : List (String × Nat)} (hp : Scc.Lower.Accepted2 p = true)
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (H : ∀ E : Entry, E.Ok (lay2 Λ p) →
      ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true, In2X h' E)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch}
    {E : Entry} (hE : E.Ok (lay2 Λ p)) :
    Correct (parsedTarget (kernel 1) E) (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      (lay2 Λ p) B ((Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog,
        (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs,
        (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).labelOffs) :=
  correct2_of hp h (Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h) hB hE (hnum2 hp h arch) (hd2 hp h) (hrd2 hp h arch)
    (rest2X_ofIn h hE (H E hE h))

/-- **`hello1`'s x86-64 statement on the parsed output**: at every
admissible entry state, `Correct` at the target on parsed texts at the
compiler's output for `hello1o` (its cells, data sections and label
offsets), from the holes. No assembly text and no parse hypothesis
(`correct2_of` at `hello1_placeOKAt`). -/
theorem hello1_finalP (H : Hello1Holes)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    ∀ E : Entry, E.Ok (lay2 Le P1) →
      Correct (parsedTarget (kernel 1) E)
        (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
        ((OX).prog, (OX).secs, (OX).labelOffs) :=
  fun _ hE => correct2_parsed_at Spike.Lib.LowerNode.hello1o_accepted2
    (hello1_out_eq ▸ Spike.Test.Hello1LinkedX64.hello1_placeOKAt) (in2X_hello1 H) hB hE

/-- **`hello1`'s x86-64 statement**: `CorrectE` at the certificate's
assembly text, from the open holes and the parse `hpa` of the text to the
certificate's literal output `outLit` (`hello1_of_closedAt2`, `outLit` the
compiler's output by the kernel-checked `out_eq`). Every correctness and
placement step is kernel-checked; `hpa` is checked by compiled evaluation,
the `#guard` below on the same constants. -/
theorem hello1_final (H : Hello1Holes)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
      SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1) P1) (lay2 Le P1) B
      ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩ :=
  hello1_of_closedAt2 (hello1_out_eq ▸ Spike.Test.Hello1LinkedX64.hello1_placeOKAt) (in2X_hello1 H)
    (SccCertificate.out_eq ▸ hpa) hB

-- `hpa`, by compiled evaluation: exactly `hello1_final`'s hypothesis.
#guard Scc.Cert.Link.X64.parsesTo ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩
  SccCertificate.outLit.prog SccCertificate.outLit.secs

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_finalP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_finalP

/-- info: 'Spike.Lib.LowerX64.hello1_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_final

end Spike.Lib.LowerX64
