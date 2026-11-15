/-
**`hello1`'s AArch64 statement at the text after the granule pass**, at
any layout passing the placement check for both the compiler's output and
the output with the tail: the compiler's text with its end label
`scc_text_end` replaced by a tail `T` (the pass's filler, `.Lgw0`, its
descriptor word and `scc_text_end`), the data sections unchanged.

- `hello1_rest2A`: `hello1`'s open premises `Rest2A` at the compiler's
  output, closed, at any layout passing the placement check (the chain of
  `hello1_finalCA_gen`, stopped before `correct2_of`);
- `hello1_finalCAG_of`: `CorrectE` at the text with the tail
  (`correct2_tail` at `hello1_rest2A`), from the placement check at both
  outputs, the tail's shape, the cells naming neither of the tail's labels
  and the parse of the text.
-/
import Spike.Test.A64Hello1FinalCA
import Spike.Test.A64Hello1FinalO
import Spike.Test.A64Hello1ClosedBVBF
import Spike.Lib.A64Rest2TailEq
import Spike.Lib.LowerA64.Correct1Tail

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64LabelCongr (Directive.Free)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

/-- The labels of the granule pass's tail: the end label it re-places and
the descriptor word's. -/
def tailLabsG : List _root_.Label := ["scc_text_end", ".Lgw0"]

/-- The compiler's output with its end label replaced by the tail `T`. -/
abbrev outG (T : Program) : Scc.Cert.PlaceOK.A64.Out := withTail OA T

/-- The placement check at a layout holds at the theorem's layout `lay2`
(which differs only in the static labels and immediates). -/
theorem placeOKAt_lay2 {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
    {o : Scc.Cert.PlaceOK.A64.Out} (h : placeOKAt pcfg Λ o = true) : placeOKAt pcfg (lay2 Λ p) o = true := h

/-- **`hello1`'s open premises at any layout passing the placement check**:
`Rest2A` at the compiler's output and every admissible entry state
(`rest2A_ofInW` at `in2AW_ofBVBF`; the landings by `hello1_landAWT` at
`hello1_hWBotA`, the setup call by `hello1_hSFA_ofPreH` at
`hello1_hAW_noneA hello1_openAPtA`, `main`'s call by `hello1_hUBVFA`). -/
theorem hello1_rest2A {Λx : Scc.Sem.Layout} {arch : WeakMem.Arch} {E : Entry} (hE : E.Ok (lay2 Λx P1A))
    (h' : placeOKAt SccCertificate.placeCfg (lay2 Λx P1A) OA = true) :
    Rest2A (lay2 Λx P1A) P1A h' arch E :=
  rest2A_ofInW h' hE (in2AW_ofBVBF h' Spike.Lib.LowerNode.hello1o_accepted2 hello1_htyA.choose_spec
    (by decide) hE ⟨ElH h' Spike.Lib.LowerNode.hello1o_accepted2, fun _ => True,
      h1InAW_ofLandT h' (hello1_landAWT h' (hello1_hWBotA h')) hello1_hTnA
        (fun J _ _ _ _ _ _ _ _ _ => hello1_hAbQA h' rfl Spike.Lib.LowerNode.hello1o_accepted2
          hello1_htyA.choose_spec (fun _ _ _ _ _ _ => trivial) J _ _),
      hello1_hSFA_ofPreH h' (openPHA_of_openAHA h' _ hello1_htyA.choose_spec
        (hello1_hAW_noneA hello1_openAPtA E hE h')),
      hello1_hUBVFA h' E _⟩)

/-- **`hello1`'s AArch64 statement at the text with the tail**: `CorrectE`
at a text `asmF` parsing to the compiler's cells with the end label
`scc_text_end` (`hlast`) replaced by `T` and the same data sections
(`hpa`), at any layout `Λx` passing the placement check for the compiler's
output (`h0`) and the output with the tail (`hF`); `T` has no instruction,
its labels among `tailLabsG`, which no cell before it names (`hfree`) and
no abort stub of `Λx` is (`ha`). -/
theorem hello1_finalCAG_of {Λx : Scc.Sem.Layout} {T : Program} {asmF : String}
    (h0 : placeOKAt SccCertificate.placeCfg Λx OA = true)
    (hF : placeOKAt SccCertificate.placeCfg Λx (outG T) = true)
    (hlast : (OA).prog.getLast? = some (.label "scc_text_end"))
    (hT : ∀ d ∈ T, ∀ l, d = .label l → l ∈ tailLabsG) (hTi : ∀ d ∈ T, ∀ i, d ≠ .instr i)
    (hfree : ∀ i, Directive.instr i ∈ (OA).prog.dropLast → Directive.Free tailLabsG (.instr i))
    (ha : ∀ k, Λx.abortLbl k ∉ tailLabsG)
    (hpa : Scc.Cert.Link.A64.parsesTo asmF (outG T).prog (outG T).secs = true)
    {B : Scc.Sem.Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch P1A) P1A) (lay2 Λx P1A) B asmF := by
  have hte : "scc_text_end" ∈ tailLabsG := by decide
  have hs : ∀ k : XferKind, k.label ∉ tailLabsG := by intro k; cases k <;> decide
  have hn : ∀ x ∈ Scc.Cert.Rt.A64.rtNames, x ∉ tailLabsG := by decide
  have hrow : ∀ r ∈ Scc.Cert.Rt.A64.bPR ++ Scc.Cert.Rt.A64.bLR ++ Scc.Cert.Rt.A64.bNR ++ Scc.Cert.Rt.A64.bTR,
      r.l1 ∉ tailLabsG ∧ r.l2 ∉ tailLabsG := by decide
  have hsecs : (outG T).secs = (OA).secs := withTail_secs _ _
  have hPF : (outG T).prog = (OA).prog.dropLast ++ T := withTail_prog _ _
  intro E hE
  obtain ⟨h1, h2⟩ := Scc.Cert.Link.A64.parsed_of_parsesTo hpa
  have hPE : (OA).prog = (OA).prog.dropLast ++ [.label "scc_text_end"] := by
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [hys, List.dropLast_concat]
  have h0' : placeOKAt SccCertificate.placeCfg (lay2 Λx P1A) OA = true := placeOKAt_lay2 h0
  exact correct_of_parsed _ E h1 h2
    (Spike.Lib.A64Rest2Tail.correct2_tail (oE := OA) (oF := outG T) (P := (OA).prog.dropLast) (T := T)
      (te := "scc_text_end") (B := tailLabsG) (hE := h0') Spike.Lib.LowerNode.hello1o_accepted2 hF
      (Spike.Lib.A64.Rt.ctrZ_ofPlaceOK h0) hB hE (hnum2 Spike.Lib.LowerNode.hello1o_accepted2 h0 arch)
      (hd2 Spike.Lib.LowerNode.hello1o_accepted2 h0) (hrd2 Spike.Lib.LowerNode.hello1o_accepted2 h0 arch)
      hsecs hPE hPF hte hT hTi hfree hs ha hn hrow
      (hello1_rest2A hE h0'))

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_rest2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rest2A

/-- info: 'Spike.Lib.LowerA64.hello1_finalCAG_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_finalCAG_of
