/-
**`Correct` on a post-pass output from the pre-pass premises** (x86-64):
the compiler's output `OX` for an `Accepted2` program, its cells `P`
closed by the end label `te`, and an output `oF` with the same data
sections whose cells are `P` followed by an instruction-free tail `T`
(the granule pass's), both passing `placeOKAt` at the same layout: the open
premises `Rest2X` at `OX` give `Correct` at `oF` (`correct2_of` at `oF`,
`Rest2X` moved by `rest2X_tail_text`; the counter's zero word, the printed
cells, the extern's loop and the reads from `OX`).

- `correct2_tail`: `Correct` on the parsed post-pass output;
- `correctE_tail`: `CorrectE` at a text parsing to it.
-/
import Spike.Lib.X64Rest2TailEq
import Spike.Lib.Rt.X64CtrZOfEmitted

namespace Spike.Lib.X64Correct2Tail

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Rt.X64 (rtNames bPR bLR bNR bTR)
open Spike.Lib.LowerX64 (Rest2X lay2 asm2 correct2_of hnum2 hd2 hrd2)
open Spike.Lib.X64LabelCongr (Directive.Free)

/-- **`Correct` at the post-pass output `oF` from `Rest2X` at the
compiler's output**, along the tail (`rest2X_tail_text`'s premises). -/
theorem correct2_tail {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
    {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout} {oF : Scc.Cert.PlaceOK.X64.Out}
    {P T : List (Directive × Nat)} {te : String} {B : List String} (hp : Scc.Lower.Accepted2 p = true)
    (hE : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hF : placeOKAt pcfg Λ oF = true)
    (hsecs : oF.secs = (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs)
    (hPE : (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog = P ++ [(.label te, 0)])
    (hPF : oF.prog = P ++ T)
    (hte : te ∈ B) (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ B) (hTi : ∀ dz ∈ T, ∀ i, dz.1 ≠ .instr i)
    (hfree : ∀ i z, (Directive.instr i, z) ∈ P → Directive.Free B (.instr i))
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) (hn : ∀ x ∈ rtNames, x ∉ B)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    {Bu : Budget} (hB : Bu.cells = allocCells) {arch : WeakMem.Arch} {E : Entry} (hEo : E.Ok (lay2 Λ p))
    (R : Rest2X (lay2 Λ p) p hE arch E) :
    Correct (Spike.Lib.X64Consumer.TParE E) (SrcSem.source (SrcSem.srcP1o arch p) p) (lay2 Λ p) Bu (asm2 oF) :=
  correct2_of hp hF (by unfold Spike.Lib.X64.Rt.CtrZ; rw [hsecs]; exact Spike.Lib.X64.Rt.ctrZ_ofPlaceOK hE)
    hB hEo (hnum2 hp hE arch) (hd2 hp hE) (hrd2 hp hE arch)
    (Spike.Lib.X64Rest2TailEq.rest2X_tail_text (Λ := lay2 Λ p) (hE := hE) (hF := hF) hsecs hPE hPF hte hT hTi hfree hs ha hn hrow R)

open Scc.Cert.Link.X64 in
/-- **`CorrectE` at a post-pass text from `Rest2X` at the compiler's
output**: `correct2_tail` at every admissible entry state, on the text
`textF` that parses to the post-pass output's cells and data sections
(`hpaF`) at its label offsets. -/
theorem correctE_tail {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat}
    {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout} {oF : Scc.Cert.PlaceOK.X64.Out}
    {P T : List (Directive × Nat)} {te : String} {B : List String} (hp : Scc.Lower.Accepted2 p = true)
    (hE : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hF : placeOKAt pcfg Λ oF = true)
    (hsecs : oF.secs = (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs)
    (hPE : (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog = P ++ [(.label te, 0)])
    (hPF : oF.prog = P ++ T)
    (hte : te ∈ B) (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ B) (hTi : ∀ dz ∈ T, ∀ i, dz.1 ≠ .instr i)
    (hfree : ∀ i z, (Directive.instr i, z) ∈ P → Directive.Free B (.instr i))
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) (hn : ∀ x ∈ rtNames, x ∉ B)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    {textF : String} {sizesF : List Nat} (hpaF : parsesTo ⟨textF, sizesF, oF.labelOffs⟩ oF.prog oF.secs = true)
    {Bu : Budget} (hB : Bu.cells = allocCells) {arch : WeakMem.Arch}
    (R : ∀ E : Entry, E.Ok (lay2 Λ p) → Rest2X (lay2 Λ p) p hE arch E) :
    CorrectE 1 (SrcSem.source (SrcSem.srcP1o arch p) p) (lay2 Λ p) Bu ⟨textF, sizesF, oF.labelOffs⟩ := by
  intro E hEo
  obtain ⟨h1, h2⟩ := parsed_of_parsesTo hpaF
  exact correct_of_parsed _ E h1 h2 (correct2_tail hp hE hF hsecs hPE hPF hte hT hTi hfree hs ha hn hrow hB hEo
    (R E hEo))

end Spike.Lib.X64Correct2Tail

/-- info: 'Spike.Lib.X64Correct2Tail.correct2_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Correct2Tail.correct2_tail

/-- info: 'Spike.Lib.X64Correct2Tail.correctE_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Correct2Tail.correctE_tail
