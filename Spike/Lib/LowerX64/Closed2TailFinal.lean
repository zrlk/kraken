/-
**The x86-64 compiler theorem at a post-pass text** (`closed2Stmt_x64_final`'s
`CorrectE`, at the text of an output whose cells are the compiler's output's
cells without the end label, then an instruction-free tail): `correctE_tail`
(`Spike/Lib/X64Correct2Tail.lean`) at `rest2X_x64_final`. Both placement
checks (`hE` at the compiler's output, `hF` at the post-pass output) are
premises.

- `x64_correctE_tail_final`: at any post-pass output `oF` of that shape;
- `x64_scc_correctE_text_closedAt2_final`: at the granule pass's output
  `ofFinal sizes labelOffs st final` from the stages a certificate decides
  (as `x64_scc_correctE_text_closedAt_final`, `Spike/Lib/LowerX64/CorrectFinal.lean`),
  the data sections and the cells from `ofFinal_of_stages`.
-/
import Spike.Lib.LowerX64.Rest2Final
import Spike.Lib.X64Correct2Tail
import Scc.Cert.GranuleOutX64

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm
open Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Rt.X64 (rtNames bPR bLR bNR bTR)
open Spike.Lib.X64LabelCongr (Directive.Free)

/-- **`CorrectE` at a post-pass text** for an `Accepted2` program at a
configuration with the header bound: the compiler's output's cells `P`
closed by the end label `te`, the post-pass output `oF` with the same data
sections and cells `P ++ T` (`T` instruction-free, its labels and `te` in
`B`, `P`'s instructions naming none of `B`, the labels the marks, the
runtime's words and the phase table read off `B`), both passing the
placement check, at a text parsing to `oF`. -/
theorem x64_correctE_tail_final (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22)
    {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {Λ : Scc.Sem.Layout} (hp : Scc.Lower.Accepted2 p = true) (hR : Scc.Lower.mainRetOk p = true)
    (hE : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (hcfg : CfgNeedOk pcfg = true)
    {oF : Scc.Cert.PlaceOK.X64.Out} {P T : List (Directive × Nat)} {te : String} {B : List String}
    (hF : placeOKAt pcfg Λ oF = true)
    (hsecs : oF.secs = (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs)
    (hPE : (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog = P ++ [(.label te, 0)])
    (hPF : oF.prog = P ++ T)
    (hte : te ∈ B) (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ B) (hTi : ∀ dz ∈ T, ∀ i, dz.1 ≠ .instr i)
    (hfree : ∀ i z, (Directive.instr i, z) ∈ P → Directive.Free B (.instr i))
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) (hn : ∀ x ∈ rtNames, x ∉ B)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    {textF : String} {sizesF : List Nat}
    (hpaF : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesF, oF.labelOffs⟩ oF.prog oF.secs = true)
    {Bu : Budget} (hB : Bu.cells = allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (SrcSem.source (SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } Bu ⟨textF, sizesF, oF.labelOffs⟩ :=
  Spike.Lib.X64Correct2Tail.correctE_tail hp hE hF hsecs hPE hPF hte hT hTi hfree hs ha hn hrow hpaF hB
    fun E hEo => rest2X_x64_final cfg hobj pcfg p sizes labelOffs Λ hp hR hE hcfg arch E hEo hE

open Kraken.Promising.X64 (sizedCells) in
/-- **The x86-64 compiler theorem for an `Accepted2` program after the
granule pass** (the stages a certificate decides: `h1`–`h3`, the pass check
`hc`, the post-pass cells `cs` at the assembler's `sizes`, `hz`, and block
table `hb`): `x64_correctE_tail_final` at `ofFinal sizes labelOffs st final`,
its data sections scc's and its cells `cs` (`ofFinal_of_stages`), the
compiler's output at the pre-pass `sizesE`, `labelOffsE` passing the
placement check (`hE`), its cells `P` closed by the end label. -/
theorem x64_scc_correctE_text_closedAt2_final (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22)
    {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog} {sizesE : List Nat} {labelOffsE : List (String × Nat)}
    {sizes : List Nat} {labelOffs : List (String × Nat)} {Λ : Scc.Sem.Layout}
    (hp : Scc.Lower.Accepted2 p = true) (hR : Scc.Lower.mainRetOk p = true)
    (hE : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizesE labelOffsE) = true)
    (hcfg : CfgNeedOk pcfg = true)
    {ir : Scc.IR.Program} {setup : Bool} {items final tits : List Scc.Emit.X64.Item}
    {sps : List (String × List Int × List Int)} {tbl : List Kraken.DataImage.Item}
    {cs : List (Directive × Nat)} {blks : List Scc.Cert.Rt.X64.OGrp}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : Scc.Cert.Granule.X64.check final items = true)
    (hz : (Scc.Cert.Granule.X64.textCells final).bind (sizedCells · sizes) = some cs)
    (hb : Scc.Cert.Granule.X64.blocksOfFinal sizes ir final = some blks)
    (hF : placeOKAt pcfg Λ (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
      (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final) = true)
    {P T : List (Directive × Nat)} {te : String} {B : List String}
    (hPE : (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizesE labelOffsE).prog = P ++ [(.label te, 0)])
    (hPF : cs = P ++ T)
    (hte : te ∈ B) (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ B) (hTi : ∀ dz ∈ T, ∀ i, dz.1 ≠ .instr i)
    (hfree : ∀ i z, (Directive.instr i, z) ∈ P → Directive.Free B (.instr i))
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) (hn : ∀ x ∈ rtNames, x ∉ B)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    {text : String}
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩
      (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
        (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final).prog
      (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
        (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final).secs = true)
    {Bu : Budget} (hB : Bu.cells = allocCells) {arch : WeakMem.Arch} :
    CorrectE 1 (SrcSem.source (SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } Bu ⟨text, sizes, labelOffs⟩ := by
  obtain ⟨hf, -, -, -, -, -, hfp, -, -⟩ :=
    Scc.Cert.Granule.X64.ofFinal_of_stages sizes labelOffs h1 h2 h3 hc hz hb
  have hsecs : (Scc.Cert.Granule.X64.ofFinal sizes labelOffs
      (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final).secs =
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizesE labelOffsE).secs := by
    rw [hf]; rfl
  exact x64_correctE_tail_final cfg hobj hp hR hE hcfg hF hsecs hPE (hfp.trans hPF) hte hT hTi hfree hs ha hn
    hrow hpa hB

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.x64_correctE_tail_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.x64_correctE_tail_final

/-- info: 'Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt2_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt2_final
