import Scc.Cert.GranuleCellsX64
import Scc.Cert.OutStageX64

/-!
# The output after the granule pass, x86-64 (untrusted)

The x86-64 twin of `Scc/Cert/GranuleOutA64.lean`. A certificate of a
program built with the granule pass certifies the **post-pass** output:
`ofFinal sizes labelOffs st final`, which is `ofStage` with the code cells
of the program the loader reads from the pass's output
(`Scc.Cert.Granule.X64.textCells final`) at the assembler's sizes of that
output (`Kraken.Promising.X64.sizedCells`), its label offsets, and the
block table recomputed on those cells (`Data.blocksOf?`). `placeOK` is then
decided on that output, as on any other: nothing about the old layout is
transferred. The sizes and label offsets are the assembler's of the
rendered post-pass text (untrusted, checked by A2 as for any output). The
soundness of `placeOK` holds for any program (`Scc/Cert/PlaceOKX64.lean`:
`placeOK`, `placeOK_of` and the `*_of_placeOKAt` lemmas take the output's
cells as a parameter; the layout lemmas are generic in the program, a data
cell stopping a run of instructions).

`ofFinal_of_stages`: with `Scc.Cert.Granule.X64.check final items` (a kernel
decision on literals), the post-pass output is scc's output
(`Out.ofEmitted (lowerAll cfg p) sizes labelOffs`) with the cells replaced
by those of `textCells final` and the block table recomputed, and that
program `Expands` scc's instruction list (`(lowerAll cfg p).prog`): the
same cells with own cells (fillers, words, word labels) inserted only where
nothing falls into them. The relation is on directives: `sizedCells_fst`
gives back the directives of the cells. Corollaries: no inserted
instruction (`ofFinal_filter_ins`), and segments no own cell may enter stay
contiguous (`ofFinal_seg`).

`final` need not be the pass's output for any of this: the check alone
gives the relation. `granuleX64 ir items = .ok final` is tested, not proved.
-/

namespace Scc.Cert.Granule.X64
open Scc.Cert.PlaceOK.X64
open Scc.Lower.X64 (lowerAll lowerAll? textDirectives)
open Scc.Emit.X64 (Item)
open Scc.Emit.Granule (insX64)
open Kraken.Promising.X64 (sizedCells sizedCells_fst)

/-- The code cells of the post-pass program at the sizes `sizes` (empty
where they do not fit). -/
def cellsOfFinal (sizes : List Nat) (final : List Item) : List (Directive × Nat) :=
  ((textCells final).bind (sizedCells · sizes)).getD []

/-- The block table of the post-pass cells (`ofFinal`'s). -/
def blocksOfFinal (sizes : List Nat) (ir : Scc.IR.Program) (final : List Item) : Option (List Rt.X64.OGrp) :=
  Data.blocksOf? ir (cellsOfFinal sizes final)

/-- **The output after the pass** from a stage, the pass's items `final`, and
the assembler's sizes and label offsets of the rendered `final`. -/
def ofFinal (sizes : List Nat) (labelOffs : List (String × Nat)) : Stage → List Item → Out
  | (ir, _, sps, tbl, need, setup), final =>
    let secs := Scc.Emit.Data.Secs.ofProgram ir.data (if ir.growth.isSome then some sps else none) tbl
    let cells := cellsOfFinal sizes final
    ⟨cells, ⟨secs.data, secs.bss, secs.rodata⟩, labelOffs,
      { blocks := (Data.blocksOf? ir cells).getD []
        need := need.getD []
        tail := if setup then .setup else .bare
        ir := some ir }⟩

/-- **`ofFinal` at the block table `blks`** in place of `blocksOfFinal`'s. -/
def ofFinalB (sizes : List Nat) (labelOffs : List (String × Nat)) :
    Stage → List Item → List Rt.X64.OGrp → Out
  | (ir, _, sps, tbl, need, setup), final, blks =>
    let secs := Scc.Emit.Data.Secs.ofProgram ir.data (if ir.growth.isSome then some sps else none) tbl
    ⟨cellsOfFinal sizes final, ⟨secs.data, secs.bss, secs.rodata⟩, labelOffs,
      { blocks := blks
        need := need.getD []
        tail := if setup then .setup else .bare
        ir := some ir }⟩

/-- **`ofFinal` from its block table**. -/
theorem ofFinal_eq_B {sizes : List Nat} {labelOffs : List (String × Nat)} {st : Stage} {final : List Item}
    {blks : List Rt.X64.OGrp} (h : blocksOfFinal sizes st.1 final = some blks) :
    ofFinal sizes labelOffs st final = ofFinalB sizes labelOffs st final blks := by
  obtain ⟨ir, items, sps, tbl, need, setup⟩ := st
  simp only [blocksOfFinal] at h
  simp only [ofFinal, ofFinalB, h, Option.getD_some]

/-- `ofFinal` is `ofStage` (at the same sizes and offsets) but for the cells
and the block table. -/
theorem ofFinal_eq (sizes : List Nat) (labelOffs : List (String × Nat)) (st : Stage) (final : List Item) :
    ofFinal sizes labelOffs st final =
      { ofStage sizes labelOffs st with
        prog := cellsOfFinal sizes final,
        place := { (ofStage sizes labelOffs st).place with
                   blocks := (blocksOfFinal sizes st.1 final).getD [] } } := by
  obtain ⟨ir, items, sps, tbl, need, setup⟩ := st
  rfl

/-- scc's instruction list is `textDirectives` of the emitter's items. -/
theorem lowerAll_prog {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items tits : List Item} {sps : List (String × List Int × List Int)} {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl)) :
    (lowerAll cfg p).prog = textDirectives items := by
  unfold lowered1 at h1
  split at h1
  · rename_i l hl
    cases h1
    unfold lowerAll lowerAll?
    simp only [hl, bind, Except.bind, Scc.Lower.X64.emitAll, h2, h3, Scc.Lower.X64.tblOf, pure, Except.pure]
  · cases h1

/-- **The post-pass output from its stages**: where the lowering gives `ir`,
the emitter `items` and `sps`, the check holds of `final`, the post-pass
program fits the sizes (`hz`, cells `cs`: no `getD` fallback) and its block
table is `blks` (`hb`), `ofFinal` of them is scc's output with the cells
`cs` and the block table `blks`; `cs` are the cells of the loaded program
`fd`, which `Expands` scc's instruction list. A certificate decides `hz` and
`hb` on literals. -/
theorem ofFinal_of_stages {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    (sizes : List Nat) (labelOffs : List (String × Nat)) {cs : List (Directive × Nat)} {blks : List Rt.X64.OGrp}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : check final items = true) (hz : (textCells final).bind (sizedCells · sizes) = some cs)
    (hb : blocksOfFinal sizes ir final = some blks) :
    let o := Out.ofEmitted (lowerAll cfg p) sizes labelOffs
    let f := ofFinal sizes labelOffs (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) final
    f = { o with prog := cs, place := { o.place with blocks := blks } } ∧
      ∃ i fd, (lowerAll cfg p).prog = some i ∧ textCells final = some fd ∧
        Expands cellsX64 false i fd ∧ f.prog = cs ∧ cs.map (·.1) = fd ∧ f.place.blocks = blks := by
  intro o f
  have ho : o = ofStage sizes labelOffs (ir, items, sps, tbl, (Scc.Lower.stackNeed .x64 ir).toOption, setup) :=
    ofEmitted_of_stages sizes labelOffs h1 h2 h3
  have hl := lowerAll_prog h1 h2 h3
  have hcs : cellsOfFinal sizes final = cs := by simp only [cellsOfFinal, hz, Option.getD_some]
  have hfp : f.prog = cs := hcs
  have hfb : f.place.blocks = blks := by
    show (Data.blocksOf? ir (cellsOfFinal sizes final)).getD [] = blks
    simp only [blocksOfFinal] at hb
    simp only [hb, Option.getD_some]
  obtain ⟨fd, i, hf, hi, he⟩ := expands_of_check hc
  refine ⟨?_, i, fd, hl.trans hi, hf, he, hfp, ?_, hfb⟩
  · have hb' : (blocksOfFinal sizes ir final).getD [] = blks := by rw [hb, Option.getD_some]
    rw [ho, ← hcs, ← hb']
    exact ofFinal_eq _ _ _ _
  · rw [hf, Option.bind_some] at hz
    exact sizedCells_fst hz

/-- **No inserted instruction**: the instruction cells of the post-pass
program are scc's, in order. -/
theorem ofFinal_filter_ins {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : check final items = true) :
    ∃ i fd, (lowerAll cfg p).prog = some i ∧ textCells final = some fd ∧
      fd.filter (fun c => (insX64 c).isSome) = i.filter (fun c => (insX64 c).isSome) := by
  obtain ⟨fd, i, hf, hi, he⟩ := expands_of_check hc
  exact ⟨i, fd, (lowerAll_prog h1 h2 h3).trans hi, hf, he.filter_ins⟩

/-- **Blocks stay contiguous**: a segment of scc's instruction list that no
own cell may enter is a contiguous segment of the post-pass program. -/
theorem ofFinal_seg {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Item} {sps : List (String × List Int × List Int)}
    {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.X64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : check final items = true) {a s b : List Directive}
    (he : (lowerAll cfg p).prog = some (a ++ s ++ b))
    (hn : noBreak cellsX64 (cellsX64.scan false a) s = true) :
    ∃ fd a' b', textCells final = some fd ∧ fd = a' ++ s ++ b' := by
  obtain ⟨fd, i, hf, hi, hx⟩ := expands_of_check hc
  rw [lowerAll_prog h1 h2 h3, hi] at he
  cases he
  obtain ⟨a', b', h⟩ := hx.seg a s b rfl hn
  exact ⟨fd, a', b', hf, h⟩

/-! ## Tests -/

namespace TestOut
open Scc.Emit.X64 Scc.Emit.Granule
open Scc.Cert.Granule.TestX64 (progs)

-- The post-pass program has a block table at the unit sizes (`unitTable`; the
-- assembler's sizes come from the certificate) at both granule sizes.
#guard (progs.take 3).all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  [granule, 1024].all fun gs => Id.run do
    let some final := (granuleWith isaX64 gs (pointsX64 p) items).toOption | return false
    let some fd := textCells final | return false
    return check final items && (blocksOfFinal (Kraken.Promising.X64.unitTable fd) p final).isSome &&
      !(cellsOfFinal (Kraken.Promising.X64.unitTable fd) final).isEmpty

end TestOut

end Scc.Cert.Granule.X64
