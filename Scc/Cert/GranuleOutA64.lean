import Scc.Cert.GranuleCellsA64
import Scc.Cert.OutStageA64

/-!
# The output after the granule pass, AArch64 (untrusted)

A certificate of a program built with the granule pass certifies the
**post-pass** output: `ofFinal`, which is `ofStage` with the instruction list
the loader reads from the pass's output (`Scc.Cert.Granule.A64.textCells
final`) and the block table recomputed on it (`Data.blocksOf?`). `placeOK`
is then decided on that output, as on any other: nothing about the old
layout is transferred. The soundness of `placeOK` holds for any program:

* `Scc/Cert/PlaceOKA64.lean`: `placeOK`, `placeOKAt`, `placeOK_of` and the
  `*_of_placeOKAt` lemmas (`fnCode_of_placeOKAt`, `rtInit_of_placeOKAt`,
  …) take the output's program as a parameter;
* `Scc/Cert/Rt/LayoutA64.lean`: `isIns`, `run` (the instructions after a
  label up to the first non-instruction cell: a filler or the word stops it),
  `blockAt`, `labelGap` (only instructions between two labels) and the
  theorems `codeAt_blockAt` and `label_labelGap` are generic in the program.

So a filler or a word inside a block, or between two labels a check relates,
makes a `placeOK` component fail: it is never read as code.

What ties the post-pass output to the emitter is `ofFinal_of_stages`: with
`Scc.Cert.Granule.A64.check final items` (a kernel decision on literals),
the post-pass output is scc's output (`Out.ofEmitted (lowerAll cfg p)`) with
the program replaced by `textCells final` and the block table recomputed,
and that program `Expands` scc's (`Scc.Cert.Granule.Expands`): the same
cells with own cells (fillers, words, word labels) inserted only where
nothing falls into them. Corollaries: no inserted instruction
(`ofFinal_filter_ins`), and every segment of scc's program no own cell may
enter is a contiguous segment of the post-pass one (`ofFinal_seg`).

`final` need not be the pass's output for any of this: the check alone
gives the relation. `granuleA64 ir items = .ok final` is tested, not proved.
-/

namespace Scc.Cert.Granule.A64
open Scc.Cert.PlaceOK.A64
open Scc.Lower.A64 (lowerAll textDirectives)
open Scc.Emit.A64 (Item Safepoint)
open Scc.Emit.Granule (insA64)

/-- **The output after the pass** from a stage and the pass's items `final`:
`ofStage`'s fields, with the program `textCells final` and its block
table. -/
def ofFinal : Stage → List Item → Out
  | (ir, _, sps, tbl, need, setup), final =>
    let secs := Scc.Emit.Data.Secs.ofProgram ir.data (if ir.growth.isSome then some sps else none) tbl
    ⟨textCells final, ⟨secs.data, secs.bss, secs.rodata⟩, [],
      { blocks := (Data.blocksOf? ir (textCells final)).getD []
        need := need.getD []
        tail := if setup then .setup else .bare
        ir := some ir }⟩

/-- The block table of the post-pass program (`ofFinal`'s). -/
def blocksOfFinal (ir : Scc.IR.Program) (final : List Item) : Option (List Rt.A64.OGrp) :=
  Data.blocksOf? ir (textCells final)

/-- **`ofFinal` at the block table `blks`** in place of `blocksOfFinal`'s. -/
def ofFinalB : Stage → List Item → List Rt.A64.OGrp → Out
  | (ir, _, sps, tbl, need, setup), final, blks =>
    let secs := Scc.Emit.Data.Secs.ofProgram ir.data (if ir.growth.isSome then some sps else none) tbl
    ⟨textCells final, ⟨secs.data, secs.bss, secs.rodata⟩, [],
      { blocks := blks
        need := need.getD []
        tail := if setup then .setup else .bare
        ir := some ir }⟩

/-- **`ofFinal` from its block table**: where the post-pass block table is
`blks`, `ofFinal` is `ofFinalB` at `blks`. -/
theorem ofFinal_eq_B {st : Stage} {final : List Item} {blks : List Rt.A64.OGrp}
    (h : blocksOfFinal st.1 final = some blks) : ofFinal st final = ofFinalB st final blks := by
  obtain ⟨ir, items, sps, tbl, need, setup⟩ := st
  simp only [blocksOfFinal] at h
  simp only [ofFinal, ofFinalB, h, Option.getD_some]

/-- `ofFinal` is `ofStage` but for the program and the block table. -/
theorem ofFinal_eq (st : Stage) (final : List Item) :
    ofFinal st final =
      { ofStage st with prog := textCells final,
                        place := { (ofStage st).place with blocks := (blocksOfFinal st.1 final).getD [] } } := by
  obtain ⟨ir, items, sps, tbl, need, setup⟩ := st
  rfl

/-- scc's instruction list is `textDirectives` of the emitter's items. -/
theorem lowerAll_prog {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items tits : List Item} {sps : List Safepoint} {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl)) :
    (Out.ofEmitted (lowerAll cfg p)).prog = textDirectives items := by
  rw [ofEmitted_of_stages h1 h2 h3]; rfl

/-- **The post-pass output from its stages**: where the lowering gives `ir`,
the emitter `items` and `sps`, the check holds of `final` and the post-pass
block table is `blks` (`hb`: no `getD` fallback; a certificate decides it on
literals), the output `ofFinal` of them is scc's output
(`Out.ofEmitted (lowerAll cfg p)`) with the program `textCells final`
(which `Expands` scc's) and the block table `blks`. -/
theorem ofFinal_of_stages {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Item} {sps : List Safepoint} {tbl : List Kraken.DataImage.Item}
    {blks : List Rt.A64.OGrp}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : check final items = true) (hb : blocksOfFinal ir final = some blks) :
    let o := Out.ofEmitted (lowerAll cfg p)
    let f := ofFinal (ir, items, sps, tbl, (Scc.Lower.stackNeed .arm ir).toOption, setup) final
    f = { o with prog := textCells final, place := { o.place with blocks := blks } } ∧
      f.prog = textCells final ∧ o.prog = textDirectives items ∧ f.place.blocks = blks ∧
      Expands cellsA64 false o.prog f.prog := by
  intro o f
  have ho : o = ofStage (ir, items, sps, tbl, (Scc.Lower.stackNeed .arm ir).toOption, setup) :=
    ofEmitted_of_stages h1 h2 h3
  have hp : o.prog = textDirectives items := lowerAll_prog h1 h2 h3
  have hb' : (blocksOfFinal ir final).getD [] = blks := by rw [hb, Option.getD_some]
  have hfb : f.place.blocks = blks := hb'
  refine ⟨by rw [ho, ← hb']; exact ofFinal_eq _ _, rfl, hp, hfb, ?_⟩
  rw [hp]
  exact expands_of_check' hc

/-- **No inserted instruction**: the instruction cells of the post-pass
program are scc's, in order. -/
theorem ofFinal_filter_ins {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Item} {sps : List Safepoint} {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl)) (hc : check final items = true) :
    (textCells final).filter (fun c => (insA64 c).isSome) =
      (Out.ofEmitted (lowerAll cfg p)).prog.filter (fun c => (insA64 c).isSome) := by
  rw [lowerAll_prog h1 h2 h3]
  exact (expands_of_check' hc).filter_ins

/-- **Blocks stay contiguous**: a segment of scc's program that no own cell
may enter (`noBreak` from the flow state before it) is a contiguous segment
of the post-pass program. -/
theorem ofFinal_seg {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items final tits : List Item} {sps : List Safepoint} {tbl : List Kraken.DataImage.Item}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps))
    (h3 : Scc.Lower.A64.tablesOf ir items cfg.gcWit = .ok (tits, tbl))
    (hc : check final items = true) {a s b : List Directive}
    (he : (Out.ofEmitted (lowerAll cfg p)).prog = a ++ s ++ b)
    (hn : noBreak cellsA64 (cellsA64.scan false a) s = true) :
    ∃ a' b', textCells final = a' ++ s ++ b' := by
  rw [lowerAll_prog h1 h2 h3] at he
  exact (expands_of_check' hc).seg a s b he hn

/-! ## Tests -/

namespace TestOut
open Scc.Emit.A64 Scc.Emit.Granule
open Scc.Cert.Granule.A64.Test (progs)

/-- `final` with `x` inserted after every unconditional `b` (between blocks,
where nothing falls). -/
def afterJmps (x : Item) (final : List Item) : List Item :=
  final.flatMap fun y => match y with
    | .d (.instr ⟨.W64, .B (.label _)⟩) => [y, x]
    | _ => [y]

-- `ofFinal`'s block table and `blocksOfFinal` agree, and the post-pass program
-- has a block table at both granule sizes.
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  [granule, 1024].all fun gs => Id.run do
    let some final := (granuleWith isaA64 gs (pointsA64 p) items).toOption | return false
    return check final items && (blocksOfFinal p final).isSome
-- Negative: an instruction (`nop`) inserted between blocks, after a `b`, next to
-- the pass's filler: it is not an own cell, so the erased cells are not the
-- emitter's: the check fails.
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleWith isaA64 1024 (pointsA64 p) items).toOption | return false
  let final' := afterJmps (ins (w := .W64) .NOP) final
  return final'.length > final.length && !check final' items
-- Positive: a word label inserted after a `b` is an own cell where nothing falls:
-- the check holds (own cells may be inserted there), and it adds no instruction.
#guard progs.all fun p => Id.run do
  let some p := p | return false
  let some items := (emitItems p).toOption | return false
  let some final := (granuleWith isaA64 1024 (pointsA64 p) items).toOption | return false
  let final' := afterJmps (.d (.label (wordLabel 999))) final
  return final'.length > final.length && check final' items

end TestOut

end Scc.Cert.Granule.A64
