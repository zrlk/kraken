/-
**An x86-64 program's output after the granule pass, as functions of its certificate's
stages** (untrusted, no new literal in a trusted file): scc's own pass on the emitted items
(`granuleX64`), its text (`render`, as `Scc.Lower.X64.Emitted.listing` with `--granule`), its
sizes and label offsets by scc's own layout (`Scc.Emit.Granule.layout`, `labelOffs`), its cells
and block table, and the stage `ofFinal` reads (`Scc/Cert/GranuleOutX64.lean`).

A test module evaluates these on one certificate's literals (`scc_lit%`) and proves the stage
facts the post-pass compiler theorems take by `kernel_rfl` on the literals.
-/
import Scc.Emit.PostX64
import Scc.Cert.GranuleOutX64

namespace Spike.Lib.X64GranuleOut

open Scc.Cert.PlaceOK.X64
open Scc.Emit.Granule (granuleX64 isaX64 layout textPart)

/-- The pass's items on the items `items` emitted for `ir` (empty if the pass fails). -/
def postItems (ir : Scc.IR.Program) (items : List Scc.Emit.X64.Item) : List Scc.Emit.X64.Item :=
  (granuleX64 ir items).toOption.getD []

/-- The sizes of the text's items, by scc's layout. -/
def itemSizes (its : List Scc.Emit.X64.Item) : List Nat := (layout isaX64 its).toOption.getD []

/-- The sizes of the non-label cells (the loader's `sizes`): the items' sizes off the labels. -/
def cellSizes (its : List Scc.Emit.X64.Item) (zs : List Nat) : List Nat :=
  ((textPart isaX64 its).zip zs).filterMap fun (i, z) =>
    match i with | .d (.label _) => none | .d _ => some z | _ => if z == 0 then none else some z

/-- The post-pass sizes. -/
def postSizes (final : List Scc.Emit.X64.Item) : List Nat := cellSizes final (itemSizes final)

/-- The post-pass label offsets. -/
def postOffs (final : List Scc.Emit.X64.Item) : List (String × Nat) :=
  Scc.Emit.Granule.labelOffs isaX64 0 (textPart isaX64 final) (itemSizes final)

/-- The post-pass text (`Emitted.listing` with `--granule`: the pass's items, then the tables'). -/
def postText (final tits : List Scc.Emit.X64.Item) : String :=
  (Scc.Emit.X64.render (final ++ tits)).toOption.getD ""

/-- The post-pass cells at the sizes `sizes`. -/
def postCells (final : List Scc.Emit.X64.Item) (sizes : List Nat) : List (Directive × Nat) :=
  ((Scc.Cert.Granule.X64.textCells final).bind (Kraken.Promising.X64.sizedCells · sizes)).getD []

/-- The post-pass block table. -/
def postBlocks (sizes : List Nat) (ir : Scc.IR.Program) (final : List Scc.Emit.X64.Item) :
    List Scc.Cert.Rt.X64.OGrp :=
  (Scc.Cert.Granule.X64.blocksOfFinal sizes ir final).getD []

/-- The stage `ofFinal` reads, from the certificate's lowered, emitted and table literals. -/
def stageOf (lw : Scc.IR.Program × Bool)
    (em : List Scc.Emit.X64.Item × List (String × List Int × List Int))
    (tbl : List Kraken.DataImage.Item) : Stage :=
  (lw.1, em.1, em.2, tbl, (Scc.Lower.stackNeed .x64 lw.1).toOption, lw.2)

end Spike.Lib.X64GranuleOut
