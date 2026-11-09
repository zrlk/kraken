import Scc.Cert.MapsCheckA64
import Scc.Cert.MapsSer

/-!
# The GC tables' stage of the AArch64 emitter (untrusted)

The AArch64 twin of `Scc.Cert.MapsEmitX64`. Once a program is emitted
(`Scc.Emit.A64.emitItemsMaps`), `emitTables` gives the GC tables as data: the tables of the text
(`computeA64`) serialised by `Scc.Cert.Maps.tableItems`, every key the label the text has there
(`labelAt`). It returns the items to append to the text (a `.section .rodata` line, then the same
data as directives, after `scc_stackmap`'s) and the data itself, which
`Scc.Emit.Data.Secs.ofProgram` takes as `tbl`: one list for the rendered text and the sections
the certificate expects.

A key without a label of its own, or a tail name the text does not define, is refused (the
serialiser's refusal; every key has its own label, which P5's ret and fall-through labels give).
A program without growable stacks (`IR.Program.growth = none`) is refused: its calls have no
`scc_stackmap` entries to take the call maps from (the emitter records safe points only with
growth). Every lowered program has growth (`Scc.Lower.lowerWithMarks`), so no program scc
emits is refused; the refusal keeps a growth-less program from silently getting no tables
(and no `scc_gc_desc` for the granules to name).

It is a stage of its own, after `emitItemsMaps` (not inside it): the kernel checks of the
emitter's stages do not evaluate the tables.
-/

namespace Scc.Cert.MapsA64
open Maps

/-- A data item as a line of the AArch64 text (`Scc.Sem.dataLine` reads it back as the item).
One item per line, so a difference word is the sole operand of its `.quad` line (never
`.quad a - ., b - .`). -/
def dataItem : DItem → Scc.Emit.A64.Item
  | .label l => .d (.label l)
  | .bytes bs => .raw (".byte " ++ ", ".intercalate (bs.map fun b => toString b.toNat))
  | .zero n => .raw s!".zero {n}"
  | .quad v => .raw s!".quad {v}"
  | .quadLabel l => .raw s!".quad {l}"
  | .align n => .raw s!".balign {n}"
  | .quadDiff a b => .raw s!".quad {a} - {b.getD "."}"

/-- **The tables' stage with key labels `labelOf items`** (the text's, `labelAt`, looked up
through the label map built once, `labelIn (labelMap items)`, in `emitTables`; a test passes
stand-ins): the items to append to the text and the tables' data.
The descriptor names the labels `d` (by default the emitter's; the stage is host-blind, a host
with other labels passes its own). -/
def emitTablesWith (labelOf : List Item → Nat → Option String) (p : IR.Program)
    (its : List Scc.Emit.A64.Item) (d : DescLabels := {}) :
    Except String (List Scc.Emit.A64.Item × List DItem) := do
  if p.growth.isNone then throw "gc tables: no Program.growth (no scc_stackmap to take call maps from)"
  let items ← itemsOf its
  let t ← computeA64 p its
  let tbl ← tableItems t (labelOf items) d (fun g => (labelAddr items g).isSome)
  pure (.raw ".section .rodata" :: tbl.map dataItem, tbl)

/-- **The GC tables' stage** (see the module docstring), the descriptor naming `d`. -/
def emitTables (p : IR.Program) (its : List Scc.Emit.A64.Item) (d : DescLabels := {}) :
    Except String (List Scc.Emit.A64.Item × List DItem) :=
  emitTablesWith (fun items => labelIn (labelMap items)) p its d

/-! ## The stage with a ranked liveness witness

The certificates cannot afford `liveSlots`' fixpoint iteration on the runtime's large routines.
`emitTablesW` takes a **ranked witness** per IR function instead (`GcWit`, which scc computes
from the IR and the text, `gcWitness`): it refuses unless every witness is the least fixpoint
on its function's body (`leastOk`, `computeWR`), then builds the tables from the witnesses
(`computeW`) and serialises them as `emitTables` does. With scc's witnesses it gives
`emitTables`' result. -/

/-- **The ranked witness scc passes to `emitTablesW`**: per IR function, its reference liveness
and ranks (`witnessR`), from the IR `p` and the emitted items `its` alone. -/
def gcWitness (p : IR.Program) (its : List Scc.Emit.A64.Item) : Except String GcWit := do
  let (items, fns) ← fnTagsA64 p its
  pure (witnessR fns items)

/-- **The tables' stage from a ranked witness** `gw` (see above), the descriptor naming `d`:
as `emitTables`, the tables `computeWR`'s. An error if `gw` has not one entry per IR function or
an entry is not its function's least fixpoint with ranks below the fuel. -/
def emitTablesW (p : IR.Program) (its : List Scc.Emit.A64.Item) (gw : GcWit)
    (d : DescLabels := {}) : Except String (List Scc.Emit.A64.Item × List DItem) := do
  if p.growth.isNone then throw "gc tables: no Program.growth (no scc_stackmap to take call maps from)"
  let (items, fns) ← fnTagsA64 p its
  let t ← computeWR fns items gw
  let tbl ← tableItems t (labelIn (labelMap items)) d (fun g => (labelAddr items g).isSome)
  pure (.raw ".section .rodata" :: tbl.map dataItem, tbl)

/-! ### `emitTablesW` in stages

A certificate checks `emitTablesW` in pieces, each its own kernel check on literals: the items,
the `scc_stackmap` table and the tags (`fnTagsA64_of_stages`), the tables from the witness
(`Scc.Cert.Maps.computeWR_of_least`, `computeW_of_stages`), the label map and the serialiser
(`emitTablesW_of_stages`). -/

/-- **`fnTagsA64` from its stages.** -/
theorem fnTagsA64_of_stages {p : IR.Program} {its : List Scc.Emit.A64.Item} {items : List Item}
    {fns : List FnTags} {stbl : List (Nat × List Int × List Int)} {areas : List (IR.Sym × Nat)}
    (ha : Scc.Emit.A64.emitPre p = .ok areas)
    (hi : itemsOf its = .ok items)
    (ht : stackTable its items = .ok stbl)
    (hf : p.funcs.zipIdx.mapM (tagsOf p areas items stbl) = .ok fns) :
    fnTagsA64 p its = .ok (items, fns) := by
  simp only [fnTagsA64, ha, hi, ht, hf, bind, Except.bind, pure, Except.pure]

/-- **`emitTablesW` from its stages**: growth, the items and tags, the tables from the witness,
the label map `labs` and the serialiser on it. -/
theorem emitTablesW_of_stages {p : IR.Program} {its : List Scc.Emit.A64.Item} {gw : GcWit}
    {d : DescLabels} {items : List Item} {fns : List FnTags} {t : Tables}
    {labs : List (Nat × String)} {tbl : List DItem}
    (hg : p.growth.isSome = true) (hf : fnTagsA64 p its = .ok (items, fns))
    (hc : computeWR fns items gw = .ok t) (hl : labelMap items = labs)
    (hs : tableItems t (labelIn labs) d (fun g => (labelAddr items g).isSome) = .ok tbl) :
    emitTablesW p its gw d = .ok (.raw ".section .rodata" :: tbl.map dataItem, tbl) := by
  have hn : p.growth.isNone = false := by
    cases h : p.growth with
    | none => rw [h] at hg; cases hg
    | some _ => rfl
  subst hl
  simp only [emitTablesW, hn, hf, hc, hs, bind, Except.bind, pure, Except.pure]
  rfl

end Scc.Cert.MapsA64
