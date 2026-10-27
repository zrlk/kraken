import Scc.Cert.OutLitX64
import Scc.Cert.LowerStage
import Scc.Cert.A12StageX64

/-!
# `out = outLit` in three kernel steps (x86-64, `scc --cert`)

The x86-64 twin of `Scc/Cert/OutStageA64.lean`. `ofStage` computes the
output (`Out.ofEmitted e sizes labelOffs`) from what it is made of: the
lowered IR, the emitter's items and safepoints, the stack need table, the
shape of `scc_rt_main`'s tail, and the assembler's sizes and label offsets.
`ofEmitted_of_stages` proves `Out.ofEmitted (lowerAll cfg p) sizes labelOffs
= ofStage …` from two equations, each a kernel check of one stage on
literals:

* `lowered1 cfg p = some (ir, setup)`: the lowering (`lowerIR`) gives the
  IR `ir`;
* `emitItemsMaps ir = .ok (items, sps)`: the emitter, run on the literal
  `ir` (itself checked in stages, `Scc.Emit.X64.emitItemsMaps_of_stages`:
  the emitter's checks, each function, and the rest).

A certificate states `ir`, `items` and `sps` as literals (`scc_lit%`,
untrusted), checks the two equations, and then `ofStage … = outLit` (the
stack need table, the `.text` filter, the sized cells and the offsets
fixpoint, on literals): three declarations, each with a part of the work.
-/

deriving instance Lean.ToExpr for Scc.Emit.X64.Item
deriving instance Lean.ToExpr for Scc.Cert.Rt.X64.PhTab
deriving instance Lean.ToExpr for Scc.Cert.PlaceOK.X64.A12Tabs
-- the functions of the block table's stage per function (below)
deriving instance Lean.ToExpr for Scc.Cert.PlaceOK.X64.Data.K
deriving instance Lean.ToExpr for Scc.Cert.PlaceOK.X64.Data.It

namespace Scc.Cert.PlaceOK.X64

open Scc.Lower.X64 (Emitted lowerAll lowerAll? emitAll textDirectives)
open Scc.Emit.X64 (Item)
open Kraken Kraken.Promising Kraken.Promising.X64

/-- What the output is computed from: the IR, the items, the safepoints,
the stack need table, whether `scc_rt_main` has a setup block. -/
abbrev Stage :=
  Scc.IR.Program × List Item × List (String × List Int × List Int) × Option (List (Scc.IR.Sym × Nat × Nat)) × Bool

/-- **The lowering's part of the output** (`none`: the lowering fails): the
IR and whether `scc_rt_main` has a setup block. -/
def lowered1 (cfg : Scc.Config) (p : CoreTerm.Prog) : Option (Scc.IR.Program × Bool) :=
  match Scc.Lower.lowerIR cfg p with
  | .ok l => some (l.ir, l.checked.entry.arg == .setupTid)
  | .error _ => none


/-- **`lowered1` from its two stages** (`Scc/Cert/LowerStage.lean`): the
depth limit `fr` of the budget and the lowering, each a kernel check of one
lowering. -/
theorem lowered1_of_stages {cfg : Scc.Config} {p : CoreTerm.Prog} {fr : Nat} {r : Scc.IR.Program × Bool}
    (h1 : Scc.Cert.LowerStage.frames1 cfg p = some fr) (h2 : Scc.Cert.LowerStage.ir1 cfg p = some r) :
    lowered1 cfg p = some r :=
  Scc.Cert.LowerStage.lowerIR_of_stages h1 h2
/-- **The output computed from a stage** at the assembler's sizes and label
offsets (`Out.ofEmitted`'s fields). -/
def ofStage (sizes : List Nat) (labelOffs : List (String × Nat)) : Stage → Out
  | (ir, items, sps, need, setup) =>
    let secs := Scc.Emit.Data.Secs.ofProgram ir.data (if ir.growth.isSome then some sps else none)
    let cells := ((textDirectives items).bind (sizedCells · sizes)).getD []
    ⟨cells, ⟨secs.data, secs.bss, secs.rodata⟩, labelOffs,
      { blocks := (Data.blocksOf? ir cells).getD []
        need := need.getD []
        tail := if setup then .setup else .bare
        ir := some ir }⟩

/-- **`out` from its stages**: where the lowering gives the IR `ir` (and the
setup flag) and the emitter its items and safepoints, scc's output is
`ofStage` of them, with the stack need table of `ir`. -/
theorem ofEmitted_of_stages {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items : List Item} {sps : List (String × List Int × List Int)} (sizes : List Nat)
    (labelOffs : List (String × Nat))
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.X64.emitItemsMaps ir = .ok (items, sps)) :
    Out.ofEmitted (lowerAll cfg p) sizes labelOffs =
      ofStage sizes labelOffs (ir, items, sps, (Scc.Lower.stackNeed .x64 ir).toOption, setup) := by
  unfold lowered1 at h1
  split at h1
  · rename_i l hl
    cases h1
    unfold lowerAll lowerAll?
    simp only [hl, bind, Except.bind, emitAll, h2, pure, Except.pure]
    rfl
  · cases h1

/-! ## The block table, a stage per function

As on AArch64 (`Scc/Cert/OutStageA64.lean`): `ofStage`'s block table
(`Data.blocksOf?`: the offsets fixpoint of every function) is most of the
last step's work and memory, and with every function in one declaration the
kernel keeps all their terms alive at once. On a large listing a
certificate checks it in its own declarations, on the literal items: the
items' functions as a literal (`Data.splitFns`, checked once), each
function's groups in a declaration of its own, chained (`mapM_some_cons`,
`blocksOfStage_of_split`); the last step then compares the rest
(`ofStage_eq_B`). -/

/-- The code cells of the items at the assembler's sizes (`ofStage`'s). -/
def cellsOfStage (sizes : List Nat) (items : List Item) : List (Directive × Nat) :=
  ((textDirectives items).bind (sizedCells · sizes)).getD []

/-- The block table of the items' code cells (`ofStage`'s). -/
def blocksOfStage (sizes : List Nat) (ir : Scc.IR.Program) (items : List Item) : Option (List Rt.X64.OGrp) :=
  Data.blocksOf? ir (cellsOfStage sizes items)

/-- **`ofStage` at the block table `blks`** in place of `blocksOfStage`'s. -/
def ofStageB (sizes : List Nat) (labelOffs : List (String × Nat)) : Stage → List Rt.X64.OGrp → Out
  | (ir, items, sps, need, setup), blks =>
    let secs := Scc.Emit.Data.Secs.ofProgram ir.data (if ir.growth.isSome then some sps else none)
    ⟨cellsOfStage sizes items, ⟨secs.data, secs.bss, secs.rodata⟩, labelOffs,
      { blocks := blks
        need := need.getD []
        tail := if setup then .setup else .bare
        ir := some ir }⟩

/-- **`ofStage` from its block table**: where the items' block table is
`blks`, `ofStage` is `ofStageB` at `blks`. -/
theorem ofStage_eq_B {sizes : List Nat} {labelOffs : List (String × Nat)} {ir : Scc.IR.Program}
    {items : List Item} {sps : List (String × List Int × List Int)}
    {need : Option (List (Scc.IR.Sym × Nat × Nat))} {setup : Bool} {blks : List Rt.X64.OGrp}
    (h : blocksOfStage sizes ir items = some blks) :
    ofStage sizes labelOffs (ir, items, sps, need, setup) =
      ofStageB sizes labelOffs (ir, items, sps, need, setup) blks := by
  simp only [blocksOfStage, cellsOfStage] at h
  simp only [ofStage, ofStageB, cellsOfStage, h, Option.getD_some]

/-- The keys of the functions `blocksOfStage` splits at. -/
def fnKeys (ir : Scc.IR.Program) : List Nat := (Data.declared ir).map Rt.X64.key

/-- The functions of the items' code cells (`blocksOfStage`'s). -/
def splitStage (sizes : List Nat) (ir : Scc.IR.Program) (items : List Item) : List (Label × List Data.It) :=
  Data.splitFns (fnKeys ir) (cellsOfStage sizes items)

/-- A function's groups (`Data.fnGrps` on a pair). -/
def grpsOf (f : Label × List Data.It) : Option (List Rt.X64.OGrp) := Data.fnGrps f.1 f.2

/-- `mapM` (in `Option`) on a cons from `g` on the head and `mapM` on the
tail. -/
theorem mapM_some_cons {α β : Type} {g : α → Option β} {x : α} {xs : List α} {y : β} {ys : List β}
    (h : g x = some y) (t : xs.mapM g = some ys) : (x :: xs).mapM g = some (y :: ys) := by
  rw [List.mapM_cons, h, t]
  rfl

/-- **`blocksOfStage` from the functions' groups.** -/
theorem blocksOfStage_of_split {sizes : List Nat} {ir : Scc.IR.Program} {items : List Item}
    {fs : List (Label × List Data.It)} {gs : List (List Rt.X64.OGrp)} (hs : splitStage sizes ir items = fs)
    (h : fs.mapM grpsOf = some gs) : blocksOfStage sizes ir items = some gs.flatten := by
  unfold splitStage fnKeys at hs
  unfold blocksOfStage Data.blocksOf?
  rw [hs]
  have : (fs.mapM fun (x : Label × List Data.It) => Data.fnGrps x.1 x.2) = some gs := h
  rw [this]
  rfl

end Scc.Cert.PlaceOK.X64
