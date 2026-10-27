import Scc.Cert.OutLitA64
import Scc.Cert.LowerStage
import Scc.Cert.A12StageA64
import Scc.Cert.A2StageA64

/-!
# `out = outLit` in three kernel steps (AArch64, `scc --cert`)

A certificate checks `out = outLit` (`Scc/Cert/OutLit.lean`), `out` being
`Out.ofEmitted (lowerAll cfg prog_src)`. Checked as one definitional
equality, the kernel runs the lowering, the emitter, the `.text` filter
and the block table's offsets fixpoint in one declaration, and keeps every
intermediate term of all four alive: on a large program (`arith.w`) more
than 5 GB.

`ofStage` computes the output from what it is made of: the lowered IR, the
emitter's items and safepoints, the stack need table and the shape of
`scc_rt_main`'s tail. `ofEmitted_of_stages` proves `Out.ofEmitted
(lowerAll cfg p) = ofStage …` from two equations, each a kernel check of
one stage on literals:

* `lowered1 cfg p = some (ir, setup)`: the lowering (`lowerIR`) gives the
  IR `ir`;
* `emitItemsMaps ir = .ok (items, sps)`: the emitter, run on the literal
  `ir` (itself checked in stages, `Scc.Emit.A64.emitItemsMaps_of_stages`:
  the emitter's checks, each function, and the rest).

A certificate states `ir`, `items` and `sps` as literals (`scc_lit%`,
untrusted), checks the two equations, and then `ofStage … = outLit` (the
stack need table, the `.text` filter and the offsets fixpoint, on
literals): three declarations, each with a part of the work. The block
table can be a fourth (`blocksOfStage`, `ofStage_eq_B`).
-/

deriving instance Lean.ToExpr for Scc.Emit.A64.Item
deriving instance Lean.ToExpr for Scc.Cert.Rt.A64.PhTab
deriving instance Lean.ToExpr for Scc.Cert.PlaceOK.A64.A12Tabs

namespace Scc.Cert.PlaceOK.A64

open Scc.Lower.A64 (Emitted lowerAll lowerAll? emitAll textDirectives)
open Scc.Emit.A64 (Item Safepoint)

/-- What the output is computed from: the IR, the items, the safepoints,
the stack need table, whether `scc_rt_main` has a setup block. -/
abbrev Stage := Scc.IR.Program × List Item × List Safepoint × Option (List (Scc.IR.Sym × Nat × Nat)) × Bool

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
/-- **The output computed from a stage** (`Out.ofEmitted`'s fields). -/
def ofStage : Stage → Out
  | (ir, items, sps, need, setup) =>
    let secs := Scc.Emit.Data.Secs.ofProgram ir.data (if ir.growth.isSome then some sps else none)
    ⟨textDirectives items, ⟨secs.data, secs.bss, secs.rodata⟩, [],
      { blocks := (Data.blocksOf? ir (textDirectives items)).getD []
        need := need.getD []
        tail := if setup then .setup else .bare
        ir := some ir }⟩

/-- **`out` from its stages**: where the lowering gives the IR `ir` (and the
setup flag) and the emitter its items and safepoints, scc's output is
`ofStage` of them, with the stack need table of `ir`. -/
theorem ofEmitted_of_stages {cfg : Scc.Config} {p : CoreTerm.Prog} {ir : Scc.IR.Program} {setup : Bool}
    {items : List Item} {sps : List Safepoint}
    (h1 : lowered1 cfg p = some (ir, setup)) (h2 : Scc.Emit.A64.emitItemsMaps ir = .ok (items, sps)) :
    Out.ofEmitted (lowerAll cfg p) =
      ofStage (ir, items, sps, (Scc.Lower.stackNeed .arm ir).toOption, setup) := by
  unfold lowered1 at h1
  split at h1
  · rename_i l hl
    cases h1
    unfold lowerAll lowerAll?
    simp only [hl, bind, Except.bind, emitAll, h2, pure, Except.pure]
    rfl
  · cases h1

/-! ## The block table, its own stage

`ofStage`'s block table (`Data.blocksOf?`: the offsets fixpoint of every
function) is most of the last step's work and memory. A certificate checks
it in its own declaration, on the literal items (`blocks_eq`, a literal
`blks`), and the last step then compares the rest (`ofStage_eq_B`). -/

/-- The block table of the items' instruction list (`ofStage`'s). -/
def blocksOfStage (ir : Scc.IR.Program) (items : List Item) : Option (List Rt.A64.OGrp) :=
  Data.blocksOf? ir (textDirectives items)

/-- **`ofStage` at the block table `blks`** in place of `blocksOfStage`'s. -/
def ofStageB : Stage → List Rt.A64.OGrp → Out
  | (ir, items, sps, need, setup), blks =>
    let secs := Scc.Emit.Data.Secs.ofProgram ir.data (if ir.growth.isSome then some sps else none)
    ⟨textDirectives items, ⟨secs.data, secs.bss, secs.rodata⟩, [],
      { blocks := blks
        need := need.getD []
        tail := if setup then .setup else .bare
        ir := some ir }⟩

/-- **`ofStage` from its block table**: where the items' block table is
`blks`, `ofStage` is `ofStageB` at `blks`. -/
theorem ofStage_eq_B {ir : Scc.IR.Program} {items : List Item} {sps : List Safepoint}
    {need : Option (List (Scc.IR.Sym × Nat × Nat))} {setup : Bool} {blks : List Rt.A64.OGrp}
    (h : blocksOfStage ir items = some blks) :
    ofStage (ir, items, sps, need, setup) = ofStageB (ir, items, sps, need, setup) blks := by
  simp only [blocksOfStage] at h
  simp only [ofStage, ofStageB, h, Option.getD_some]

/-! ## The block table, a stage per function

`blocksOfStage` is an offsets fixpoint per function (`Data.fnGrps`); with
every function in one declaration, the kernel keeps all their terms alive
at once. A certificate states the items' functions as literals
(`Data.splitFns`, checked once), checks each function's groups in its own
declaration and chains them (`mapM_some_cons`, `blocksOfStage_of_split`). -/

/-- The keys of the functions `blocksOfStage` splits at. -/
def fnKeys (ir : Scc.IR.Program) : List Nat := (Data.declared ir).map Rt.A64.key

/-- The functions of the items' instruction list (`blocksOfStage`'s). -/
def splitStage (ir : Scc.IR.Program) (items : List Item) : List (Label × List Data.It) :=
  Data.splitFns (fnKeys ir) (textDirectives items)

/-- A function's groups (`Data.fnGrps` on a pair). -/
def grpsOf (f : Label × List Data.It) : Option (List Rt.A64.OGrp) := Data.fnGrps f.1 f.2

/-- `mapM` (in `Option`) on a cons from `g` on the head and `mapM` on the
tail. -/
theorem mapM_some_cons {α β : Type} {g : α → Option β} {x : α} {xs : List α} {y : β} {ys : List β}
    (h : g x = some y) (t : xs.mapM g = some ys) : (x :: xs).mapM g = some (y :: ys) := by
  rw [List.mapM_cons, h, t]
  rfl

/-- **`blocksOfStage` from the functions' groups.** -/
theorem blocksOfStage_of_split {ir : Scc.IR.Program} {items : List Item} {fs : List (Label × List Data.It)}
    {gs : List (List Rt.A64.OGrp)} (hs : splitStage ir items = fs) (h : fs.mapM grpsOf = some gs) :
    blocksOfStage ir items = some gs.flatten := by
  unfold splitStage fnKeys at hs
  unfold blocksOfStage Data.blocksOf?
  rw [hs]
  have : (fs.mapM fun (x : Label × List Data.It) => Data.fnGrps x.1 x.2) = some gs := h
  rw [this]
  rfl

end Scc.Cert.PlaceOK.A64
