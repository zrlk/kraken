import Scc.Cert.OutLitX64
import Scc.Cert.LowerStage

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
  `ir`.

A certificate states `ir`, `items` and `sps` as literals (`scc_lit%`,
untrusted), checks the two equations, and then `ofStage … = outLit` (the
stack need table, the `.text` filter, the sized cells and the offsets
fixpoint, on literals): three declarations, each with a part of the work.
-/

deriving instance Lean.ToExpr for Scc.Emit.X64.Item

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
depth limit `fr` of the budget and the lowering at `fr`, each a kernel check
of one lowering. -/
theorem lowered1_of_stages {cfg : Scc.Config} {p : CoreTerm.Prog} {fr : Nat} {r : Scc.IR.Program × Bool}
    (h1 : Scc.Cert.LowerStage.frames1 cfg p = some fr) (h2 : Scc.Cert.LowerStage.ir1 cfg p fr = some r) :
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

end Scc.Cert.PlaceOK.X64
