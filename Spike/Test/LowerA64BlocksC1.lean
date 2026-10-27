import Spike.Lib.LowerA64.BlocksC1

/-!
# An `Accepted1` block with calls on AArch64

`Spike/Lib/LowerA64/BlocksC1.lean` at work: every function `emitItemsMaps`
emits for `progOf`'s program places stack-map labels after its calls; a
one-word call's argument and result; a call site's run before its `bl`
from `callSite1`'s split, instructions only, as `call_blockAt` asks. The
lemmas' axioms.
-/

namespace Spike.Test.LowerA64BlocksC1

open Kraken.AArch64.Parser
open Scc.Emit.A64
open Spike.Lib.LowerA64

/-- The functions of `progOf`'s program have stack-map labels on. -/
example (lay : Scc.Layout) (rt fs : List Scc.IR.Func) (areas : List (Scc.IR.Sym × Nat)) (fi : Nat)
    (f : Scc.IR.Func) :
    (fnCtx Scc.Lower.Names.abort (Scc.Lower.Inv.progOf lay rt fs).growth areas fi f).maps = true := rfl

/-- One argument word is `x0`'s load, and nothing on the stack. -/
example (cx : FnCtx) (w : Scc.IR.Operand) : cx.callArgs [w] = cx.getOp .X0 w := callArgs_one w 0

/-- The allocator's three arguments `h`, `k`, `u` into `x0`, `x1`, `x2`. -/
example (cx : FnCtx) (h k u : Scc.IR.Operand) :
    cx.callArgs [h, k, u] = (do
      let lh ← cx.getOp .X0 h
      let lk ← cx.getOp .X1 k
      let lu ← cx.getOp .X2 u
      return lh ++ (lk ++ lu)) := callArgs_three h k u 0

/-- **A call block's `bl`, placed** (`callBlk_code`'s `A` instructions
only): `callSite1`'s split at the call (instruction 1, after the new
depth's store `c1`) has no label before the `bl`, and the run before it is
`c1` and the argument's load. -/
example {c1 ca : List Item} {X ys : List Directive} {L l : Label} (h1 : AllIns c1)
    (ha : AllIns ca) (hX : (X = [] ∧ L = l) ∨ ∃ X', X = X' ++ [.label L])
    (he : directives c1 ++ directives ca = X ++ ys) : L = l ∧ ys.all Scc.Cert.Rt.A64.isIns = true :=
  let h := callSite_run h1 ha hX he
  ⟨h.2.1, h.2.2.2⟩

/--
info: 'Spike.Lib.LowerA64.callBlk_code' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms callBlk_code

/--
info: 'Spike.Lib.LowerA64.callSite_run' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms callSite_run

/--
info: 'Spike.Lib.LowerA64.instsItems_allIns' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms instsItems_allIns

/--
info: 'Spike.Lib.LowerA64.callArgs_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms callArgs_eq

/--
info: 'Spike.Lib.LowerA64.term_allIns' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms term_allIns

end Spike.Test.LowerA64BlocksC1
