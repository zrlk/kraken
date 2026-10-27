import Spike.Lib.LowerX64.BlocksC1

/-!
# An `Accepted1` block with calls on x86-64

`Spike/Lib/LowerX64/BlocksC1.lean` at work: every function of `progOf`'s
program records safepoints after its calls; a one-word call's argument;
the allocator's three arguments; a call site's run before its `callq` from
`callSite1`'s split, label-free, as `call_blockAt` asks. The lemmas'
axioms.
-/

namespace Spike.Test.LowerX64BlocksC1

open Scc.Emit.X64 (Item directives)
open Spike.Lib.LowerX64

/-- The functions of `progOf`'s program record safepoints. -/
example (lay : Scc.Layout) (rt fs : List Scc.IR.Func) (f : Scc.IR.Func) :
    (frOf (Scc.Lower.Inv.progOf lay rt fs) f).maps = true := frOf_maps (growth_progOf lay rt fs) f

/-- One argument word is `%rdi`'s load, and nothing on the stack. -/
example (fr : Scc.Emit.X64.Frame) (w : Scc.IR.Operand) (what : String) :
    Scc.Emit.X64.callArgs fr [w] what = (Scc.Emit.X64.ld fr w .rdi >>= fun _ => pure ()) :=
  callArgs_one_eq fr w what

/-- The allocator's three arguments `h`, `k`, `u` into `%rdi`, `%rsi`, `%rdx`. -/
example (fr : Scc.Emit.X64.Frame) (h k u : Scc.IR.Operand) :
    getOps fr ([h, k, u].zip Scc.Emit.X64.argRegs) = (do
      let lh ← getOp fr .rdi h
      let lk ← getOp fr .rsi k
      let lu ← getOp fr .rdx u
      return lh ++ (lk ++ lu)) := callArgs_three fr h k u

/-- **A call block's `callq`, placed** (`callBlk_code`'s `A` label-free):
`callSite1`'s split at the call has no label before the `callq`, and the
run before it is `A`'s directives. -/
example {A : List Item} {Xd ys rest rest' : List Directive} {L l a b : Label} {c c' : Directive}
    (hA : AllIns A) (hys : ys.all (fun d => !d.isLabel) = true) (hr' : rest'.all (fun d => !d.isLabel) = true)
    (hc : c.isLabel = false) (hc' : c'.isLabel = false)
    (hX : (Xd = [] ∧ L = l) ∨ ∃ X', Xd = X' ++ [.label L])
    (he : Xd ++ ys ++ c :: .label a :: rest = directives A ++ c' :: .label b :: rest') :
    L = l ∧ ys = directives A :=
  let h := callSite_run hA hys hr' hc hc' hX he
  ⟨h.2.1, h.2.2⟩

/-- The `unreachable` terminator is one `ud2`, label-free. -/
example (fr : Scc.Emit.X64.Frame) (s : Scc.Emit.X64.S) :
    Scc.Emit.X64.emitTerm fr .unreachable s = .ok ((), { s with out := .d (Scc.Emit.X64.i64 .ud2) :: s.out }) := rfl

/--
info: 'Spike.Lib.LowerX64.callBlk_code' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms callBlk_code

/--
info: 'Spike.Lib.LowerX64.callSite_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms callSite_run

/--
info: 'Spike.Lib.LowerX64.instsCode_allIns' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms instsCode_allIns

/--
info: 'Spike.Lib.LowerX64.emitInst_allIns' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms emitInst_allIns

/--
info: 'Spike.Lib.LowerX64.emitTerm_allIns' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms emitTerm_allIns

/--
info: 'Spike.Lib.LowerX64.emitInst_call1_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms emitInst_call1_inv

/--
info: 'Spike.Lib.LowerX64.callArgs_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms callArgs_eq

end Spike.Test.LowerX64BlocksC1
