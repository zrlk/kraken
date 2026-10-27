import Spike.Lib.LowerX64.BodyC

/-!
# A lowered `Accepted1` body with calls as one segment at fixed frames on x86-64

`Spike/Lib/LowerX64/BodyC.lean` at work: a block of the code predicate is
its own sub-block, a `ret`'s items, and the axioms of the pieces.
-/

namespace Spike.Test.LowerX64BodyC

open Scc.Emit.X64 (Item emitTerm)
open Spike.Lib.LowerX64

/-- A block of `Cd` is a sub-block of itself. -/
example (Cd : Int64 → List (Directive × Nat) → Prop) (pc : Int64) (blk : List (Directive × Nat))
    (h : Cd pc blk) : SubCd Cd pc blk := SubCd.whole h

/-- A `ret`'s items are the load into `%rax`, the epilogue and `ret`. -/
example (fr : Scc.Emit.X64.Frame) (w : Scc.IR.Operand) (l : List Item) (h : Emits (emitTerm fr (.ret [w])) l) :
    ∃ lw, getOp fr .rax w = .ok lw ∧ dirs l = retDirs lw := emits_ret h

/-- info: 'Spike.Lib.LowerX64.cdOf_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cdOf_sub

/-- info: 'Spike.Lib.LowerX64.subCd_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms subCd_split

/-- info: 'Spike.Lib.LowerX64.emits_br' depends on axioms: [propext] -/
#guard_msgs in
#print axioms emits_br

/-- info: 'Spike.Lib.LowerX64.lowerC_term_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerC_term_ne

/-- info: 'Spike.Lib.LowerX64.bodyC_segS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bodyC_segS

/-- info: 'Spike.Lib.LowerX64.kind1_zip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms kind1_zip

end Spike.Test.LowerX64BodyC
