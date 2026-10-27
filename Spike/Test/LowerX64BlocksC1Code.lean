import Spike.Lib.LowerX64.BlocksC1Code

/-!
# The code predicate of an `Accepted1` block with calls on x86-64

`Spike/Lib/LowerX64/BlocksC1Code.lean` at work: `CodeC`'s arms unfolded on
an `unreachable`, a `ret`, a non-call instruction and a one-word user call.
-/

namespace Spike.Test.LowerX64BlocksC1Code

open Scc.Emit.X64 (Item emitInst emitTerm)
open Spike.Lib.LowerX64

variable (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
  (Bl : Int64 → Nat → Label → Nat → Prop)

/-- `unreachable` makes no claim. -/
example (k : Nat) (pc : Int64) : CodeC fr Cd Bl k pc [] .unreachable := Or.inl rfl

/-- A `ret`'s code at `pc`, at some cell sizes. -/
example (k : Nat) (pc : Int64) (w : Scc.IR.Operand) (l : List Item) (zs : List Nat)
    (h : Emits (emitTerm fr (.ret [w])) l) (hz : zs.length = (dirs l).length) (hc : Cd pc ((dirs l).zip zs)) :
    CodeC fr Cd Bl k pc [] (.ret [w]) := Or.inr ⟨l, zs, h, hz, hc⟩

/-- The thread-pointer read, then the block's rest at the same label
counter. -/
example (k : Nat) (pc : Int64) (d : Scc.IR.Reg) (l : List Item) (zs : List Nat) (is : List Scc.IR.Inst)
    (tm : Scc.IR.Term) (h : Emits (emitInst fr none (.getTp d)) l) (hz : zs.length = (dirs l).length)
    (hc : Cd pc ((dirs l).zip zs)) (hr : CodeC fr Cd Bl k (pc + Int64.ofNat zs.sum) is tm) :
    CodeC fr Cd Bl k pc (.getTp d :: is) tm := Or.inl ⟨rfl, l, zs, h, hz, hc, hr⟩

/-- A one-word user call at label counter `k`: the argument's load, the
`callq` with return label `.L<fn>.x<k>` (`Bl _ _ _ k`), the result's store,
then the rest from `k + 1`. -/
example (k : Nat) (pc : Int64) (d : Scc.IR.Reg) (g : String) (w : Scc.IR.Operand) (lw : List Item)
    (off : Int) (zs : List Nat) (zc z : Nat) (tm : Scc.IR.Term) (hw : getOp fr .rdi w = .ok lw)
    (hd : rsOf fr d = some off) (hz : zs.length = (dirs lw).length) (h1 : Cd pc ((dirs lw).zip zs))
    (h2 : Bl (pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) k)
    (h3 : Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)])
    (hr : CodeC fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z) [] tm) :
    CodeC fr Cd Bl k pc [.call [d] (Scc.Lower.Names.user g) [w]] tm :=
  Or.inr ⟨d, g, w, lw, off, zs, zc, z, rfl, hw, hd, hz, h1, h2, h3, hr⟩

/--
info: 'Spike.Lib.LowerX64.emitInst_sm' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms emitInst_sm

/-- info: 'Spike.Lib.LowerX64.codeC_of_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms codeC_of_seg

/-- info: 'Spike.Lib.LowerX64.cdOf_cdC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cdOf_cdC

/-- info: 'Spike.Lib.LowerX64.hgap_of_lays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hgap_of_lays

/-- info: 'Spike.Lib.LowerX64.runPhB_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms runPhB_congr

/-- info: 'Spike.Lib.LowerX64.ne_abortI_of_callBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ne_abortI_of_callBlk

/-- info: 'Spike.Lib.LowerX64.codeC_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms codeC_block

/-- info: 'Spike.Lib.LowerX64.blocksCodeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blocksCodeC

/-- info: 'Spike.Lib.LowerX64.entryCodeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entryCodeC

/-- info: 'Spike.Lib.LowerX64.fnCodeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnCodeC

/-- info: 'Spike.Lib.LowerX64.hgap_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hgap_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.fnCodeC_of_fnPh1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnCodeC_of_fnPh1

/-- info: 'Spike.Lib.LowerX64.fnCodeC_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnCodeC_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.cdOf_blC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cdOf_blC

/-- info: 'Spike.Lib.LowerX64.blC_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms blC_ph

/-- info: 'Spike.Lib.LowerX64.runsAux_head' depends on axioms: [propext] -/
#guard_msgs in
#print axioms runsAux_head

end Spike.Test.LowerX64BlocksC1Code
