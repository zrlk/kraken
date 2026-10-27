import Spike.Lib.LowerA64.CallC

/-!
# The plain call (AArch64)

`Spike/Lib/LowerA64/CallC.lean`: the plain call (`CallC`, without the depth
counter) from the callees' segments and the call's blocks inside `W`
(`callC_of`), its pieces (the argument's load, `bl g`, the callee, the
result's store), and the call premise from it (`callPreC_of`); the axioms of
the pieces.
-/

namespace Spike.Test.LowerA64CallC

/-- info: 'Spike.Lib.LowerA64.argC_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.argC_seg

/-- info: 'Spike.Lib.LowerA64.blC_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.blC_seg

/-- info: 'Spike.Lib.LowerA64.frame_outC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.frame_outC

/-- info: 'Spike.Lib.LowerA64.calleeC_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.calleeC_seg

/-- info: 'Spike.Lib.LowerA64.resC_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.resC_seg

/-- info: 'Spike.Lib.LowerA64.callC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.callC_of

/-- info: 'Spike.Lib.LowerA64.callPreC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.callPreC_of

/-- info: 'Spike.Lib.LowerA64.bodyC_segS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.bodyC_segS

/-- info: 'Spike.Lib.LowerA64.bodySpecC_of_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.bodySpecC_of_call

/-- `CallBlk` holds at an argument's load. -/
example {cx : Scc.Emit.A64.FnCtx} {w : Scc.IR.Operand} {lw : List Scc.Emit.A64.Item}
    (hw : cx.getOp .X0 w = .ok lw) : Spike.Lib.LowerA64.CallBlk cx (Scc.Emit.A64.directives lw) :=
  .inl ⟨w, lw, hw, rfl⟩

end Spike.Test.LowerA64CallC
