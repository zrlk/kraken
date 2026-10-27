import Spike.Lib.LowerA64.ProWS

/-!
# A code block's prologue inside the body's fragment at depth (AArch64)

`Spike/Lib/LowerA64/ProWS.lean`: the prologue obligation of a code block's
segment inside `BodyWS0` at the frames, from the prologue's code and phase
facts (with its parameter spill), and the prologue with saved registers
inside the consumer's facts (`Spike/Lib/LowerA64/UserW.lean`); the axioms
of the pieces.
-/

namespace Spike.Test.LowerA64ProWS

/-- info: 'Spike.Lib.LowerA64.proW_sfactsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.proW_sfactsP

/-- info: 'Spike.Lib.LowerA64.spillsOk_of_spills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.spillsOk_of_spills

/-- info: 'Spike.Lib.LowerA64.proW_bodyS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.proW_bodyS

/-- A one-parameter spill: `x0` to the parameter's slot, a cell of the frame. -/
example {cx : Scc.Emit.A64.FnCtx} (hf : Scc.Lower.InvA64.FrameOk cx) (h1 : cx.frame ≤ 4095)
    (h16 : cx.frame % 16 = 0) {pr : Scc.IR.Reg} {ps}
    (hps : Scc.Cert.Code1A64.spills cx [pr] = some ps) :
    ∀ q ∈ ps, Spike.Lib.offOk (-(Int64.ofInt cx.frame).toInt) 0 (-(Int64.ofInt cx.frame).toInt + q.2.toInt) = true :=
  Spike.Lib.LowerA64.spillsOk_of_spills hf h1 h16 hps

end Spike.Test.LowerA64ProWS
