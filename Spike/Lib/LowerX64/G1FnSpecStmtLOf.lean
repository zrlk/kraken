/-
**Every compiled block of an `Accepted2` program is one segment inside
`W2` at every reachable placement** (x86-64; the twin of
`Spike/Lib/LowerA64/G1FnSpecStmtLOf.lean`'s `fnSpecC2StmtL`):
`FnSpecC2StmtL` (`Spike/Lib/LowerX64/G1FnSpecStmtL.lean`), by
`fnSpecC2AtL_of` at the construct statements' proofs:

- the plain call with its blocks asked at placed nodes (`callC2_ofFW`),
  the calls' blocks inside `W2` (`wCallG2L`) and the callees' prologues
  (`proCallG2L`);
- the room and limit rows (`room2Own`, `room2Callee`, `lim2Callee`,
  `limOk2L`);
- the lane stores and buffers (`laneBuf2L`) and the output calls
  (`print2L`).
-/
import Spike.Lib.LowerX64.G1FnSpecStmtL
import Spike.Lib.LowerX64.G1FnSpecOfL
import Spike.Lib.LowerX64.G1CallW
import Spike.Lib.LowerX64.G1WCallG2L
import Spike.Lib.LowerX64.G1ProCallG2L
import Spike.Lib.LowerX64.G1Room2
import Spike.Lib.LowerX64.G1LaneBufL
import Spike.Lib.LowerX64.G1PrintL
import Spike.Lib.LowerX64.G1LimOkL

namespace Spike.Lib.LowerX64

set_option autoImplicit false

/-- **The program-wide function segment of an `Accepted2` program at every
reachable placement** (`fnSpecC2AtL_of` at every instance). -/
theorem fnSpecC2StmtL : FnSpecC2StmtL := by
  intro cfg pcfg p sizes labelOffs Λ hp _hcfg h htg Dt hDt J Bot
  have hown := room2Own h hp
  have hrc := room2Callee h hp
  have hlc := lim2Callee h hp
  exact fnSpecC2AtL_of h callC2_ofFW hp hown hrc hlc (limOk2L h hp) (laneBuf2L h hp) (print2L h hp)
    htg (proCallG2L h hp hown hrc hlc) (wCallG2L h hp hown) hDt J Bot

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.fnSpecC2StmtL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.fnSpecC2StmtL
