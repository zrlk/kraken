/-
**Every compiled block of an `Accepted2` program is one segment inside
`W2`** (AArch64): `FnSpecC2Stmt` (`Spike/Lib/LowerA64/G1FnSpec.lean`), by
`fnSpecC2At_of` at the construct statements' proofs:

- the plain call with its blocks asked at placed nodes (`callC2_ofFW`),
  the calls' blocks inside `W2` (`wCallG2`) and the callees' prologues
  (`proCallG2`);
- the room and limit rows (`room2Own`, `room2Callee`, `lim2Callee`,
  `limOk2`);
- the lane stores and buffers (`laneBuf2`) and the output calls
  (`print2`).
-/
import Spike.Lib.LowerA64.G1FnSpecOf
import Spike.Lib.LowerA64.G1CallW
import Spike.Lib.LowerA64.G1WCallG2
import Spike.Lib.LowerA64.G1ProCallG2
import Spike.Lib.LowerA64.G1Room2
import Spike.Lib.LowerA64.G1LaneBuf
import Spike.Lib.LowerA64.G1Print

namespace Spike.Lib.LowerA64

set_option autoImplicit false

/-- **The program-wide function segment of an `Accepted2` program**
(`fnSpecC2At_of` at every instance). -/
theorem fnSpecC2Stmt : FnSpecC2Stmt := by
  intro cfg pcfg p Λ hp _hcfg h htg Dt hDt J Bot
  have hown := room2Own h hp
  have hrc := room2Callee h hp
  have hlc := lim2Callee h hp
  exact fnSpecC2At_of h callC2_ofFW hp hown hrc hlc (limOk2 h hp) (laneBuf2 h hp) (print2 h hp) htg
    (proCallG2 h hp hown hrc hlc) (wCallG2 h hp hown) hDt J Bot

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.fnSpecC2Stmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.fnSpecC2Stmt
