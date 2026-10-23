/-
**The start's segment at `ret0`'s placement check** (`Spike/Lib/LowerA64/StartSeg.lean`):
`a64_start_segW` specialises to `ret0_placeOK`'s layout; the switch region's
depth `frame + 96` fits the first stack at the largest `Accepted0` frame
(`4080`, the 16-aligned bound below `4095`) and would not at a frame of a
whole stack.
-/
import Spike.Lib.LowerA64.StartSeg
import Spike.Test.A64PhRec

namespace Spike.Test.LowerA64StartSeg

open Spike.Lib.LowerA64

/-- `a64_start_segW` at `ret0`'s placement check. -/
example := @a64_start_segW _ _ _
  (Scc.Cert.PlaceOK.A64.atTables Scc.Cert.PlaceOK.A64.Test.ret0_placeOK) SccCode.ret0Imms

/-- **Oracle**: the largest 16-aligned frame below `4095` gives a switch
region inside the first stack. -/
example : (4080 : Int) + 96 ≤ 16384 ∧ 4080 % 16 = 0 ∧ (4080 : Int) ≤ 4095 := by decide

/-- **Negative**: a frame of a whole stack does not fit. -/
example : ¬ ((16384 : Int) + 96 ≤ 16384) := by decide

end Spike.Test.LowerA64StartSeg
