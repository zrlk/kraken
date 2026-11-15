/-
**`main`'s segment at every reachable placement for every `Accepted2`
program** (x86-64): `MainSeg2LStmt` (`Spike/Lib/LowerX64/G1MainCallL.lean`)
by `mainSeg2L_of` (`Spike/Lib/LowerX64/G1MainSegL.lean`) at the write tail
`fun _ => True`, the function segment from `fnSpecC2StmtL`
(`Spike/Lib/LowerX64/G1FnSpecStmtLOf.lean`).

- `mainSeg2LStmt_of`: `MainSeg2LStmt`.
-/
import Spike.Lib.LowerX64.G1MainSegL
import Spike.Lib.LowerX64.G1MainCallL
import Spike.Lib.LowerX64.G1FnSpecStmtLOf

namespace Spike.Lib.LowerX64

set_option autoImplicit false

/-- **`MainSeg2LStmt`**: `mainSeg2L_of` at the write tail `fun _ => True`
(its premises at the output call and the aborts trivial), the function
segment `fnSpecC2StmtL` at the bottom keys `fun _ _ => True`. -/
theorem mainSeg2LStmt_of : MainSeg2LStmt := by
  intro cfg pcfg p sizes labelOffs Λ hp hcfg h htg J
  exact mainSeg2L_of h hp htg (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fnSpecC2StmtL cfg pcfg p sizes labelOffs Λ hp hcfg h htg _ (fun _ _ _ _ _ _ _ _ _ => trivial) J _)

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainSeg2LStmt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainSeg2LStmt_of
