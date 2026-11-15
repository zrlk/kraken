/-
**The start of an `Accepted2` program without a setup block** (AArch64):
`h0NoneW : H0NoneStmtW` (`Spike/Lib/LowerA64/G1NoSetupStmt.lean`). Such a
program allocates nothing, so its landings are empty (`H1InAW` holds of
the empty states); the start's segment is `h0InAW_bare`
(`Spike/Lib/LowerA64/G1NoSetupH0.lean`) at the bounds `stackBounds0` and
`main`'s call `mainCall0` (`Spike/Lib/LowerA64/G1NoSetupCallStmt.lean`) from
`main`'s segment at the write tail `fun _ => True`.

- `h0NoneW`: the statement.
-/
import Spike.Lib.LowerA64.G1NoSetupH0

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- **The start of an `Accepted2` program without a setup block**: the
landings' states empty, the write tail `fun _ => True`, `H0InAW` by
`h0InAW_bare` at the bounds of `stackBounds0` and `main`'s call of
`mainCall0`, `H1InAW` of the empty states. The function segment and the
branch-target check are not needed. -/
theorem h0NoneW : H0NoneStmtW := by
  intro cfg pcfg p Λ hp hR _ hcfg hs E hE h' _ _ HM
  obtain ⟨L, D, lM, fM, nM, hB⟩ := stackBounds0 cfg pcfg p (lay2 Λ p) h' hp hs hcfg
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h' (Spike.Lib.LowerNode.imms2Me Λ p))
  exact ⟨fun _ _ _ _ _ _ _ _ => False, fun _ => True,
    h0InAW_bare h' hp hs hE hB (mainCall0 cfg pcfg p Λ hp hR hcfg hs h' E _ _ HM),
    ⟨fun _ _ _ _ _ _ _ _ _ _ => SegWS.empty fun _ _ _ h => h⟩⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.h0NoneW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0NoneW

end Spike.Lib.LowerA64
