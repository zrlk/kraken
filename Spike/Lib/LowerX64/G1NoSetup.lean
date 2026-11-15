/-
**The start of an `Accepted2` program without a setup block** (x86-64; the
twin of `Spike/Lib/LowerA64/G1NoSetup.lean`): `H0NoneStmtW`
(`Spike/Lib/LowerX64/G1NoSetupStmt.lean`) from `main`'s call at the bare
start `MainCall0Stmt` (`Spike/Lib/LowerX64/G1NoSetupDefs.lean`). Such a
program allocates nothing, so its landings are empty (`H1InW` holds of the
empty states); the start's segment is `h0InW_bare`
(`Spike/Lib/LowerX64/G1NoSetupH0.lean`) at the bounds `stackBounds0`
(`Spike/Lib/LowerX64/G1NoSetupBounds.lean`) and `main`'s call from
`main`'s segment at the write tail `fun _ => True`.

- `h0NoneW_of_mainCall0`: the statement from `MainCall0Stmt`;
- `h0NoneW`: the statement, at `mainCall0`.
-/
import Spike.Lib.LowerX64.G1NoSetupH0

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **The start of an `Accepted2` program without a setup block, from
`main`'s call at the bare start**: the landings' states empty, the write
tail `fun _ => True`, `H0InW` by `h0InW_bare` at the bounds of
`stackBounds0` and `main`'s call of `HM`, `H1InW` of the empty states. The
function segment and the branch-target check are not needed. -/
theorem h0NoneW_of_mainCall0 (HM : MainCall0Stmt) : H0NoneStmtW := by
  intro cfg pcfg p sizes labelOffs Λ hp hR _ hcfg hs E hE h' _ _ HS
  obtain ⟨L, D, lM, fM, nM, hB⟩ := stackBounds0 h' hp hs hcfg
    (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h' (Spike.Lib.LowerNode.imms2Me Λ p))
  exact ⟨fun _ _ _ _ _ => fun _ _ _ => False, fun _ => True,
    h0InW_bare h' hp hs hE hB (HM cfg pcfg p sizes labelOffs Λ hp hR hcfg hs h' E _ _ HS),
    ⟨fun _ _ _ _ _ _ _ _ _ _ => SegWS.empty fun _ _ _ h => h⟩⟩

/-- **The start of an `Accepted2` program without a setup block**:
`h0NoneW_of_mainCall0` at `main`'s call `mainCall0`
(`Spike/Lib/LowerX64/G1NoSetupCallStmt.lean`). -/
theorem h0NoneW : H0NoneStmtW := h0NoneW_of_mainCall0 mainCall0

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.h0NoneW_of_mainCall0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0NoneW_of_mainCall0

/-- info: 'Spike.Lib.LowerX64.h0NoneW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0NoneW

end Spike.Lib.LowerX64
