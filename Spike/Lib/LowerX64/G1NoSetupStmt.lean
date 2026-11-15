/-
**The start of an `Accepted2` program without a setup block: the
statement** (x86-64; the twin of `Spike/Lib/LowerA64/G1NoSetupStmt.lean`):
`H0NoneStmtW`, the segment obligations `In2XW`
(`Spike/Lib/LowerX64/Closed2AtW.lean`) at every instance of `Closed2InW`
whose program has no setup block (`setupOf p = none`).

`Accepted2` asks for the setup block only when `main` takes its result
(`setupPresent`), so `Closed2InW` covers programs whose `main` takes the
unit and is called by `scc_rt_main` directly (the bare start, `bareMC`,
the output's `.bare` tail). Such a program allocates nothing (`newBuf` is
the setup block's only), so its landings are empty.

The premises are the ones the setup start's assembly carries, in its
order: the output's user code passing the branch-target check `tgOkB`, the
program-wide function segment `FnSpecC2At` (`Spike/Lib/LowerX64/G1FnSpec.lean`)
and `main`'s segment at its callee frames `MainSeg2`
(`Spike/Lib/LowerX64/G1MainStmt.lean`), both at the write tail
`fun _ => True`.

- `H0NoneStmtW`: the statement.
-/
import Spike.Lib.LowerX64.Closed2AtW
import Spike.Lib.LowerX64.G1MainStmt

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64ConsumerS (InvS)

/-- **The start of an `Accepted2` program without a setup block** (see the
module docstring): at every instance of `Closed2InW` (binders in its
order) whose program has no setup block (`hnone`), every admissible entry
state `E` and placement `h'` at `lay2 Λ p`, whose output's user code passes
`tgOkB`, from the program-wide function segment and `main`'s segment at the
write tail `fun _ => True` and every frame invariant, `In2XW`. -/
def H0NoneStmtW : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted2 p = true),
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true → Scc.Lower.setupOf p = none → ∀ E : Entry, E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true →
    (∀ (J : InvS) (Bot : StkKey → List TermRun.Frame → Prop), FnSpecC2At h' hp (fun _ => True) J Bot) →
    (∀ J : InvS, MainSeg2 h' hp (fun _ => True) J) →
    In2XW h' E

end Spike.Lib.LowerX64
