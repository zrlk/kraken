/-
**The x86-64 compiler theorem for an `Accepted2` program from the generic
producers** (G1.5's final step): `Closed2Stmt`
(`Spike/Lib/LowerX64/Closed2Stmt.lean`) at every configuration whose object
layout's header scalar count starts below bit 22, by `closed2Stmt_at`
(`Spike/Lib/LowerX64/G1Closed2.lean`), from the two open statements as
named hypotheses:

- `TgOkBStmt`: the branch-target check on every output;
- `MainSeg2LStmt` (`Spike/Lib/LowerX64/G1MainCallL.lean`): `main`'s
  segment at every reachable placement.

The function segment (`fnSpecC2Stmt`), `main`'s segment at the start
(`mainSeg2Stmt_ofL`), `main`'s call after the setup block
(`huSetupStmt_of`), the landings (`h1SetupStmt_ofMainSeg2L`) and the
bare start (`h0NoSetupStmt`, by `h0NoneW`
(`Spike/Lib/LowerX64/G1NoSetup.lean`)) are proved.

- `h0NoSetupStmt`: `H0NoSetupStmt` (`h0NoneW`);
- `Closed2StmtH`: `Closed2Stmt` at the configurations with the header
  bound;
- `closed2Stmt_x64`: `Closed2StmtH` from the two statements;
- `closed2Stmt_x64_tg`: `Closed2StmtH` from the branch-target check alone,
  `main`'s segment by `mainSeg2LStmt_of`
  (`Spike/Lib/LowerX64/G1MainSegLStmt.lean`).
-/
import Spike.Lib.LowerX64.G1Closed2H
import Spike.Lib.LowerX64.G1MainCallL
import Spike.Lib.LowerX64.G1NoSetup
import Spike.Lib.LowerX64.G1MainSegLStmt

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **The bare start's segment obligations** (`h0NoneW`; `H0NoneStmtW` is
`H0NoSetupStmt`). -/
theorem h0NoSetupStmt : H0NoSetupStmt := h0NoneW

/-- **`Closed2Stmt` at the configurations with the header bound**
(`Scc.Obj.nShift cfg.layout.obj < 22`, the configuration premise of the
x86-64 theorem). -/
def Closed2StmtH : Prop :=
  ∀ (cfg : Scc.Config), Scc.Obj.nShift cfg.layout.obj < 22 →
  ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : CoreTerm.Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true →
    ∀ {text : String}, Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs = true →
    ∀ {B : Scc.Sem.Budget}, B.cells = Scc.Cert.PlaceOK.allocCells → ∀ {arch : WeakMem.Arch},
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B ⟨text, sizes, labelOffs⟩

/-- **The x86-64 compiler theorem from two statements**: the
branch-target check (`HTg`), `main`'s segment at every reachable placement
(`HM : MainSeg2LStmt`, giving `main`'s segment at the start by
`mainSeg2Stmt_ofL`, `main`'s call after the setup block by
`huSetupStmt_of`, and the landings by `h1SetupStmt_ofMainSeg2L`); the bare
start is `h0NoSetupStmt`. -/
theorem closed2Stmt_x64 (HTg : TgOkBStmt) (HM : MainSeg2LStmt) :
    Closed2StmtH :=
  fun cfg hobj => closed2Stmt_at fnSpecC2Stmt HTg (mainSeg2Stmt_ofL HM)
    (huSetupStmt_of (mainSeg2Stmt_ofL HM)) (h1SetupStmt_ofMainSeg2L HM) h0NoSetupStmt cfg hobj

/-- **The x86-64 compiler theorem from the branch-target check**:
`closed2Stmt_x64` at `main`'s segment `mainSeg2LStmt_of`. -/
theorem closed2Stmt_x64_tg (HTg : TgOkBStmt) : Closed2StmtH :=
  closed2Stmt_x64 HTg mainSeg2LStmt_of

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.closed2Stmt_x64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.closed2Stmt_x64

/-- info: 'Spike.Lib.LowerX64.h0NoSetupStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.h0NoSetupStmt

/-- info: 'Spike.Lib.LowerX64.closed2Stmt_x64_tg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.closed2Stmt_x64_tg
