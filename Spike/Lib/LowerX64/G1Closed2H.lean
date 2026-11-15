/-
**The segment obligations of the `Accepted2` theorem with the function
segment, `main`'s call after the setup block and the landings proved**
(x86-64): `closed2InW_at` and `closed2Stmt_at`
(`Spike/Lib/LowerX64/G1Closed2.lean`) at the function segment
`fnSpecC2Stmt` (`Spike/Lib/LowerX64/G1FnSpecStmtOf.lean`), `main`'s call
after the setup block from `main`'s segment (`huSetupStmt_of`, by
`hUBVF_of_mainSeg2`, `Spike/Lib/LowerX64/G1MainCall.lean`) and the
landings `h1SetupStmt_of` (`Spike/Lib/LowerX64/G1H1.lean`), whose own
premise is `main`'s call at every reachable placement (`MainLUAllStmt`).

- `MainLUAllStmt`: `MainLUStmt` at every instance with a setup block;
- `huSetupStmt_of`: `HUSetupStmt` from `MainSeg2Stmt`;
- `closed2InW_atH`, `closed2Stmt_atH`: `Closed2InW` and `Closed2Stmt` at a
  configuration with `hobj`, from the branch-target check, `main`'s segment
  (`MainSeg2Stmt`), `MainLUAllStmt` and the bare start (`H0NoSetupStmt`).
-/
import Spike.Lib.LowerX64.G1Closed2
import Spike.Lib.LowerX64.G1FnSpecStmtOf
import Spike.Lib.LowerX64.G1H1
import Spike.Lib.LowerX64.G1MainCall

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **`main`'s call at every reachable placement at every instance with a
setup block** (`MainLUStmt`, the premise of `h1SetupStmt_of`). -/
def MainLUAllStmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    ∀ ty : Ty, Scc.Lower.setupOf p = some ty →
    ∀ h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    MainLUStmt h ty

/-- **`main`'s call after the setup block from `main`'s segment**
(`hUBVF_of_mainSeg2` at each instance, `MainSeg2Stmt` at the write tail
`fun _ => True`). -/
theorem huSetupStmt_of (HM : MainSeg2Stmt) : HUSetupStmt := by
  intro cfg pcfg p sizes labelOffs Λ hp ty hty hR hcfg E _hE h htg
  exact hUBVF_of_mainSeg2 h hp hty hR hcfg E _ (HM cfg pcfg p sizes labelOffs Λ hp hcfg h htg)

/-- **`Closed2InW` at a configuration with the header bound, the function
segment, `main`'s call after the setup block and the landings proved**
(`closed2InW_at` at `fnSpecC2Stmt`, `huSetupStmt_of` and `h1SetupStmt_of`). -/
theorem closed2InW_atH (HTg : TgOkBStmt) (HM : MainSeg2Stmt) (HML : MainLUAllStmt) (H0 : H0NoSetupStmt)
    (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) :
    ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat) (labelOffs : List (String × Nat))
    (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true → ∀ (E : Entry), E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    In2XW h' E :=
  closed2InW_at fnSpecC2Stmt HTg HM (huSetupStmt_of HM) (h1SetupStmt_of HML) H0 cfg hobj

/-- **`Closed2Stmt` at a configuration with the header bound, the function
segment, `main`'s call after the setup block and the landings proved**
(`closed2Stmt_at` at `fnSpecC2Stmt`, `huSetupStmt_of` and `h1SetupStmt_of`). -/
theorem closed2Stmt_atH (HTg : TgOkBStmt) (HM : MainSeg2Stmt) (HML : MainLUAllStmt) (H0 : H0NoSetupStmt)
    (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) :
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
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B ⟨text, sizes, labelOffs⟩ :=
  closed2Stmt_at fnSpecC2Stmt HTg HM (huSetupStmt_of HM) (h1SetupStmt_of HML) H0 cfg hobj

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.huSetupStmt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.huSetupStmt_of

/-- info: 'Spike.Lib.LowerX64.closed2InW_atH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.closed2InW_atH

/-- info: 'Spike.Lib.LowerX64.closed2Stmt_atH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.closed2Stmt_atH
