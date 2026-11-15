/-
**The `Accepted2` theorem's segment obligations, unconditionally**
(AArch64): `Closed2InAW` (`Spike/Lib/LowerA64/Closed2AtWA.lean`) and
`Closed2StmtA` at every configuration whose object layout's header scalar
count starts below bit 22 (`hobj`), with every producer statement of
`Spike/Lib/LowerA64/G1Closed2.lean` discharged:

- the branch-target check by `tgOkB_accepted2`
  (`Spike/Lib/LowerA64/G1TgOk.lean`);
- the function segment at the start's placement by `fnSpecC2Stmt`
  (`Spike/Lib/LowerA64/G1FnSpecStmt.lean`) and at every reachable placement
  by `fnSpecC2StmtL` (`Spike/Lib/LowerA64/G1FnSpecStmtLOf.lean`);
- `main`'s segment at every reachable placement by `mainSeg2L_of`
  (`Spike/Lib/LowerA64/G1MainSegL.lean`), at the start's placement its
  corollary `mainSeg2_ofL`;
- with a setup block, the landings' segments by `h1InAW_ofSetupL`
  (`Spike/Lib/LowerA64/G1H1.lean`) at `main`'s calls from the landings
  (`mainLU_ofMainSeg2L`, `Spike/Lib/LowerA64/G1MainCallL.lean`), the setup
  and `main` calls by `in2AW_of_setupG1`;
- without one, the bare start by `h0NoneW`
  (`Spike/Lib/LowerA64/G1NoSetup.lean`).

The write tail is `fun _ => True` throughout, so its obligations at the
output call's and the abort stubs' system calls hold trivially.

- `mainSeg2L_true`: `MainSeg2L` at the write tail `fun _ => True`;
- `closed2InAW_g1`, `closed2StmtA_g1`: `Closed2InAW`'s and
  `Closed2StmtA`'s bodies at a configuration with `hobj`.
-/
import Spike.Lib.LowerA64.G1Closed2
import Spike.Lib.LowerA64.G1MainSegL
import Spike.Lib.LowerA64.G1MainCallL
import Spike.Lib.LowerA64.G1FnSpecStmt
import Spike.Lib.LowerA64.G1H1
import Spike.Lib.LowerA64.G1NoSetup
import Spike.Lib.LowerA64.G1TgOk

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

/-- **`main`'s segment at every reachable placement at the trivial write
tail** (`mainSeg2L_of` at `fun _ => True`, the function segment from
`fnSpecC2StmtL`). -/
theorem mainSeg2L_true {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
    (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (hp : Scc.Lower.Accepted2 p = true) (hcfg : CfgNeedOkA pcfg = true)
    (htg : tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true)
    (J : InvS) : MainSeg2L h hp (fun _ => True) J :=
  mainSeg2L_of h hp htg (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) J
    (fnSpecC2StmtL cfg pcfg p Λ hp hcfg h htg _ (fun _ _ _ _ _ _ _ _ => trivial) J _)

/-- **`Closed2InAW` at a configuration with the header bound**
(`Closed2InAW`'s body at `cfg`; see the module docstring): every producer
statement discharged, by cases on the setup block. -/
theorem closed2InAW_g1 (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) :
    ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout),
    Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true →
    CfgNeedOkA pcfg = true → ∀ (E : Entry), E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true,
    In2AW h' E := by
  intro pcfg p Λ hp hR h hcfg E hE h'
  have htg := tgOkB_accepted2 cfg p hp
  have HF : ∀ J Bot, FnSpecC2At h' hp (fun _ => True) J Bot :=
    fnSpecC2Stmt cfg pcfg p Λ hp hcfg h' htg (fun _ => True) fun _ _ _ _ _ _ _ _ => trivial
  have HML : ∀ J, MainSeg2L h' hp (fun _ => True) J := mainSeg2L_true h' hp hcfg htg
  have HM : ∀ J, MainSeg2 h' hp (fun _ => True) J := fun J => mainSeg2_ofL h' (HML J)
  cases hs : Scc.Lower.setupOf p with
  | none => exact h0NoneW cfg pcfg p Λ hp hR h hcfg hs E hE h' htg HF HM
  | some ty =>
    exact in2AW_of_setupG1 h' hp hs hR hcfg hE htg hobj HF HM
      (h1InAW_ofSetupL h' hp hs hcfg hobj htg (mainLU_ofMainSeg2L h' hp hs hR hcfg HML) E)

/-- **`Closed2StmtA` at a configuration with the header bound**
(`Closed2StmtA`'s body at `cfg`, `a64_scc_correctE_text_closedAt2_atW` at
`closed2InAW_g1`): every `Accepted2` program returning by `mainRetOk`,
placed by the placement check under a configuration passing the need
check, assembles to text whose runs refine the source. -/
theorem closed2StmtA_g1 (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) :
    ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : CoreTerm.Prog) (Λ : Scc.Sem.Layout),
    Scc.Lower.Accepted2 p = true → Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true →
    CfgNeedOkA pcfg = true →
    ∀ {asm : String}, Scc.Cert.Link.A64.parsesTo asm
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs = true →
    ∀ {B : Scc.Sem.Budget}, B.cells = Scc.Cert.PlaceOK.allocCells → ∀ {arch : WeakMem.Arch},
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B asm := by
  intro pcfg p Λ hp hR h hcfg asm hpa B hB arch
  exact a64_scc_correctE_text_closedAt2_atW hp hR h hcfg (closed2InAW_g1 cfg hobj pcfg p Λ hp hR h hcfg) hpa hB

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.mainSeg2L_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainSeg2L_true

/-- info: 'Spike.Lib.LowerA64.closed2InAW_g1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.closed2InAW_g1

/-- info: 'Spike.Lib.LowerA64.closed2StmtA_g1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.closed2StmtA_g1
