/-
**The segment obligations of the `Accepted2` theorem from the generic
producers** (AArch64): `Closed2InAW` (`Spike/Lib/LowerA64/Closed2AtWA.lean`),
hence `Closed2StmtA`, at every configuration whose object layout's header
scalar count starts below bit 22 (`hobj`), from the program-wide function
segment `FnSpecC2Stmt` (`Spike/Lib/LowerA64/G1FnSpec.lean`) and the open
statements named here, by cases on the setup block.

With a setup block (`setupOf p = some ty`), `in2AW_ofBVBF`
(`Spike/Test/A64Hello1ClosedBVBF.lean`) at the landings `ElH` and the write
tail `fun _ => True`:

- the setup call `HSBVFA` by `hSBVFA_of_accepted2H`
  (`Spike/Lib/LowerA64/G1SetupOpen.lean`): the function segment from
  `FnSpecC2Stmt`, the room from the placement check (`room2Own`), the
  header bound `hobj` and the branch-target check
  (`TgOkBStmt`);
- `main`'s call `HUBVFA` by `hUBVFA_of_mainSeg2`
  (`Spike/Lib/LowerA64/G1MainCall.lean`) from `main`'s segment
  (`MainSeg2Stmt`);
- the landings' segments `H1InAW` at `ElH` (`H1SetupStmt`).

Without one, the bare start's `In2AW` (the premise `H0`, the shape of the
no-setup statement).

- `TgOkBStmt`, `MainSeg2Stmt`, `H1SetupStmt`: the open statements;
- `in2AW_of_setupG1`: `In2AW` at one instance with a setup block;
- `closed2InAW_at`, `closed2StmtA_at`: `Closed2InAW` and `Closed2StmtA`
  at a configuration with `hobj`, from `FnSpecC2Stmt`, the open statements
  and `H0`.
-/
import Spike.Lib.LowerA64.G1MainCall
import Spike.Lib.LowerA64.G1SetupOpen
import Spike.Lib.LowerA64.G1Room2
import Spike.Lib.LowerA64.Closed2StmtA
import Spike.Test.A64Hello1ClosedBVBF

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

/-- **The branch-target check passes on every `Accepted2` program's
output** (`tgOkB`, the premise of `FnSpecC2Stmt` and of the construct
blocks' targets). -/
def TgOkBStmt : Prop :=
  ∀ (cfg : Scc.Config) (p : Prog), Scc.Lower.Accepted2 p = true →
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true

/-- **`main`'s segment at every instance** (`MainSeg2` at the write tail
`fun _ => True` and every invariant), at the placement check, the
configuration's need check and the branch-target check. -/
def MainSeg2Stmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout)
    (hp : Scc.Lower.Accepted2 p = true), CfgNeedOkA pcfg = true →
    ∀ h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true,
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true →
    ∀ J : InvS, MainSeg2 h hp (fun _ => True) J

/-- **The landings' segments with a setup block** (`H1InAW` at the
landings `ElH` and the write tail `fun _ => True`), at every instance of
`Closed2InAW` with a setup block and the branch-target check. -/
def H1SetupStmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout)
    (hp : Scc.Lower.Accepted2 p = true) (ty : Ty), Scc.Lower.setupOf p = some ty →
    Scc.Lower.mainRetOk p = true → CfgNeedOkA pcfg = true → ∀ E : Entry, E.Ok (lay2 Λ p) →
    ∀ h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true,
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true →
    H1InAW h E (ElH h hp) (fun _ => True)

section Inst

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

/-- **`In2AW` at one instance with a setup block** (`in2AW_ofBVBF` at the
landings `ElH` and the write tail `fun _ => True`): the landings'
segments `H1`, the setup call by `hSBVFA_of_accepted2H` (the function
segment `HF`, the room `room2Own`, the header `hobj`, the branch-target
check `htg`), `main`'s call by `hUBVFA_of_mainSeg2` (`main`'s segment
`HM`). -/
theorem in2AW_of_setupG1 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hR : Scc.Lower.mainRetOk p = true) (hcfg : CfgNeedOkA pcfg = true) {E : Entry} (hE : E.Ok (lay2 Λ p))
    (htg : tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22)
    (HF : ∀ J Bot, FnSpecC2At h hp (fun _ => True) J Bot) (HM : ∀ J, MainSeg2 h hp (fun _ => True) J)
    (H1 : H1InAW h E (ElH h hp) (fun _ => True)) : In2AW h E :=
  in2AW_ofBVBF h hp hty hcfg hE ⟨ElH h hp, fun _ => True, H1,
    hSBVFA_of_accepted2H h hp hty hobj hcfg htg (room2Own h hp) E HF,
    hUBVFA_of_mainSeg2 h hp hty hR hcfg E _ HM⟩

end Inst

/-- **`Closed2InAW` at a configuration from the generic producers'
statements** (`Closed2InAW`'s body at `cfg`, whose object layout's header
scalar count starts below bit 22, `hobj`): at each instance, the function
segment from `FnSpecC2Stmt` (the write tail `fun _ => True`), `main`'s
segment from `MainSeg2Stmt`, the branch-target check from `TgOkBStmt`; with
a setup block `in2AW_of_setupG1` (the landings from `H1SetupStmt`), without
one the bare start's `In2AW` `H0`.

So `Closed2StmtA` at every configuration with `hobj` (`closed2StmtA_at`)
holds conditional only on the function segment `FnSpecC2Stmt` (the
statement of the generic function segment, whose own premises are the call
and step statements of `Spike/Lib/LowerA64/G1FnSpec.lean`), `main`'s
segment `MainSeg2Stmt`, the landings' segments `H1SetupStmt`, the
branch-target check `TgOkBStmt` and the bare start `H0`. The header bound
`hobj` is a premise on the configuration: the placement check pins the
header's shift, so a layout without it fails `placeOKAt`. -/
theorem closed2InAW_at (HFS : FnSpecC2Stmt) (HTg : TgOkBStmt) (HM : MainSeg2Stmt) (H1 : H1SetupStmt)
    (H0 : ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout)
      (hp : Scc.Lower.Accepted2 p = true), Scc.Lower.mainRetOk p = true →
      placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true → CfgNeedOkA pcfg = true →
      Scc.Lower.setupOf p = none → ∀ (E : Entry), E.Ok (lay2 Λ p) →
      ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true,
      tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true →
      (∀ J Bot, FnSpecC2At h' hp (fun _ => True) J Bot) → (∀ J, MainSeg2 h' hp (fun _ => True) J) →
      In2AW h' E) (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) :
    ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout),
    Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true →
    CfgNeedOkA pcfg = true → ∀ (E : Entry), E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true,
    In2AW h' E := by
  intro pcfg p Λ hp hR h hcfg E hE h'
  have htg := HTg cfg p hp
  have HF : ∀ J Bot, FnSpecC2At h' hp (fun _ => True) J Bot :=
    HFS cfg pcfg p Λ hp hcfg h' htg (fun _ => True) fun _ _ _ _ _ _ _ _ => trivial
  have HMJ := HM cfg pcfg p Λ hp hcfg h' htg
  cases hs : Scc.Lower.setupOf p with
  | none => exact H0 cfg pcfg p Λ hp hR h hcfg hs E hE h' htg HF HMJ
  | some ty =>
    exact in2AW_of_setupG1 h' hp hs hR hcfg hE htg hobj HF HMJ (H1 cfg pcfg p Λ hp ty hs hR hcfg E hE h' htg)

/-- **`Closed2StmtA` at a configuration with the header bound from the
generic producers' statements** (`Closed2StmtA`'s body at `cfg`;
`a64_scc_correctE_text_closedAt2_atW` at `closed2InAW_at`; see its
docstring for the premises). -/
theorem closed2StmtA_at (HFS : FnSpecC2Stmt) (HTg : TgOkBStmt) (HM : MainSeg2Stmt) (H1 : H1SetupStmt)
    (H0 : ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout)
      (hp : Scc.Lower.Accepted2 p = true), Scc.Lower.mainRetOk p = true →
      placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true → CfgNeedOkA pcfg = true →
      Scc.Lower.setupOf p = none → ∀ (E : Entry), E.Ok (lay2 Λ p) →
      ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true,
      tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))) = true →
      (∀ J Bot, FnSpecC2At h' hp (fun _ => True) J Bot) → (∀ J, MainSeg2 h' hp (fun _ => True) J) →
      In2AW h' E) (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) :
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
  exact a64_scc_correctE_text_closedAt2_atW hp hR h hcfg (closed2InAW_at HFS HTg HM H1 H0 cfg hobj pcfg p Λ hp hR h hcfg)
    hpa hB

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.in2AW_of_setupG1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.in2AW_of_setupG1

/-- info: 'Spike.Lib.LowerA64.closed2InAW_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.closed2InAW_at

/-- info: 'Spike.Lib.LowerA64.closed2StmtA_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.closed2StmtA_at
