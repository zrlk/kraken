/-
**The segment obligations of the `Accepted2` theorem from the generic
producers** (x86-64; the twin of `Spike/Lib/LowerA64/G1Closed2.lean`):
`Closed2InW` (`Spike/Lib/LowerX64/Closed2AtW.lean`), hence `Closed2Stmt`,
at every configuration whose object layout's header scalar count starts
below bit 22 (`hobj`), from the program-wide function segment
`FnSpecC2Stmt` (`Spike/Lib/LowerX64/G1FnSpec.lean`) and the open
statements named here, by cases on the setup block.

With a setup block (`setupOf p = some ty`), `in2XW_ofBVBF`
(`Spike/Test/X64Hello1ClosedBVBF.lean`) at the landings `ElG` and the
write tail `fun _ => True`:

- the setup call `HSBVF` by `hSBVF_of_accepted2H`
  (`Spike/Lib/LowerX64/G1SetupOpen.lean`): the function segment from
  `FnSpecC2Stmt`, the room from the placement check (`room2Own`), the
  header bound `hobj` and the branch-target check (`TgOkBStmt`);
- `main`'s call `HUBVF` (`HUSetupStmt`; on AArch64 `hUBVFA_of_mainSeg2`
  from `main`'s segment `MainSeg2Stmt`, whose x86-64 twin is not yet
  here);
- the landings' segments `H1InW` at `ElG` (`H1SetupStmt`).

Without one, the bare start's `In2XW` (`H0NoSetupStmt`, the shape of the
no-setup statement).

- `TgOkBStmt`, `HUSetupStmt`, `H1SetupStmt`, `H0NoSetupStmt`: the open
  statements;
- `in2XW_of_setupG1`: `In2XW` at one instance with a setup block;
- `closed2InW_at`, `closed2Stmt_at`: `Closed2InW` and `Closed2Stmt` at a
  configuration with `hobj`, from `FnSpecC2Stmt`, `MainSeg2Stmt`
  (`Spike/Lib/LowerX64/G1MainStmt.lean`) and the open statements.
-/
import Spike.Lib.LowerX64.G1SetupOpen
import Spike.Lib.LowerX64.G1MainStmt
import Spike.Lib.LowerX64.G1Room2
import Spike.Lib.LowerX64.Closed2AtW
import Spike.Test.X64Hello1ClosedBVBF

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

/-- **The branch-target check passes on every `Accepted2` program's
output** (`tgOkB`, the premise of `FnSpecC2Stmt` and of the construct
blocks' targets), at every assembled size and label offset table. -/
def TgOkBStmt : Prop :=
  ∀ (cfg : Scc.Config) (p : Prog) (sizes : List Nat) (labelOffs : List (String × Nat)),
    Scc.Lower.Accepted2 p = true →
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true

/-- **`main`'s call after the setup block at every instance with a setup
block** (`HUBVF` at the landings `ElG` and the write tail `fun _ => True`),
at the configuration's need check and the branch-target check. -/
def HUSetupStmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted2 p = true) (ty : Ty),
    Scc.Lower.setupOf p = some ty → Scc.Lower.mainRetOk p = true → CfgNeedOk pcfg = true →
    ∀ E : Entry, E.Ok (lay2 Λ p) →
    ∀ h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true →
    HUBVF h ty E (ElG h hp) (fun _ => True)

/-- **The landings' segments with a setup block** (`H1InW` at the
landings `ElG` and the write tail `fun _ => True`), at every instance of
`Closed2InW` with a setup block, the header bound and the branch-target
check. -/
def H1SetupStmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted2 p = true) (ty : Ty),
    Scc.Lower.setupOf p = some ty → Scc.Lower.mainRetOk p = true → CfgNeedOk pcfg = true →
    Scc.Obj.nShift cfg.layout.obj < 22 →
    ∀ E : Entry, E.Ok (lay2 Λ p) →
    ∀ h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true →
    H1InW h E (ElG h hp) (fun _ => True)

/-- **The bare start's segment obligations** (`In2XW` at every instance of
`Closed2InW` without a setup block), given the branch-target check, the
function segment and `main`'s segment (`MainSeg2`) at the write tail
`fun _ => True`. -/
def H0NoSetupStmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted2 p = true),
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true → Scc.Lower.setupOf p = none → ∀ E : Entry, E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true →
    (∀ J Bot, FnSpecC2At h' hp (fun _ => True) J Bot) → (∀ J : InvS, MainSeg2 h' hp (fun _ => True) J) →
    In2XW h' E

section Inst

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

/-- **`In2XW` at one instance with a setup block** (`in2XW_ofBVBF` at the
landings `ElG` and the write tail `fun _ => True`): the landings'
segments `H1`, the setup call by `hSBVF_of_accepted2H` (the function
segment `HF`, the room `room2Own`, the header `hobj`, the branch-target
check `htg`), `main`'s call `HU`. -/
theorem in2XW_of_setupG1 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true) {E : Entry} (hE : E.Ok (lay2 Λ p))
    (htg : tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22)
    (HF : ∀ J Bot, FnSpecC2At h hp (fun _ => True) J Bot) (HU : HUBVF h ty E (ElG h hp) (fun _ => True))
    (H1 : H1InW h E (ElG h hp) (fun _ => True)) : In2XW h E :=
  in2XW_ofBVBF h hp hty hcfg hE ⟨ElG h hp, fun _ => True, H1,
    hSBVF_of_accepted2H h hp hty hobj hcfg htg (room2Own h hp) E HF, HU⟩

end Inst

/-- **`Closed2InW` at a configuration from the generic producers'
statements** (`Closed2InW`'s body at `cfg`, whose object layout's header
scalar count starts below bit 22, `hobj`): at each instance, the function
segment from `FnSpecC2Stmt` (the write tail `fun _ => True`), the
branch-target check from `TgOkBStmt`, `main`'s segment from
`MainSeg2Stmt`; with a setup block
`in2XW_of_setupG1` (`main`'s call from `HUSetupStmt`, the landings from
`H1SetupStmt`), without one `H0NoSetupStmt` (given `main`'s segment). The header bound `hobj` is a
premise on the configuration: the placement check pins the header's shift,
so a layout without it fails `placeOKAt`. -/
theorem closed2InW_at (HFS : FnSpecC2Stmt) (HTg : TgOkBStmt) (HM : MainSeg2Stmt) (HU : HUSetupStmt)
    (H1 : H1SetupStmt) (H0 : H0NoSetupStmt) (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) :
    ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat) (labelOffs : List (String × Nat))
    (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true → ∀ (E : Entry), E.Ok (lay2 Λ p) →
    ∀ h' : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
    In2XW h' E := by
  intro pcfg p sizes labelOffs Λ hp hR h hcfg E hE h'
  have htg := HTg cfg p sizes labelOffs hp
  have HF : ∀ J Bot, FnSpecC2At h' hp (fun _ => True) J Bot :=
    HFS cfg pcfg p sizes labelOffs Λ hp hcfg h' htg (fun _ => True) fun _ _ _ _ _ _ _ _ _ => trivial
  have HMJ := HM cfg pcfg p sizes labelOffs Λ hp hcfg h' htg
  cases hs : Scc.Lower.setupOf p with
  | none => exact H0 cfg pcfg p sizes labelOffs Λ hp hR h hcfg hs E hE h' htg HF HMJ
  | some ty =>
    exact in2XW_of_setupG1 h' hp hs hcfg hE htg hobj HF
      (HU cfg pcfg p sizes labelOffs Λ hp ty hs hR hcfg E hE h' htg)
      (H1 cfg pcfg p sizes labelOffs Λ hp ty hs hR hcfg hobj E hE h' htg)

/-- **`Closed2Stmt` at a configuration with the header bound from the
generic producers' statements** (`Closed2Stmt`'s body at `cfg`;
`x64_scc_correctE_text_closedAt2_atW` at `closed2InW_at`; see its
docstring for the premises). -/
theorem closed2Stmt_at (HFS : FnSpecC2Stmt) (HTg : TgOkBStmt) (HM : MainSeg2Stmt) (HU : HUSetupStmt)
    (H1 : H1SetupStmt) (H0 : H0NoSetupStmt) (cfg : Scc.Config) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) :
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
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B ⟨text, sizes, labelOffs⟩ := by
  intro pcfg p sizes labelOffs Λ hp hR h hcfg text hpa B hB arch
  exact x64_scc_correctE_text_closedAt2_atW hp hR h hcfg
    (closed2InW_at HFS HTg HM HU H1 H0 cfg hobj pcfg p sizes labelOffs Λ hp hR h hcfg) hpa hB

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.in2XW_of_setupG1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.in2XW_of_setupG1

/-- info: 'Spike.Lib.LowerX64.closed2InW_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.closed2InW_at

/-- info: 'Spike.Lib.LowerX64.closed2Stmt_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.closed2Stmt_at
