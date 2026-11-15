/-
**The bare start's stack bounds and `main`'s call: the statements**
(AArch64): for an `Accepted2` program without a setup block, `scc_rt_main`
is `bareMC` (the output's `.bare` tail) and calls `main` directly.

- `Bounds0A`: the switch depth `L`, `main`'s callee room `D` and `main`'s
  row (label `lM`, frame `fM`, need `nM`), the twin of `Bounds2A`
  (`Spike/Lib/LowerA64/H0InAssembledBA.lean`) without the setup block's
  row, at `bareMC`'s frame;
- `StackBounds0Stmt`: some `Bounds0A` at every such program passing the
  placement check at a configuration with `CfgNeedOkA` (the twin of
  `stackBounds2A`);
- `HU0A`: `main`'s call `UserCallWSF` (`Spike/Lib/LowerA64/G1NoSetupRt.lean`)
  at every choice of the bounds, at the switch region's frame condition with
  `WordsNone`, the post `UPostRF ∧ MainCtlV`, the return address
  `bareMC.e0 + 4`, the ghost control the program's start control;
- `MainCall0Stmt`: `HU0A` from `main`'s segment `MainSeg2`
  (`Spike/Lib/LowerA64/G1MainStmt.lean`) at every frame invariant.
-/
import Spike.Lib.LowerA64.G1NoSetupRt
import Spike.Lib.LowerA64.G1NoSetupStmt
import Spike.Lib.LowerA64.HeldPostAV

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (bareMC UserCallWSF swFSL rS0 rtF)
open Spike.Lib.AllocReach (Reach IN)

/-- **The bounds of the bare start** (AArch64): `main`'s row of the stack
need table (label `lM`, frame `fM`, need `nM`) with `main`'s callee room
`D` covering the need, the stack check's `48` and the deepest runtime
routine's `208`; the frame of every stack-checked IR function named
`main` its row's; a switch depth `L` holding `bareMC`'s frame and `D`; the
limit's room below `bareMC`'s frame and below it and `main`'s frame at the
first stack's top (layout `Lr`); `bareMC`'s frame inside the switch
region. -/
def Bounds0A (cfg : Scc.Config) (p : Prog) (Lr : Spike.Lib.A64.Rt.RuntimeLayout) (L D : Int) (lM : String)
    (fM nM : Nat) : Prop :=
  Scc.Cert.NeedA64.row? (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
      (Scc.Lower.Names.user "main") = some (lM, fM, nM) ∧ fM ≤ nM ∧ (nM : Int) + 48 ≤ D ∧
      (nM : Int) + 48 + 208 ≤ D ∧
    (∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "main" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fM) ∧
    0 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧ 0 ≤ D ∧ D % 8 = 0 ∧
    bareMC.Z.toInt + D ≤ L ∧
    Lr.stacksA.toNat + 4096 ≤ (stacksA Lr.lab + 0#64 + 16384#64 - bareMC.Z.toBitVec).toNat ∧
    Lr.stacksA.toNat + 4096 ≤ (stacksA Lr.lab + 0#64 + 16384#64 - bareMC.Z.toBitVec -
      (Int64.ofInt (fM : Int)).toBitVec).toNat ∧
    (swR (stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).Off (-bareMC.Z.toInt)

/-- **The bare start's bounds exist** (the twin of `stackBounds2A` without
a setup block): at every `Accepted2` program without a setup block whose
output passes the placement check at a configuration with `CfgNeedOkA`,
at any runtime layout `Lr`. -/
def StackBounds0Stmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout),
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true →
    Scc.Lower.Accepted2 p = true → Scc.Lower.setupOf p = none → CfgNeedOkA pcfg = true →
    ∀ Lr : Spike.Lib.A64.Rt.RuntimeLayout, ∃ (L D : Int) (lM : String) (fM nM : Nat), Bounds0A cfg p Lr L D lM fM nM

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The start's frame condition (`Closed2AtWA`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSA` at `WNF`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region's frame condition below the top `v`, with `WordsNone`. -/
local notation "FWS" v:max => fun m =>
  Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m

/-- **`main`'s call at the bare start, at every choice of the bounds**
(`Bounds0A`): `UserCallWSF` at the switch region's frame condition with
`WordsNone`, `main`'s label, `bareMC`'s frame, the room `D`, `main`'s frame
`fM` as the limit room, the post `UPostRF ∧ MainCtlV`, the return address
`bareMC.e0 + 4`, the ghost control the program's start control `C0` and
the first TCB. -/
def HU0A (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (Dt : State → Prop) : Prop :=
  ∀ (L D : Int) (lM : String) (fM nM : Nat), Bounds0A cfg p (Ly) L D lM fM nM →
    ∀ J : InvS, StJ J → ∀ v, UserCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FWS v)
      bareMC.fn bareMC.Z D (Int64.ofInt (fM : Int))
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab bareMC.e0 + 4).toBitVec C0 (TP0)

end Assembled

/-- **`main`'s call at the bare start from `main`'s segment**: at every
`Accepted2` program without a setup block, with `mainRetOk`, whose output
passes the placement check at `lay2 Λ p` at a configuration with
`CfgNeedOkA`, every entry state, landings' states and write tail, `HU0A`
from `MainSeg2` at every frame invariant. -/
def MainCall0Stmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (Λ : Scc.Sem.Layout)
    (hp : Scc.Lower.Accepted2 p = true),
    Scc.Lower.mainRetOk p = true → CfgNeedOkA pcfg = true → Scc.Lower.setupOf p = none →
    ∀ (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
      (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (Dt : State → Prop),
    (∀ J : InvS, MainSeg2 h hp Dt J) → HU0A h E El Dt

end Spike.Lib.LowerA64
