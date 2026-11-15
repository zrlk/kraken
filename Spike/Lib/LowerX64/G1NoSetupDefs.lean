/-
**The bare start's stack bounds and `main`'s call: the statements**
(x86-64): for an `Accepted2` program without a setup block, `scc_rt_main`
is `bareMC` (the output's `.bare` tail) and calls `main` directly. The twin
of `Spike/Lib/LowerA64/G1NoSetupDefs.lean`.

- `Bounds0X`: the switch depth `L`, `main`'s callee room `D` and `main`'s
  row (label `lM`, frame size `fM`, need `nM`), the twin of `Bounds2`
  (`Spike/Lib/LowerX64/H0InAssembledB.lean`) without the setup block's
  row, at `bareMC`'s frame (`stackBounds0`'s conclusion);
- `StackBounds0Stmt`: some `Bounds0X` at every such program passing the
  placement check at a configuration with `CfgNeedOk`;
- `HU0X`: `main`'s call `UserCallWSF` (`Spike/Lib/LowerX64/G1NoSetupRt.lean`)
  at every choice of the bounds, in `scc_rt_main`'s callee region of the
  switch region under `(WordsNone ∧ swFSL) ∧ CallerCells`, the post
  `UPostRF ∧ MainCtlV`, the return address `bareMC.sp0`, the ghost control
  the program's start control;
- `MainCall0Stmt`: `HU0X` from `main`'s segment `MainSeg2`
  (`Spike/Lib/LowerX64/G1MainStmt.lean`) at every frame invariant.
-/
import Spike.Lib.LowerX64.G1NoSetupRt
import Spike.Lib.LowerX64.G1NoSetupBounds
import Spike.Lib.LowerX64.H0InAssembledBVBF
import Spike.Lib.LowerX64.G1NoSetupStmt

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open A9NoSpawn Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.X64.Rt (bareMC UserCallWSF swFSL rS0 rtF)

/-- **The bounds of the bare start** (x86-64): `main`'s row of the stack
need table (label `lM`, frame size `fM` with the saved `%rbp`'s `8`, need
`nM`) with `main`'s callee room `D` covering the need and `48`, the
deepest runtime routine's `208`, and the frame and `48`; the frame size of
every stack-checked IR function named `main` its row's; a switch depth `L`
holding `scc_rt_main`'s call, `bareMC`'s frame, `main`'s call and `D`; the
limit's room below `bareMC`'s frame and below it and `main`'s frame at the
first stack's top (layout `Lr`); `%rdi`'s spill slot `-16` inside
`scc_rt_main`'s callee region. -/
def Bounds0X (cfg : Scc.Config) (p : Prog) (sizes : List Nat) (labelOffs : List (String × Nat))
    (Lr : Spike.Lib.X64.Rt.RuntimeLayout) (L D : Int) (lM : String) (fM nM : Nat) : Prop :=
  Scc.Cert.NeedX64.row? (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user "main") = some (lM, fM + 8, nM) ∧ fM + 8 ≤ nM ∧ (nM : Int) + 48 ≤ D ∧
      (nM : Int) + 48 + 208 ≤ D ∧ (fM : Int) + 48 ≤ D ∧
    (∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "main" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fM) ∧
    8 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧ 0 ≤ D ∧ D % 8 = 0 ∧
    8 + 8 + bareMC.Z.toInt + 8 + D ≤ L ∧
    Lr.stacksA.toNat + 4096 ≤ (stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 - bareMC.Z.toBitVec).toNat ∧
    Lr.stacksA.toNat + 4096 ≤ (stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 - bareMC.Z.toBitVec -
      8#64 - 8#64 - (Int64.ofInt (fM : Int)).toBitVec).toNat ∧
    ((swR (stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).Off (-16)

/-- **The bare start's bounds exist** (the twin of `stackBounds2` without
a setup block): at every `Accepted2` program without a setup block whose
output passes the placement check at a configuration with `CfgNeedOk`, at
any runtime layout `Lr`. -/
def StackBounds0Stmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout),
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    Scc.Lower.Accepted2 p = true → Scc.Lower.setupOf p = none → CfgNeedOk pcfg = true →
    ∀ Lr : Spike.Lib.X64.Rt.RuntimeLayout, ∃ (L D : Int) (lM : String) (fM nM : Nat),
      Bounds0X cfg p sizes labelOffs Lr L D lM fM nM

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt
  (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The start's frame condition (`Closed2AtW`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX` at `WNF`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- `scc_rt_main`'s callee region of the switch region at depth `L`, below
the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top
`v`, the caller's cells outside `RS v`. -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
  CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

/-- **`main`'s call at the bare start, at every choice of the bounds**
(`Bounds0X`): `UserCallWSF` in `scc_rt_main`'s callee region of the switch
region under `(WordsNone ∧ swFSL) ∧ CallerCells`, `main`'s label,
`bareMC`'s frame, the room `D`, `main`'s frame `fM` as the limit room, the
post `UPostRF ∧ MainCtlV`, the return address `bareMC.sp0`, the ghost
control the program's start control `C0` and the first TCB. -/
def HU0X (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (Dt : State → Prop) : Prop :=
  ∀ (L D : Int) (lM : String) (fM nM : Nat), Bounds0X cfg p sizes labelOffs (Ly) L D lM fM nM →
    ∀ J : InvS, StJ J → ∀ v, UserCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      bareMC.fn bareMC.Z D (Int64.ofInt (fM : Int))
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab bareMC.sp0).toBitVec C0 TP0

end Assembled

/-- **`main`'s call at the bare start from `main`'s segment**: at every
`Accepted2` program without a setup block, with `mainRetOk`, whose output
passes the placement check at `lay2 Λ p` at a configuration with
`CfgNeedOk`, every entry state, landings' states and write tail, `HU0X`
from `MainSeg2` at every frame invariant. -/
def MainCall0Stmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted2 p = true),
    Scc.Lower.mainRetOk p = true → CfgNeedOk pcfg = true → Scc.Lower.setupOf p = none →
    ∀ (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
      (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop),
    (∀ J : InvS, MainSeg2 h hp Dt J) → HU0X h E El Dt

end Spike.Lib.LowerX64
