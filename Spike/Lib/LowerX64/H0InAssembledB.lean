/-
**`H0In` for a program with a setup block, assembled, its code, start and
stack facts discharged** (x86-64; the twin of
`Spike/Lib/LowerA64/H0InAssembledBA.lean`): `h0In_setup_assembledS` with the
switch depth `L`, the callee rooms `D1`, `D2`, the callees' frames and every
stack bound from `stackBounds2` (at the configuration's `CfgNeedOk`). The
setup call `hS` and `main`'s call `hU` are stated for every choice of the
bounds (`Bounds2`, `stackBounds2`'s conjunction, field for field).

- `Bounds2`: the bounds `stackBounds2` picks.
- `h0In_setup_assembledB`: `H0In` from `hE`, `hPost`, `hS`, `hU`.
-/
import Spike.Lib.LowerX64.H0InAssembledS
import Spike.Lib.LowerX64.StackBounds2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64 (swR)

/-- **The bounds `stackBounds2` picks** (x86-64): its conjunction, field
for field, at the runtime layout `Lr`, the switch depth `L`, the callee
rooms `D1`, `D2` (each room for the callee's need, the stack check's `48`
and the deepest runtime routine's `208`, `needDRX`), the callees' row labels
`lS`, `lM`, frames `fS`, `fM` and needs `nS`, `nM`. -/
def Bounds2 (cfg : Scc.Config) (p : Prog) (sizes : List Nat) (labelOffs : List (String × Nat))
    (Lr : Spike.Lib.X64.Rt.RuntimeLayout) (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat) : Prop :=
  Scc.Cert.NeedX64.row? (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user "rodata") = some (lS, fS + 8, nS) ∧ fS + 8 ≤ nS ∧ (nS : Int) + 48 ≤ D1 ∧
      (nS : Int) + 48 + 208 ≤ D1 ∧ (fS : Int) + 48 ≤ D1 ∧
    Scc.Cert.NeedX64.row? (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
      (Scc.Lower.Names.user "main") = some (lM, fM + 8, nM) ∧ fM + 8 ≤ nM ∧ (nM : Int) + 48 ≤ D2 ∧
      (nM : Int) + 48 + 208 ≤ D2 ∧ (fM : Int) + 48 ≤ D2 ∧
    (∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS) ∧
    (∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "main" →
        (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fM) ∧
    8 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧ 0 ≤ D1 ∧ D1 % 8 = 0 ∧ 0 ≤ D2 ∧ D2 % 8 = 0 ∧ 8 ≤ D1 ∧
    8 + 8 + (Spike.Lib.X64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + 8 + D1 ≤ L ∧
    8 + 8 + (Spike.Lib.X64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + 8 + D2 ≤ L ∧
    Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 -
      (Spike.Lib.X64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec).toNat ∧
    Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 -
      (Spike.Lib.X64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec - 8#64 - 8#64 -
      (Int64.ofInt (fS : Int)).toBitVec).toNat ∧
    Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 - 8#64 - 8#64 -
      (Spike.Lib.X64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec - 8#64 - 8#64 -
      (Int64.ofInt (fM : Int)).toBitVec).toNat ∧
    (((swR (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).Off (-16) ∧
      ∀ j < (Spike.Lib.X64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).sw,
        ((swR (Spike.Lib.X64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).Off
          (-24 - 8 * (j : Int)))

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open A9NoSpawn Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2)
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWSF MainSW SetupArgs swFSL mainSIn oU rS0 entryR rtF setupMC
  rtCodeOkS mainS0R mainSRR CFactsC arOf marshal)

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
/-- The frame invariant `J` holds at the starts (`StartsSX`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
  (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

/-- **`H0In` for a program with a setup block, assembled, its code, start
and stack facts discharged** (x86-64): `h0In_setup_assembledS` with `L`,
`D1`, `D2`, `ZU1 = Int64.ofInt fS`, `ZU2 = Int64.ofInt fM` and their bounds
from `stackBounds2` (at `CfgNeedOk`). The setup call `hS` and `main`'s call
`hU` are for every choice of the bounds (`Bounds2` at the runtime's
layout). Open: the entry `hE`, the main
thread's posts `hPost`, `hS`, `hU`. -/
theorem h0In_setup_assembledB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true) (hE : E.Ok (lay2 Λ p))
    (hPost : ∀ c fs v, UPostRF p (fun _ => none) c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs)
    (hS : ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
        (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt (fS : Int))
        (SRetR (fun _ => none) ty) ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0)
    (hU : ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
        (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 (Int64.ofInt (fM : Int))
        (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (TP0).toBitVec)
        (UPostRF p (fun _ => none)) ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec TP0) :
    H0In h E El Dt := by
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  obtain ⟨L, D1, D2, lS, lM, fS, nS, fM, nM, hB⟩ := stackBounds2 h hp hs hcfg (Ly)
  have hS' := hS L D1 D2 lS lM fS nS fM nM hB
  have hU' := hU L D1 D2 lS lM fS nS fM nM hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hL, hLm, hL8, hD10, hD18, hD20, hD28, hD8, hL1, hL2, hZM, hZS, hZU,
    hOff⟩ := hB
  exact h0In_setup_assembledS h hp hty hE hL hLm hL8 hD10 hD18 hD20 hD28 hPost hOff hL1 hL2 hZM hZS hZU hS'
    hD8 hU'

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.h0In_setup_assembledB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0In_setup_assembledB

end Spike.Lib.LowerX64
