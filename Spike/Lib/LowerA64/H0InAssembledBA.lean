/-
**`H0InA` for a program with a setup block, assembled, its code, start and
stack facts discharged** (AArch64; the twin of
`Spike/Lib/LowerX64/H0InAssembledB.lean`): `h0InA_setup_assembledS` with the
switch depth `L`, the callee rooms `D1`, `D2`, the callees' frames and every
stack bound from `stackBounds2A` (at the configuration's `CfgNeedOkA`). The
setup call `hS` and `main`'s call `hU` are stated for every choice of the
bounds (`Bounds2A`, `stackBounds2A`'s conjunction, field for field).

- `Bounds2A`: the bounds `stackBounds2A` picks.
- `h0InA_setup_assembledB`: `H0InA` from `hE`, `hPost`, `hS`, `hU`.
-/
import Spike.Lib.LowerA64.H0InAssembledSA
import Spike.Lib.LowerA64.StackBounds2A

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm

/-- **The bounds `stackBounds2A` picks** (AArch64): its conjunction, field
for field, at the runtime layout `Lr`, the switch depth `L`, the callee
rooms `D1`, `D2` (each room for the callee's need, the stack check's `48`
and the deepest runtime routine's `208`, `needDR`), the callees' row labels
`lS`, `lM`, frames `fS`, `fM` and needs `nS`, `nM`. -/
def Bounds2A (cfg : Scc.Config) (p : Prog) (Lr : Spike.Lib.A64.Rt.RuntimeLayout) (L D1 D2 : Int) (lS lM : String)
    (fS nS fM nM : Nat) : Prop :=
  Scc.Cert.NeedA64.row? (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
      (Scc.Lower.Names.user "rodata") = some (lS, fS, nS) ∧ fS ≤ nS ∧ (nS : Int) + 48 ≤ D1 ∧
      (nS : Int) + 48 + 208 ≤ D1 ∧
    Scc.Cert.NeedA64.row? (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need
      (Scc.Lower.Names.user "main") = some (lM, fM, nM) ∧ fM ≤ nM ∧ (nM : Int) + 48 ≤ D2 ∧
      (nM : Int) + 48 + 208 ≤ D2 ∧
    (∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS) ∧
    (∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "main" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fM) ∧
    0 ≤ L ∧ L ≤ 16384 ∧ L % 8 = 0 ∧ 0 ≤ D1 ∧ D1 % 8 = 0 ∧ 0 ≤ D2 ∧ D2 % 8 = 0 ∧
    (Spike.Lib.A64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + D1 ≤ L ∧
    (Spike.Lib.A64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt + D2 ≤ L ∧
    Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 -
      (Spike.Lib.A64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec).toNat ∧
    Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 -
      (Spike.Lib.A64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec -
      (Int64.ofInt (fS : Int)).toBitVec).toNat ∧
    Lr.stacksA.toNat + 4096 ≤ (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64 -
      (Spike.Lib.A64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toBitVec -
      (Int64.ofInt (fM : Int)).toBitVec).toNat ∧
    (Spike.Lib.A64.Flow.swR (Spike.Lib.A64.Flow.Ret0.stacksA Lr.lab + 0#64 + 16384#64) (-L) 0).Off
      (-(Spike.Lib.A64.Rt.setupMC (Spike.Lib.LowerNode.setupWords2 p)).Z.toInt)

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (SetupCode setupMC SetupCallWS MainCallWSF SetupArgs swFSL rS0 rtF arOf)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2)
open Spike.Lib.AllocReach (Reach IN)

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
/-- The frame invariant `J` holds at the starts (`StartsSA`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB's address. -/
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (X0)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v

/-- **`H0InA` for a program with a setup block, assembled, its code, start
and stack facts discharged** (AArch64): `h0InA_setup_assembledS` with `L`,
`D1`, `D2`, `ZU1 = Int64.ofInt fS`, `ZU2 = Int64.ofInt fM` and their bounds
from `stackBounds2A` (at `CfgNeedOkA`). The setup call `hS` and `main`'s
call `hU` are for every choice of the bounds (`Bounds2A` at the runtime's
layout). Open: the entry `hE`, the main
thread's posts `hPost`, `hS`, `hU`. -/
theorem h0InA_setup_assembledB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true) (hE : E.Ok (lay2 Λ p))
    (hPost : ∀ c fs v, UPostRF p (fun _ => none) c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs)
    (hS : ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt (fS : Int))
        (SRetR (fun _ => none) ty) ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0))
    (hU : ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 (Int64.ofInt (fM : Int))
        (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (X0))
        (UPostRF p (fun _ => none)) ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0)) :
    H0InA h E El Dt := by
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  obtain ⟨L, D1, D2, lS, lM, fS, nS, fM, nM, hB⟩ := stackBounds2A h hp hs hcfg (Ly)
  have hS' := hS L D1 D2 lS lM fS nS fM nM hB
  have hU' := hU L D1 D2 lS lM fS nS fM nM hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hL0, hLm, hL8, hD10, hD18, hD20, hD28, hL1, hL2, hZM, hZS, hZU, hOff⟩ := hB
  exact h0InA_setup_assembledS h hp hty hE hL0 hLm hL8 hD10 hD18 hD20 hD28 hL1 hL2 hZM hZS hZU hPost hOff
    hS' hU'

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.h0InA_setup_assembledB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0InA_setup_assembledB

end Spike.Lib.LowerA64
