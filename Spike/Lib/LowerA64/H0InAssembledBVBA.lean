/-
**`H0InA` for a program with a setup block, assembled, its code, start and
stack facts discharged, at the setup call's known frame condition,
`main`'s post placed by its value** (AArch64; the twin of
`Spike/Lib/LowerX64/H0InAssembledBVB.lean`): `h0InA_setup_assembledS` and
`h0InA_setup_assembledB` (`Spike/Lib/LowerA64/H0InAssembledSA.lean`,
`Spike/Lib/LowerA64/H0InAssembledBA.lean`) over `h0InA_setup_assembledCVB`
(`Spike/Lib/LowerA64/H0InAssembledCVBA.lean`). The setup call `hS` is at
`SetupCallWSB` with the callee's frame condition `SetupGF`, `main`'s call
`hU` at the post `UPostRF ∧ MainCtlV`, so `hPost` is gone.

- `h0InA_setup_assembledSVB`: `h0InA_setup_assembledS` at `SetupCallWSB` /
  `SetupGF` and `UPostRF ∧ MainCtlV`;
- `h0InA_setup_assembledBVB`: `h0InA_setup_assembledB` likewise, `hS` / `hU` for
  every choice of the bounds (`Bounds2A`).
-/
import Spike.Lib.LowerA64.H0InAssembledBA
import Spike.Lib.LowerA64.H0InAssembledCVBA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm

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
open Spike.Lib.A64.Rt (SetupCallWSB SetupGF)

/-- **`H0InA` for a program with a setup block, assembled, its code and start
facts discharged, at the setup call's known frame condition, `main`'s post
placed by its value** (`h0InA_setup_assembledS` over
`h0InA_setup_assembledCVB`): the setup call `hS` at `SetupCallWSB` /
`SetupGF`, `main`'s post `UPostRF ∧ MainCtlV`, so without `hPost`. Open:
as `h0InA_setup_assembledS` otherwise. -/
theorem h0InA_setup_assembledSVB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hE : E.Ok (lay2 Λ p)) {L : Int}
    (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L) (hL2 : (setupMC (setupWords2 p)).Z.toInt + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC (setupWords2 p)).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC (setupWords2 p)).Z.toBitVec - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC (setupWords2 p)).Z.toBitVec - ZU2.toBitVec).toNat)
    (hOff : (swR (TOP) (-L) 0).Off (-(setupMC (setupWords2 p)).Z.toInt))
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v) (setupMC (setupWords2 p)) D1 ZU1
        ⟨TOP, TP0, C0⟩ (X0)))
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 ZU2
      (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (X0))
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0)) :
    H0InA h E El Dt :=
  h0InA_setup_assembledCVB h hp hty hE (hp0_start2A hp) (hf0_start2A hty _) (hov_start2A hty _)
    (hC0_start2A h hty _) (hpl0_start2A h hty _) hL0 hLm hL8 hD10 hD18 hD20 hD28 hL1 hL2 hZM hZS hZU
    hOff (hme_start2A h hty _) hS (hcall_start2A hp hty _) hU


/-- **`H0InA` for a program with a setup block, assembled, its code, start
and stack facts discharged, at the setup call's known frame condition,
`main`'s post placed by its value** (`h0InA_setup_assembledB` over
`h0InA_setup_assembledSVB`): `hS` at `SetupCallWSB` / `SetupGF` and `hU` at
`main`'s post `UPostRF ∧ MainCtlV`, both for every choice of the bounds
(`Bounds2A`). Open: the entry `hE`, `hS`, `hU`. -/
theorem h0InA_setup_assembledBVB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true) (hE : E.Ok (lay2 Λ p))
    (hS : ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt (fS : Int))
        (SRetR (fun _ => none) ty) ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)
        (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v) (setupMC (setupWords2 p)) D1
          (Int64.ofInt (fS : Int))
          ⟨TOP, TP0, C0⟩ (X0)))
    (hU : ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 (Int64.ofInt (fM : Int))
        (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (X0))
        (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
        ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0)) :
    H0InA h E El Dt := by
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  obtain ⟨L, D1, D2, lS, lM, fS, nS, fM, nM, hB⟩ := stackBounds2A h hp hs hcfg (Ly)
  have hS' := hS L D1 D2 lS lM fS nS fM nM hB
  have hU' := hU L D1 D2 lS lM fS nS fM nM hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hL0, hLm, hL8, hD10, hD18, hD20, hD28, hL1, hL2, hZM, hZS, hZU, hOff⟩ := hB
  exact h0InA_setup_assembledSVB h hp hty hE hL0 hLm hL8 hD10 hD18 hD20 hD28 hL1 hL2 hZM hZS hZU hOff
    hS' hU'


end Assembled

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerA64.h0InA_setup_assembledSVB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0InA_setup_assembledSVB

/--
info: 'Spike.Lib.LowerA64.h0InA_setup_assembledBVB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0InA_setup_assembledBVB

end Spike.Lib.LowerA64
