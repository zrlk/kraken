/-
**`H0In` for a program with a setup block, assembled, its code, start and
stack facts discharged, at the setup call's known frame condition,
`main`'s post placed by its value** (x86-64; the twin of
`Spike/Lib/LowerA64/H0InAssembledBVBA.lean`): `h0In_setup_assembledS` and
`h0In_setup_assembledB` (`Spike/Lib/LowerX64/H0InAssembledS.lean`,
`Spike/Lib/LowerX64/H0InAssembledB.lean`) over `h0In_setup_assembledCVB`
(`Spike/Lib/LowerX64/H0InAssembledCVB.lean`). The setup call `hS` is at
`SetupCallWSB` with the callee's frame condition `SetupGF`, `main`'s call
`hU` at the post `UPostRF ∧ MainCtlV`, so `hPost` is gone.

- `h0In_setup_assembledSVB`: `h0In_setup_assembledS` at `SetupCallWSB` /
  `SetupGF` and `UPostRF ∧ MainCtlV`;
- `h0In_setup_assembledBVB`: `h0In_setup_assembledB` likewise, `hS` / `hU` for
  every choice of the bounds (`Bounds2`).
-/
import Spike.Lib.LowerX64.H0InAssembledB
import Spike.Lib.LowerX64.H0InAssembledCVB

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64 (swR)

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
open Spike.Lib.X64.Rt (SetupCallWSB SetupGF)

/-- **`H0In` for a program with a setup block, assembled, its code and start
facts discharged, at the setup call's known frame condition, `main`'s post
placed by its value** (`h0In_setup_assembledS` over
`h0In_setup_assembledCVB`): the setup call `hS` at `SetupCallWSB` /
`SetupGF`, `main`'s post `UPostRF ∧ MainCtlV`, so without `hPost`. Open:
as `h0In_setup_assembledS` otherwise. -/
theorem h0In_setup_assembledSVB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hE : E.Ok (lay2 Λ p)) {L : Int}
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    (hOff : (RS TOP).Off (-16) ∧ ∀ j < (setupMC (setupWords2 p)).sw, (RS TOP).Off (-24 - 8 * (j : Int)))
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hL2 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC (setupWords2 p)).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC (setupWords2 p)).Z.toBitVec -
      8#64 - 8#64 - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC (setupWords2 p)).Z.toBitVec -
      8#64 - 8#64 - ZU2.toBitVec).toNat)
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0
      (SetupGF p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 ZU1 ⟨TOP - 8#64, TP0, C0⟩
        (TP0).toBitVec))
    (hD8 : 8 ≤ D1)
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 ZU2
      (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (TP0).toBitVec)
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec TP0) :
    H0In h E El Dt :=
  h0In_setup_assembledCVB h hp hty hE (hp0_start2 hp) (hf0_start2 hty _) (hov_start2 hty _) (hC0_start2 h hty _)
    (hpl0_start2 h hty _) hL hLm hL8 hD10 hD18 hD20 hD28 hOff (hme_start2 h hty _) hL1 hL2 hZM hZS hZU
    hS (hcall_start2 hp hty _) hD8 hU


/-- **`H0In` for a program with a setup block, assembled, its code, start
and stack facts discharged, at the setup call's known frame condition,
`main`'s post placed by its value** (`h0In_setup_assembledB` over
`h0In_setup_assembledSVB`): `hS` at `SetupCallWSB` / `SetupGF` and `hU` at
`main`'s post `UPostRF ∧ MainCtlV`, both for every choice of the bounds
(`Bounds2`). Open: the entry `hE`, `hS`, `hU`. -/
theorem h0In_setup_assembledBVB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true) (hE : E.Ok (lay2 Λ p))
    (hS : ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
        (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 (Int64.ofInt (fS : Int))
        (SRetR (fun _ => none) ty) ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0
        (SetupGF p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt (fS : Int))
          ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec))
    (hU : ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
      Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
      ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
        (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
        (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 (Int64.ofInt (fM : Int))
        (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (TP0).toBitVec)
        (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
        ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec TP0) :
    H0In h E El Dt := by
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  obtain ⟨L, D1, D2, lS, lM, fS, nS, fM, nM, hB⟩ := stackBounds2 h hp hs hcfg (Ly)
  have hS' := hS L D1 D2 lS lM fS nS fM nM hB
  have hU' := hU L D1 D2 lS lM fS nS fM nM hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hL, hLm, hL8, hD10, hD18, hD20, hD28, hD8, hL1, hL2, hZM, hZS, hZU,
    hOff⟩ := hB
  exact h0In_setup_assembledSVB h hp hty hE hL hLm hL8 hD10 hD18 hD20 hD28 hOff hL1 hL2 hZM hZS hZU hS'
    hD8 hU'


end Assembled

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerX64.h0In_setup_assembledSVB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0In_setup_assembledSVB

/--
info: 'Spike.Lib.LowerX64.h0In_setup_assembledBVB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0In_setup_assembledBVB

end Spike.Lib.LowerX64
