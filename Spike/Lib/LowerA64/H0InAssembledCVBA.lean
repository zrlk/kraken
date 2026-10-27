/-
**`H0InA` for a program with a setup block, assembled, at the setup call's
known frame condition, `main`'s post placed by its value** (AArch64; the twin
of `Spike/Lib/LowerX64/H0InAssembledCVB.lean`):
`Spike/Lib/LowerA64/H0InAssembledCBA.lean` over `h0InA_of_setupFNPVB`
(`Spike/Lib/LowerA64/H0InSetupVBA.lean`). The assembled theorems take
`main`'s post `UPostRF ∧ MainCtlV`, asked of the user call `hU` at its
held pair, so `hPost` is gone (as in
`Spike/Lib/LowerA64/H0InAssembledVA.lean`).

- `h0InA_setup_assembledFVB`: `h0InA_setup_assembledFB` at `UPostRF ∧ MainCtlV`.
- `h0InA_setup_assembledCVB`: `h0InA_setup_assembledCB` at `UPostRF ∧ MainCtlV`.
-/
import Spike.Lib.LowerA64.H0InAssembledCA
import Spike.Lib.LowerA64.H0InSetupVBA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (SetupCode setupMC SetupCallWSB SetupGF MainCallWSF SetupArgs swFSL rS0 rtF arOf)
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

/-- **`H0InA` for a program with a setup block, assembled, at the setup
call's known frame condition** (`h0InA_setup_assembled` through
`h0InA_of_setupFNPVB`): the setup call `hS` at `SetupCallWSB` with the
callee's frame condition `SetupGF`. `main`'s post `UPostRF ∧ MainCtlV`
(asked of `hU` at the held pair), so without `hPost`. Open: as
`h0InA_setup_assembled` otherwise. -/
theorem h0InA_setup_assembledFVB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hE : E.Ok (lay2 Λ p)) {L : Int}
    (hp0 : ProgNoS ZBad p) (hf0 : FrOk2 C0 []) (hov : ¬ OvfReady C0) (hC0 : CFacts (lay2 Λ p) (fun _ => none) C0)
    (hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [])
    (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {chkF entryF : Label} {ZF limF : Int64} {LgF : Label} {psF : List (XReg × Int64)}
    (hproF : prologueIn (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (setupMC (setupWords2 p)).fn chkF
      entryF ZF limF LgF psF = true) (hlF : chkF ∉ abLabs)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L) (hL2 : (setupMC (setupWords2 p)).Z.toInt + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC (setupWords2 p)).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC (setupWords2 p)).Z.toBitVec - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC (setupWords2 p)).Z.toBitVec - ZU2.toBitVec).toNat)
    (hPostS : ∀ c rs, SPostC p (fun _ => none) ty C0 c rs → CFactsC c ∧ MainCtlC c [])
    (hOff : (swR (TOP) (-L) 0).Off (-(setupMC (setupWords2 p)).Z.toInt))
    (hme : ∀ y t ws, TermRun.lookupE (C0).env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep (fun _ => none) ws[k].val (X0).toNat)
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v) (setupMC (setupWords2 p)) D1 ZU1
        ⟨TOP, TP0, C0⟩ (X0)))
    (hcall : ∃ cE fr, Spike.Lib.A64.Flow.CallTo p C0 cE fr)
    {chk entry : Label} {Zs lim : Int64} {Lg : Label} {ps : List (XReg × Int64)}
    (hproS : prologueIn (Ly).prog (setupMC (setupWords2 p)).setup chk entry Zs lim Lg ps = true)
    (hphS : blkPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab chk + Int64.ofNat (4 * 0)) 0 (chkHead Zs) = true)
    (hlS : chk ∉ abLabs)
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 ZU2
      (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (X0))
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0)) :
    H0InA h E El Dt := by
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hc := rtCodeOkS_setupWords2A h hp hs'
  have htl := tail_setup_of_accepted2A h hp hs'
  have hsw := (setupIn_sw_eq h htl hc).1
  have hPlS := hPlS_ofSPostC (Λ := lay2 Λ p) (lbl := fun _ => none) (p := p) (ty := ty)
    (exe := (Ly).exe) (endPc := (Ly).endPc) (F := FS (TOP)) (Ly).lab
    (sc := setupMC (setupWords2 p)) (g := ⟨TOP, TP0, C0⟩) (x0 := X0)
    (by simp only [setupMC]; omega) (Spike.Lib.LowerNode.simpleTy_of_accepted2 hp ty hty)
    (valWords_of_rtCodeOkSA h hp hty hc) hOff hme
  exact h0InA_of_setupFNPVB h hE hp0 hf0 hov hC0 hpl0 hL0 hLm hL8 htl hc
    (hstkA_of_placeOKAt h hp hs') hproF hlF hD10 hD18 hD20 hD28
    hL1 hL2 hZM hZS hZU hPostS (fun _ _ _ h => h.1) (fun _ _ _ h => h.2) hPlS hS hcall (hPS_framed (p := p)) hproS
      hphS hlS hU

/-- **`H0InA` for a program with a setup block, assembled, its code facts
discharged, at the setup call's known frame condition**
(`h0InA_setup_assembledC` through `h0InA_setup_assembledFVB`): the setup call
`hS` at `SetupCallWSB` with the callee's frame condition `SetupGF`.
`main`'s post `UPostRF ∧ MainCtlV`, so without `hPost`.
Open: as `h0InA_setup_assembledC` otherwise. -/
theorem h0InA_setup_assembledCVB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hE : E.Ok (lay2 Λ p)) {L : Int}
    (hp0 : ProgNoS ZBad p) (hf0 : FrOk2 C0 []) (hov : ¬ OvfReady C0) (hC0 : CFacts (lay2 Λ p) (fun _ => none) C0)
    (hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [])
    (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L) (hL2 : (setupMC (setupWords2 p)).Z.toInt + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC (setupWords2 p)).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC (setupWords2 p)).Z.toBitVec - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC (setupWords2 p)).Z.toBitVec - ZU2.toBitVec).toNat)
    (hOff : (swR (TOP) (-L) 0).Off (-(setupMC (setupWords2 p)).Z.toInt))
    (hme : ∀ y t ws, TermRun.lookupE (C0).env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep (fun _ => none) ws[k].val (X0).toNat)
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0)
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v) (setupMC (setupWords2 p)) D1 ZU1
        ⟨TOP, TP0, C0⟩ (X0)))
    (hcall : ∃ cE fr, Spike.Lib.A64.Flow.CallTo p C0 cE fr)
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 ZU2
      (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (X0))
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0)) :
    H0InA h E El Dt := by
  obtain ⟨chkF, entryF, ZF, limF, LgF, psF, hproF, hlF⟩ := mainPro_ofPlaceOK hp h (setupWords2 p)
  obtain ⟨chk, entry, Zs, lim, Lg, ps, hproS, hphS, hlS⟩ :=
    setupCode_ofPlaceOK hp hty h (Spike.Lib.LowerNode.imms2Me Λ p) (setupWords2 p)
  exact h0InA_setup_assembledFVB h hp hty hE hp0 hf0 hov hC0 hpl0 hL0 hLm hL8 hproF hlF hD10 hD18 hD20 hD28
    hL1 hL2 hZM hZS hZU (postS_setupTerm (th02_term_setup hty _)) hOff hme hS hcall hproS hphS hlS hU

end Assembled

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerA64.h0InA_setup_assembledFVB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0InA_setup_assembledFVB

/--
info: 'Spike.Lib.LowerA64.h0InA_setup_assembledCVB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0InA_setup_assembledCVB

end Spike.Lib.LowerA64
