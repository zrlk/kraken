/-
**`H0InA` for a program with a setup block, `main`'s post placed by its
value** (AArch64; the twin of `Spike/Lib/LowerX64/H0InAssembledV.lean`):
the `H0InA` chain (`Spike/Lib/LowerA64/H0InSetupA.lean`,
`Spike/Lib/LowerA64/H0InAssembledA.lean`,
`Spike/Lib/LowerA64/H0InAssembledCA.lean`) over `h0_ofPlaceOK_setupFV`
(`Spike/Lib/LowerA64/RtMainXVA.lean`): the post's controls at `MainCtlV`
in place of `MainCtlN`. The assembled theorems take `main`'s post
`UPostRF ∧ MainCtlV`, asked of the user call `hU` at its held pair, so
`hPost` is gone.

- `h0InA_of_setupFV`, `h0InA_of_setupFNPV`: `h0InA_of_setupFN`,
  `h0InA_of_setupFNP` at `MainCtlV`;
- `h0InA_setup_assembledV`, `h0InA_setup_assembledCV`:
  `h0InA_setup_assembled`, `h0InA_setup_assembledC` at the post
  `UPostRF ∧ MainCtlV`, without `hPost`.
-/
import Spike.Lib.LowerA64.RtMainXVA
import Spike.Lib.LowerA64.H0InAssembledCA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (InstOk SetupCode setupMC MainSW mainSIn SetupCallWS MainCallWSF SetupArgs swFSL rS0 entryR
  rtF arOf)
open Spike.Lib.A64.Rt.MainS (MainPhS)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.AllocReach (Reach IN)

section Setup

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) o = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) o)).term, (th02 p (meW2 (lay2 Λ p) o)).env, none⟩ : Ctl)

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

/-- **`H0InA` from the setup-block start**: `h0_ofPlaceOK_setupFV` at
`FE := rtF Ly`, `rd := IsNum`, `ls0 := 0`, `ab := ab2` and the program's
start control, its `W2`-side calls `hS`, `hU` at every frame invariant
holding at the starts. -/
theorem h0InA_of_setupFV {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (hE : E.Ok (lay2 Λ p)) {lbl0 : Lbl} {L : Int}
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 C0 []) (hov : ¬ OvfReady C0) (hC0 : CFacts (lay2 Λ p) lbl0 C0)
    (hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [])
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hL1 : (setupMC sw).Z.toInt + D1 ≤ L) (hL2 : (setupMC sw).Z.toInt + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec - ZU2.toBitVec).toNat)
    (hPostS : ∀ c rs, PostS c rs → CFactsC c ∧ MainCtlC c [])
    (hPU : ∀ c fs v, Post c fs v → UPostRF p (fun _ => none) c fs v)
    (hPost : ∀ c fs v, Post c fs v → MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
    (hPlS : BlkW (fun s c => Placed (lay2 Λ p) lbl0 s c ∧ PlacedS (lay2 Λ p) (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), C0⟩
        (pinA (Ly).lab + 0#64 + 8#64))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).e0 + 4).toBitVec C0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.A64.Flow.CallTo p C0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.A64.Flow.CallTo p C0 cE fr → PostR c rs →
      ∃ c'', Spike.Lib.FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    {chk entry : Label} {Zs lim : Int64} {Lg : Label} {ps : List (XReg × Int64)}
    (hproS : prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg ps = true)
    (hphS : blkPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab chk + Int64.ofNat (4 * 0)) 0 (chkHead Zs) = true)
    (hlS : chk ∉ abLabs)
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2 (SetupArgs PostS (setupMC sw).sw (pinA (Ly).lab + 0#64 + 8#64)) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) :
    H0InA h E El Dt :=
  ⟨fun J hJ => h0_ofPlaceOK_setupFV h (Spike.Lib.LowerNode.imms2Me Λ p) (rd := Spike.Lib.LowerNode.IsNum) (J := J) (Dt := Dt)
    (ls0 := fun _ => 0) (ab := ab2 p (Ly).lab) hE (fun _ hm => hm) (Spike.Lib.A64.Rt.rtF_stable _ hE)
    (fun _ _ hm => Spike.Lib.A64.Rt.rtF_takeMem _ (Spike.Lib.A64.Rt.rS0_sub _) hm)
    hp hf0 hov hC0 hpl0 hL0 hL hL8 hsw hc hph hgrow hset hfn hD10 hD18 hD20 hD28 hL1 hL2 hZM hZS hZU hPostS hPU
    hPost hPlS (hS J hJ) hcall hPS hproS hphS hlS (hU J hJ)⟩

/-- **`H0InA` from the setup-block start, the runtime's code facts from the
placement check** (`h0InA_of_setupFV`): at a `.setup` tail (`hs`) and the
runtime's code at `setupMC sw` (`hc`, A11 then gives `sw < 8` and
`MainPhS`), the stack-growth stub's label in the code (`hstk`), the setup's
and the user function's labels right before their stack checks' heads
(`hproS`, `hproF`), those off the write abort (`hlS`, `hlF`). -/
theorem h0InA_of_setupFNPV {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {Dt : State → Prop} (hE : E.Ok (lay2 Λ p)) {lbl0 : Lbl} {L : Int}
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 C0 []) (hov : ¬ OvfReady C0) (hC0 : CFacts (lay2 Λ p) lbl0 C0)
    (hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [])
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    (hs : o.place.tail = .setup) {sw : Nat} (hc : Spike.Lib.A64.Rt.rtCodeOkS o.prog (setupMC sw) = true)
    (hstk : Scc.Cert.Rt.A64.InRun o.prog ".L1_scc_rt_main.stack_grow" 0)
    {chkF entryF : Label} {ZF limF : Int64} {LgF : Label} {psF : List (XReg × Int64)}
    (hproF : prologueIn o.prog (setupMC sw).fn chkF entryF ZF limF LgF psF = true) (hlF : chkF ∉ abLabs)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hL1 : (setupMC sw).Z.toInt + D1 ≤ L) (hL2 : (setupMC sw).Z.toInt + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec - ZU2.toBitVec).toNat)
    (hPostS : ∀ c rs, PostS c rs → CFactsC c ∧ MainCtlC c [])
    (hPU : ∀ c fs v, Post c fs v → UPostRF p (fun _ => none) c fs v)
    (hPost : ∀ c fs v, Post c fs v → MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
    (hPlS : BlkW (fun s c => Placed (lay2 Λ p) lbl0 s c ∧ PlacedS (lay2 Λ p) (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), C0⟩
        (pinA (Ly).lab + 0#64 + 8#64))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).e0 + 4).toBitVec C0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.A64.Flow.CallTo p C0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.A64.Flow.CallTo p C0 cE fr → PostR c rs →
      ∃ c'', Spike.Lib.FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    {chk entry : Label} {Zs lim : Int64} {Lg : Label} {ps : List (XReg × Int64)}
    (hproS : prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg ps = true)
    (hphS : blkPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab chk + Int64.ofNat (4 * 0)) 0 (chkHead Zs) = true)
    (hlS : chk ∉ abLabs)
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2 (SetupArgs PostS (setupMC sw).sw (pinA (Ly).lab + 0#64 + 8#64)) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) :
    H0InA h E El Dt := by
  obtain ⟨hsw, hrt⟩ := setupIn_sw_eq h hs hc
  have hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw) :=
    Spike.Lib.A64.Rt.mainPhS_of_tab h _ hrt
  have hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow) :=
    ⟨".L1_scc_rt_main.stack_grow", 0, hstk, by decide, ofNat4_zero _⟩
  have hpro : ∀ {fn chk entry : Label} {Z lim : Int64} {Lg : Label} {ps : List (XReg × Int64)},
      prologueIn (Ly).prog fn chk entry Z lim Lg ps = true → chk ∉ abLabs →
      PosOff (Ly).prog (Ly).lab ((Ly).lab fn) := by
    intro fn chk entry Z lim Lg ps hpr hl
    simp only [prologueIn, Bool.and_eq_true] at hpr
    have hb := posOff_of_blockAt (lab := (Ly).lab) hpr.1.1.1.1.2 hl (i := 0) (by simp [chkHead])
    rw [show 4 * (0 + 0) = 4 * 0 from rfl, ofNat4_zero] at hb
    exact posOff_of_labelGap (Ly).lays hpr.1.1.1.1.1 hb
  exact h0InA_of_setupFV h hE hp hf0 hov hC0 hpl0 hL0 hL hL8 hsw hc hph hgrow (hpro hproS hlS) (hpro hproF hlF)
    hD10 hD18 hD20 hD28 hL1 hL2 hZM hZS hZU hPostS hPU hPost hPlS hS hcall hPS hproS hphS hlS hU

end Setup


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

/-- **`H0InA` for a program with a setup block, assembled, `main`'s post placed by its value**
(AArch64; at the post `UPostRF ∧ MainCtlV`, without `hPost`): at
the lowering's output of an `Accepted2` program `p` with a setup block of
result type `ty` (`hty`), the runtime's code at `setupMC (setupWords2 p)`,
the posts `SRetR` / `SPostC` / `UPostRF`. Open (as x86-64's
`h0In_setup_assembled`, AArch64's prologue facts in place of its `hfnB`):

- the start control's facts (`hE`, `hp0`, `hf0`, `hov`, `hC0`, `hpl0`) and
  the switch depth `L` (`hL0`, `hLm`, `hL8`);
- `main`'s prologue (`hproF`, `hlF`), the setup's prologue (`hproS`, `hphS`, `hlS`);
- the callees' room (`hD10` … `hD28`, `hL1`, `hL2`) and the limit's room
  past each frame (`hZM`, `hZS`, `hZU`);
- the setup's post's facts (`hPostS`) and the start's call (`hcall`);
- the marshalling block's base cell in the region (`hOff`) and the start's
  environment represented by the first TCB (`hme`);
- the two calls (`hS`, `hU`). -/
theorem h0InA_setup_assembledV {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
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
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0))
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
  exact h0InA_of_setupFNPV h hE hp0 hf0 hov hC0 hpl0 hL0 hLm hL8 htl hc
    (hstkA_of_placeOKAt h hp hs') hproF hlF hD10 hD18 hD20 hD28
    hL1 hL2 hZM hZS hZU hPostS (fun _ _ _ h => h.1) (fun _ _ _ h => h.2) hPlS hS hcall (hPS_framed (p := p)) hproS
    hphS hlS hU

/-- **`H0InA` for a program with a setup block, assembled, its code facts
discharged, `main`'s post placed by its value** (AArch64): `h0InA_setup_assembledV` without `hproF`, `hlF`,
`hproS`, `hphS`, `hlS` (`mainPro_ofPlaceOK`, `setupCode_ofPlaceOK` at the
theorem's immediates and setup words) and `hPostS` (`postS_setupTerm`). Open: as `h0InA_setup_assembledV`
otherwise. -/
theorem h0InA_setup_assembledCV {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
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
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0))
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
  exact h0InA_setup_assembledV h hp hty hE hp0 hf0 hov hC0 hpl0 hL0 hLm hL8 hproF hlF hD10 hD18 hD20 hD28
    hL1 hL2 hZM hZS hZU (postS_setupTerm (th02_term_setup hty _)) hOff hme hS hcall hproS hphS hlS hU

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.h0InA_of_setupFV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0InA_of_setupFV

/-- info: 'Spike.Lib.LowerA64.h0InA_of_setupFNPV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0InA_of_setupFNPV

/-- info: 'Spike.Lib.LowerA64.h0InA_setup_assembledV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0InA_setup_assembledV

/-- info: 'Spike.Lib.LowerA64.h0InA_setup_assembledCV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0InA_setup_assembledCV

end Spike.Lib.LowerA64
