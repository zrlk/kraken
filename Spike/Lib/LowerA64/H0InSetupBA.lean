/-
**`H0InA` from the setup-block start at the setup call's known frame
condition** (AArch64): `Spike/Lib/LowerA64/H0InSetupA.lean` over
`h0_ofPlaceOK_setupFNB` (`Spike/Lib/LowerA64/RtMainXNB.lean`), the setup
call `hS` at `SetupCallWSB` with the callee's frame condition `SetupGF`.

- `h0InA_of_setupFNB`: `h0InA_of_setupFN` at `SetupCallWSB` / `SetupGF`.
- `h0InA_of_setupFNPB`: `h0InA_of_setupFNP` at `SetupCallWSB` / `SetupGF`.
-/
import Spike.Lib.LowerA64.Closed2AtA
import Spike.Lib.LowerA64.RtMainXNB
import Spike.Lib.LowerA64.SetupSw
import Spike.Lib.LowerA64.UserAb

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (InstOk SetupCode setupMC MainSW mainSIn SetupCallWSB SetupGF MainCallWSF SetupArgs swFSL rS0
  entryR rtF arOf)
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

/-- **`H0InA` from the setup-block start, at the setup call's known frame
condition** (`h0InA_of_setupFN`): `h0_ofPlaceOK_setupFNB` at `FE := rtF Ly`,
`rd := IsNum`, `ls0 := 0`, `ab := ab2` and the program's start control, its
`W2`-side calls `hS` (at `SetupCallWSB` / `SetupGF`), `hU` at every frame
invariant holding at the starts. -/
theorem h0InA_of_setupFNB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
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
    (hPost : ∀ c fs v, Post c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs)
    (hPlS : BlkW (fun s c => Placed (lay2 Λ p) lbl0 s c ∧ PlacedS (lay2 Λ p) (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), C0⟩
        (pinA (Ly).lab + 0#64 + 8#64))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).e0 + 4).toBitVec C0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0)
        (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (setupMC sw) D1 ZU1
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), C0⟩
        (pinA (Ly).lab + 0#64 + 8#64)))
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
  ⟨fun J hJ => h0_ofPlaceOK_setupFNB h (Spike.Lib.LowerNode.imms2Me Λ p) (rd := Spike.Lib.LowerNode.IsNum) (J := J) (Dt := Dt)
    (ls0 := fun _ => 0) (ab := ab2 p (Ly).lab) hE (fun _ hm => hm) (Spike.Lib.A64.Rt.rtF_stable _ hE)
    (fun _ _ hm => Spike.Lib.A64.Rt.rtF_takeMem _ (Spike.Lib.A64.Rt.rS0_sub _) hm)
    hp hf0 hov hC0 hpl0 hL0 hL hL8 hsw hc hph hgrow hset hfn hD10 hD18 hD20 hD28 hL1 hL2 hZM hZS hZU hPostS hPU
    hPost hPlS (hS J hJ) hcall hPS hproS hphS hlS (hU J hJ)⟩

/-- **`H0InA` from the setup-block start at the setup call's known frame
condition, the runtime's code facts from the placement check**
(`h0InA_of_setupFNP` through `h0InA_of_setupFNB`): at a `.setup` tail (`hs`) and the
runtime's code at `setupMC sw` (`hc`, A11 then gives `sw < 8` and
`MainPhS`), the stack-growth stub's label in the code (`hstk`), the setup's
and the user function's labels right before their stack checks' heads
(`hproS`, `hproF`), those off the write abort (`hlS`, `hlF`). -/
theorem h0InA_of_setupFNPB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
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
    (hPost : ∀ c fs v, Post c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs)
    (hPlS : BlkW (fun s c => Placed (lay2 Λ p) lbl0 s c ∧ PlacedS (lay2 Λ p) (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), C0⟩
        (pinA (Ly).lab + 0#64 + 8#64))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).e0 + 4).toBitVec C0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))
      (SetupGF p (Ly).lab ((MSS J) []) (Ly).exe (Ly).endPc (swR v (-L) 0)
        (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (setupMC sw) D1 ZU1
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), C0⟩
        (pinA (Ly).lab + 0#64 + 8#64)))
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
  exact h0InA_of_setupFNB h hE hp hf0 hov hC0 hpl0 hL0 hL hL8 hsw hc hph hgrow (hpro hproS hlS) (hpro hproF hlF)
    hD10 hD18 hD20 hD28 hL1 hL2 hZM hZS hZU hPostS hPU hPost hPlS hS hcall hPS hproS hphS hlS hU

end Setup

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerA64.h0InA_of_setupFNB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0InA_of_setupFNB

/--
info: 'Spike.Lib.LowerA64.h0InA_of_setupFNPB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0InA_of_setupFNPB

end Spike.Lib.LowerA64
