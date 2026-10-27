/-
Draft check (AArch64): `h0InA_setup_assembled`'s `hS` from `setupCallWS_ofPlaceOK` at the assembled instance.
-/
import Spike.Lib.LowerA64.H0InAssembledA
import Spike.Lib.LowerA64.HproSetupPA
import Spike.Lib.LowerA64.PinnedTcbA

namespace Spike.Lib.LowerA64

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
open Spike.Lib.A64.Flow.Ret0 (LimOk WcG CallerCells limA)
open Scc.Sem (ValRep)
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

/-- **`h0InA_setup_assembled`'s `hS` at one invariant and top, from the
placement check** (`setupCallWS_ofPlaceOK` at the instance; draft check):
the setup block `dS` compiled at `jS` of return type `ty`; left the inputs
of `setupCallWS_ofPlaceOK` there, `me`'s word at the table's immediate by
`valRep_meW2_of_placeOKAtA`. -/
theorem hS_assembledA {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) {L : Int} {D1 : Int} {ZU1 : Int64} (J : InvS) (v : BitVec 64)
    {jS : Nat} {dS : Decl} (hdS : (Spike.Lib.LowerNode.compiled2 p)[jS]? = some dS) (hrt : dS.retTy = ty)
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop}
    (hs : FnSpecC2 (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none) (fun _ => 0) (MSS J)
      CxOk (fnCode2OfP hp h jS dS hdS))
    (hu : dS.argTy = .unit) (hna : (fnCode2OfP hp h jS dS hdS).na = 0)
    (hfn : (setupMC (setupWords2 p)).setup = (fnCode2OfP hp h jS dS hdS).fn)
    (hZU : ZU1 = Int64.ofInt (fnCode2OfP hp h jS dS hdS).cx.frame)
    (hcE : ∀ cE fr, CallTo p C0 cE fr → cE = Spike.Lib.Ctl.mk dS.body [(dS.arg, dS.argTy, [])] none)
    (hms : ∀ (fr : TermRun.Frame) a Z', LimOk ((MSS J) []) (FS v) (Ly).exe (Ly).endPc a Z' →
      LimOk ((MSS J) [fr]) (FS v) (Ly).exe (Ly).endPc a Z')
    (hL : PosOff (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (Ly).lab
      ((Ly).lab (proL (fnCode2OfP hp h jS dS hdS).cx)))
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) false ⟨limA TP0, 8⟩ = true)
    (hun : ∀ m, (FS v) m → Mem.loadInt m.dmem (limA TP0) 8 = none)
    (hsub : (rS0 (Ly)).Sub (Ly).Λ.stackPool) (hfit : (rS0 (Ly)).lo + (rS0 (Ly)).size ≤ 2 ^ 64)
    (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, ((swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0).OK →
      ((swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0).base.toNat % 16 = 0 →
      FStable ((swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0) F' →
      (∀ m, F' m → (FS v) m ∧ CallerCells (swR v (-L) 0) (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0 m) →
      ∀ (g : WcG) (fr : TermRun.Frame), g.ra = ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec → g.tp = TP0 →
      CallTo p C0 g.c0 fr → ((swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0).base = g.sp →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isaLSE2),
        CalleePre2R (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none) (fun _ => 0) (MSS J)
          CxOk (fnCode2OfP hp h jS dS hdS) (rS0 (Ly))
          ((swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0) F' [fr]
          g.fp g.ra TP0 G0 Ab g.c0 ∧
        FrOk2 g.c0 [fr] ∧ SegWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none) (MSS J) Ab
          (fun _ _ _ => False)) :
    SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec C0 (TP0) := by
  have hc0 : C0 = Spike.Lib.Ctl.mk Scc.Sem.SrcSem.setupTerm [("me", .ptr .pub .void,
      [meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))]), ("u", .unit, [])] none := by
    simp only [th02, hty]
  rw [← hrt]
  exact setupCallWS_ofPlaceOK hp h (Λw := (Ly).Λ) hdS hs hu hna hfn hZU hc0 hcE hms hL
    (Spike.Lib.LowerNode.imms2Me_setupK hty) (valRep_meW2_of_placeOKAtA h _) hmr hun hsub hfit hpN hpre

end Assembled

/-- info: 'Spike.Lib.LowerA64.hS_assembledA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hS_assembledA

end Spike.Lib.LowerA64
