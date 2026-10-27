/-
**The consumer's `h0` with a setup block at the setup call's known frame
condition** (AArch64): `h0_ofPlaceOK_setupFR`
(`Spike/Lib/LowerA64/RtMainXR.lean`) with the setup block's `hS` at
`SetupCallWSB` and the callee's frame condition `SetupGF`
(`Spike/Lib/Rt/A64MainSSB.lean`), so a consumer of the setup call's segment
sees the frame condition `call_ndSG` runs the callee under.

- `h0_ofPlaceOK_setupFRB`: `h0_ofPlaceOK_setupFR` through `startS_segWSFB`.
-/
import Spike.Lib.LowerA64.RtMainXR
import Spike.Lib.Rt.A64MainSSB

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (InstOk SetupCode setupMC MainSW mainSIn)
open Spike.Lib.A64.Rt.MainS (MainPhS)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.AllocReach (IN)
open Scc.Sem.A64 (abi pcOf)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {lbl : Lbl} {lab : Label → Int64}

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (SetupCallWSB SetupGF MainCallWSF SetupArgs swFSL rS0 entryR rtF) in
/-- **`h0_ofPlaceOK_setupFR` at the setup call's known frame condition**
(`Spike/Lib/Rt/A64MainSSB.lean`): the setup block's `hS` at `SetupCallWSB`
with the callee's frame condition `SetupGF` (the ghost frame condition of
`call_ndSG` at `mainSC`), threaded by `startS_segWSFB`; the rest as
`h0_ofPlaceOK_setupFR`. -/
theorem h0_ofPlaceOK_setupFRB {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (takeMem pm (rS0 (Ly)) m))
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0) (hC0 : CFacts (Ly).Λ lbl0 c0)
    (hpl0 : ∀ s, PlacedS (Ly).Λ (fun _ => none) s c0 [])
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
    (hPost : ∀ c fs v, Post c fs v → CFactsC c ∧ MainCtlC c fs)
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (pinA (Ly).lab + 0#64 + 8#64))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
    (hPlX : ∀ fs, ExitW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c fs)
      (fun _ _ => False) (Ly).exe (Ly).endPc (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (Spike.Lib.A64.Rt.mainSR (Ly).lab (setupMC sw) (fun c v => Post c fs v)) (setupMC sw).k)
    (hS : ∀ v, SetupCallWSB (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).e0 + 4).toBitVec c0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))
      (SetupGF p (Ly).lab (MSAt h i p rd J ab ls0 []) (Ly).exe (Ly).endPc (swR v (-L) 0)
        (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (setupMC sw) D1 ZU1
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.A64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.A64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', Spike.Lib.FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    {chk entry : Label} {Zs lim : Int64} {Lg : Label} {ps : List (XReg × Int64)}
    (hproS : prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg ps = true)
    (hphS : blkPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab chk + Int64.ofNat (4 * 0)) 0 (chkHead Zs) = true)
    (hlS : chk ∉ abLabs)
    (hU : ∀ v, MainCallWSF (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2 (SetupArgs PostS (setupMC sw).sw (pinA (Ly).lab + 0#64 + 8#64)) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (entryR E) FE (entryN (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hZ := setupMC_Z sw hsw
  have hW := mainSW_ofPlaceOKR h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (ab := ab) hp hL0 hL hL8 hsw hc
    hph hgrow hset hfn (by omega) hC0 (fun c rs h => (hPostS c rs h).1) (fun c v h => (hPost c [] v h).1)
    ⟨hf0, hov, hpl0⟩ (fun c rs h => (hPostS c rs h).2) (fun c v h => (hPost c [] v h).2) hPlS (hPlX [])
  have hWx := hWx_ofPlaceOKR h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) hp hL0 hL hL8 hsw hc hph
    hgrow hset hfn (by omega) hC0 (fun c fs v h => (hPost c fs v h).1) (fun c fs v h => (hPost c fs v h).2) hPlX
  have h16 : (setupMC sw).Z.toInt % 16 = 0 := by rw [hZ]; omega
  have hZ16 : 16 ≤ (setupMC sw).Z.toInt := by rw [hZ]; omega
  have hZw : 8 * ((setupMC sw).sw : Int) + 8 ≤ (setupMC sw).Z.toInt := by
    show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega
  have hk : Spike.Lib.offOk (-(setupMC sw).Z.toInt) 0 (-(setupMC sw).Z.toInt + (setupMC sw).k.toInt) = true := by
    simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, setupMC_k sw hsw]; refine ⟨?_, ?_, ?_⟩ <;> omega
  have hsw7 : (setupMC sw).sw ≤ 7 := show sw ≤ 7 by omega
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hSM := stackM_rS0 (Ly) hE
  obtain ⟨hhdr, htcb, hfld, htk⟩ := rows_ofPlaceOK h i (p := p) (rd := rd) (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
    (J := IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) ls0 J) (ab := ab) (lsize := ls0) hFE
  have h16t : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
  exact Spike.Lib.A64.Rt.startS_segWSFB (Ly).lays rfl (Spike.Lib.A64.Rt.rtCode0_of_placeOKAt h) msOfAX_K_abi hFEs
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) 0#64 0#64 c0 (by decide) hhdr htcb (by simp) hfld htk h16t hok
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ hL0 hL)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_houtD _ hL0 hL)
    (hun_ofPlaceOK h i hFE) (Spike.Lib.A64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)
    (Spike.Lib.A64.Rt.outS_of_sub _ hE hsub) hFEk
    (startEW_w2G h i (lbl0 := lbl0) (J := IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) ls0 J)
      (Dt := Dt) (lsize := ls0) (L := L) hp hf0 hov hC0 (Spike.Lib.A64.Rt.entryR_ok hE)
      (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide) hFE
      (rS0_eq_lab _) hsub hSM.1 hSM.2.1 hSM.2.2 (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) h16t hok hL8 (by simp)
      hpl0)
    (Spike.Lib.A64.Rt.mainSIn_of_okS hc) h16 hZ16 hsw7 hZw hk
    hD10 hD18 hD20 hD28 hL1 hL2 (limOk_ofPlaceOK h i hZM) (limOk_ofPlaceOK h i hZS) (limOk_ofPlaceOK h i hZU) hS
    hcall hPS (hWC_ofPlaceOK h i (sc := setupMC sw) hp hL0 hL hL8 hproS hphS hlS hC0 ⟨hf0, hov, hpl0⟩) hU
    (fun R' F' s c fs v hP hAt => uPostRF_exit R' F' s c fs v (hPU c fs v hP) hAt) hW hWx

end Place

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerA64.h0_ofPlaceOK_setupFRB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0_ofPlaceOK_setupFRB

end Spike.Lib.LowerA64
