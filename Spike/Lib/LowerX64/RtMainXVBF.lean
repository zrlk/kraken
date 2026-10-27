/-
**`h0` at the setup call's known frame condition with an extra frame `Fw`
after the switch** (x86-64): `h0_ofPlaceOK_setupFVB`
(`Spike/Lib/LowerX64/RtMainXVB.lean`) over `startSF_segWSFB`
(`Spike/Lib/Rt/X64MainSSBF.lean`): the setup call `hS` and the user
function's call `hU` at the frame `(Fw ∧ swFSL) ∧ CallerCells`, so that
their proofs may use a fact `Fw` of the entry's memory (`hFw`) kept by the
writes in the switched stack (`hFwS`); the runtime's own obligations, proved
at `swFSL`, moved by `Spike/Lib/Rt/X64WMonoF.lean`.

- `h0_ofPlaceOK_setupFVBF`: `h0_ofPlaceOK_setupFVB` at the extra frame `Fw`.
-/
import Spike.Lib.LowerX64.RtMainXVB
import Spike.Lib.Rt.X64MainSSBF
import Spike.Lib.Rt.X64WMonoF

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (NodeW BlkW ND At)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add' xExit xExit_ok prologueIn exitIn XExitW)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk setupMC MainSW mainSIn marshal blkW_postO nodeW_syscall_postO mainSRR)
open Spike.Lib.X64.Rt.MainU (xExit_noRet)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i

open A9NoSpawn Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable)
open Spike.Lib.LowerNode (FrOk2 ZBad)

open Spike.Lib.X64.Flow.Ret0 (stacksA)
open Spike.Lib.X64.Rt (arOf)
open Spike.Lib.X64.AllocG (BlkW.imp NodeW.imp)

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (SetupCode SetupCallWSB SetupGF MainCallWSF MainSW SetupArgs swFSL mainSIn oU rS0 entryR
  rtF setupMC rtCodeOkS mainS0R mainSRR CFactsC) in
open Spike.Lib.AllocReach (IN) in
/-- **`h0_ofPlaceOK_setupFVB` with the extra frame `Fw` after the switch**:
`hS`, `hU` at `(Fw ∧ swFSL) ∧ CallerCells`, given `Fw` of the entry's
memory (`hFw`) and `FStable` with `swFSL` in the switched stack (`hFwS`). -/
theorem h0_ofPlaceOK_setupFVBF {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (takeMem pm (rS0 (Ly)) m))
    {Fw : _root_.Mem 64 → Prop} (hFw : ∀ m, FE m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
      (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m))
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 c0 []) (hov : ¬ OvfReady c0) (hC0 : CFacts (Ly).Λ lbl0 c0)
    (hpl0 : ∀ s, PlacedS (Ly).Λ (fun _ => none) s c0 [])
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hPostS : ∀ c rs, PostS c rs → CFactsC c ∧ MainCtlC c [])
    (hPU : ∀ c fs v, Post c fs v → UPostRF p (fun _ => none) c fs v)
    (hPost : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ (fun _ => none) c fs v)
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0R (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
      (marshal (setupMC sw).sw (setupMC sw).fn))
    (hL1 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU2.toBitVec).toNat)
    (hS : ∀ v, SetupCallWSB (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).sp0).toBitVec c0
      (tpOf (pinA (Ly).lab + 0#64 + 8#64))
      (SetupGF p (Ly).lab (MSAt h i p rd J ab ls0 []) ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
            (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
          CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
        (setupMC sw) D1 ZU1 ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.X64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hD8 : 8 ≤ D1) {chk entry : Label} {Zs lim : Int64} {Lg : Label} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)}
    (hproS : Spike.Lib.X64.Flow.prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg zl zf z1 z2 zs ps = true)
    (hphS : blkPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab (setupMC sw).setup + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true)
    (hlS : (setupMC sw).setup ∉ Spike.Lib.X64.AllocG.abLabs) (hlcS : chk ∉ Spike.Lib.X64.AllocG.abLabs)
    (hU : ∀ v, MainCallWSF (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2
      (SetupArgs PostS (setupMC sw).sw (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (tpOf (pinA (Ly).lab + 0#64 + 8#64))) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.X64.At (Ly).exe (Ly).endPc (entryR E) FE (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  have hin := Spike.Lib.X64.Rt.mainSIn_of_okS hc
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hL0 : (0 : Int) ≤ L := by omega
  have hW0 := mainSW_ofPlaceOKR h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (ab := ab)
    (Post := fun _ _ => False) hp hL hLm hL8 hsw hc hph hgrow hset hfn (by omega) hC0
    (fun c rs h => (hPostS c rs h).1) (fun _ _ h => h.elim) ⟨hf0, hov, hpl0⟩ (fun c rs h => (hPostS c rs h).2)
    (fun _ _ h => h.elim) hPlS
    ⟨Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ => hJ.1.elim, Spike.Lib.X64.Rt.NodeW.ofSt fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.elim⟩
  have hWx := hWx_ofPlaceOKV h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) hp hL hLm hL8 hsw hc hph
    hgrow hset hfn (by omega) hC0 hov hPost
  have hWs : ∀ v, MainSW (Spike.Lib.X64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (MSAt h i p rd J ab ls0 [])
      (setupMC sw) PostS (fun c v => Post c [] v)
      ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec := fun v =>
    ⟨(hW0 v).pro, (hW0 v).call0, (hW0 v).sp0, hWx v []⟩
  have hFF : ∀ v m, ((Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
      (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
      swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m :=
    fun _ _ h => ⟨h.1.2, h.2⟩
  have hpl : ∀ s c, Placed (Ly).Λ (fun _ => none) s c → (MSAt h i p rd J ab ls0 []).pl s c := by
    intro s c hP; cases ab <;> exact ⟨rfl, hP⟩
  obtain ⟨hhdr, htcb, hfld, htk⟩ := rows_ofPlaceOK h i (p := p) (rd := rd) (ar := arOf (Ly).Λ)
    (J := IN (arOf (Ly).Λ) (fun _ => none) ls0 J) (ab := ab) (lsize := ls0) hFE
  have h8 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm
  exact Spike.Lib.X64.Rt.startSF_segWSFB (Ly).lays rfl (Spike.Lib.X64.Rt.rtCodeTi_of_placeOKAt h) msOfAX_K_abi hFEs
    (Spike.Lib.X64.Rt.entryR_ok hE) (Spike.Lib.X64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) 0#64 0#64 c0 (by decide) hhdr htcb (by decide) hfld htk hok
    (by rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ hL0 hLm)
    (hun_ofPlaceOK h i hFE) hFw hFwS (Spike.Lib.X64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub) hFEk
    (Spike.Lib.X64.Rt.StartEW.toF (startEW_w2G h i (lbl0 := lbl0) (J := IN (arOf (Ly).Λ) (fun _ => none) ls0 J)
      (Dt := Dt) (lsize := ls0)
      hp hf0 hov hC0 (Spike.Lib.X64.Rt.entryR_ok hE) (by show (-65536 : Int) ≤ -304; decide)
      (by show (0 : Int) ≤ 0; decide) hFE (by rw [Spike.Lib.X64.Rt.stacksA_lab0]) hsub
      (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub) h8 hok hL hL8 (by decide) hpl0) Fw)
    hin (by rw [hZ]; omega) (show sw ≤ 5 by omega) (by show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega)
    (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, hk]; refine ⟨?_, ?_, ?_⟩ <;> omega)
    hD10 hD18 hD20 hD28 hL1 hL2 hL8 (limOk_ofPlaceOK h i hZM) (limOk_ofPlaceOK h i hZS) (limOk_ofPlaceOK h i hZU)
    hS hcall hPS (fun v s c hA => hWC_ofPlaceOK h i hp hL hLm hL8 hsw hD8 hL1 hproS hphS hlS hlcS hC0
      ⟨hf0, hov, hpl0⟩ v s c (hA.monoF (hFF v))) hU
    (fun R' F' s c fs v hP hAt => uPostRF_exit (Λ := (Ly).Λ) hpl R' F' s c fs v (hPU c fs v hP) hAt)
    (fun v => (hWs v).monoF (hFF v)) (fun v fs => (hWx v fs).monoF (hFF v))

end Place

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerX64.h0_ofPlaceOK_setupFVBF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0_ofPlaceOK_setupFVBF

end Spike.Lib.LowerX64
