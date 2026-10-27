/-
**`scc_rt_main`'s segment from the marshalling block at any current
placement** (x86-64): a setup bottom key's `h0`
(`Spike/Test/X64Hello1BotH.lean`) inside `W2AtL` / `MSAtL`
(`Spike/Lib/LowerX64/RtMainXRL.lean`) at a current placement `L0`, `ls`
some allocations past the start's, at the switch region's frame condition
with `WordsNone`: `mainS0_segSwF` (`Spike/Lib/Rt/X64MainS0Sw.lean`) at the
first stack's top, its own obligations from `mainSW_ofPlaceOKRL`'s
marshalling block (`sp0`, the user function's post unused) and
`hWx_ofPlaceOKVL`'s exit tail, both moved to `WordsNone` by `monoF`, the
limit word's facts at the placement's level (`limOk_lvl_ofPlaceOK`), the
frame condition stable (`wordsNone_swFSL_fstable`). At any other top the
frame condition is empty (`swF`), so the segment is.

- `mainS0_segL`: the segment at every top `v`; left: the record's code and
  phase facts, the controls' facts back from the setup block (`hC0`,
  `hCS`, `hQ0`, `hQS`, `hPlS`) and the user function (`hov`, `hQP`), the
  placement's reach (`hR`), the user frame's room (`hZU`), the user call
  (`hU`) and the exit (`hexit`).
-/
import Spike.Lib.LowerX64.RtMainXVL
import Spike.Lib.LowerX64.LimLvl2
import Spike.Lib.Rt.X64MainS0Sw
import Spike.Lib.Rt.X64SwWordsNone
import Spike.Lib.Rt.X64WMonoF

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64
open A9NoSpawn Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At swR FStable)
open Spike.Lib.X64.Flow (XExitW)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.AllocReach (Reach)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.X64.Rt (MainCallWSF SetupArgs swFSL oU rS0 setupMC rtCodeOkS mainS0R mainS0 mainSRR CFactsC
  arOf marshal MainExitFA)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i

/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`. -/
local notation "FW" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

/-- **`scc_rt_main`'s segment from the marshalling block inside `W2AtL`
at a current placement `L0`, `ls`**, at every top `v` of the switch
region (a setup bottom key's `h0`): at the first stack's top
`mainS0_segSwF` at `Fw := WordsNone`, its marshalling block from
`mainSW_ofPlaceOKRL` (`sp0`; the user function's post `False`), its exit
tail from `hWx_ofPlaceOKVL`, the limit word's facts at `L0`, `ls` from
the placement's reach (`hR`, `limOk_lvl_ofPlaceOK`); elsewhere empty. -/
theorem mainS0_segL {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {L0 : Lbl} {ls : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int}
    (hp : ProgNoS ZBad p) (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64}
    (hL2 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D2 ≤ L)
    (hR : Reach (arOf Λ) (fun _ => none) (fun _ => 0) L0 ls)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU2.toBitVec).toNat)
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0) (hCS : ∀ c rs, PostS c rs → CFactsC c)
    (hQ0 : MainCtl (Ly).Λ L0 c0) (hQS : ∀ c rs, PostS c rs → MainCtlC c [])
    (hQP : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ L0 c fs v)
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ L0 s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (RS (TOP))
      (fun m => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) (TOP) m ∧ CallerCells (swR (TOP) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0R (Ly).lab (setupMC sw) PostS ⟨TOP - 8#64, TP0, c0⟩ (TP0).toBitVec)
      (marshal (setupMC sw).sw (setupMC sw).fn))
    (hU : MainCallWSF (W2AtL h i p rd (rS0 (Ly)) J Dt ls0 L0 ls) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly)))
      p L0 (MSAtL h i p rd J ab ls0 L0 ls) (Ly).exe (Ly).endPc (RS (TOP)) (FW (TOP))
      (setupMC sw).fn (setupMC sw).Z D2 ZU2 (SetupArgs PostS (setupMC sw).sw (TP0).toBitVec) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (TP0))
    (hexit : ∀ s c fs (w : BitVec 64), Post c fs w →
      Spike.Lib.X64.At (Ly).exe (Ly).endPc (RS (TOP)) (FW (TOP))
        ⟨(Ly).lab (setupMC sw).sp1 + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5, oU (setupMC sw).Z,
          fun σ _ => σ.regs.rdi.toBitVec = w⟩ s c →
        MainExitFA p (MSAtL h i p rd J ab ls0 L0 ls []) s c fs w.toNat)
    {Q : FragS isa} (v : BitVec 64) :
    SegWS (W2AtL h i p rd (rS0 (Ly)) J Dt ls0 L0 ls) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p L0
      (MSAtL h i p rd J ab ls0 L0 ls)
      ((Spike.Lib.X64.At (Ly).exe (Ly).endPc (RS v) (FW v)
        (mainS0 (Ly).lab (setupMC sw) PostS ⟨TOP - 8#64, TP0, c0⟩ (TP0).toBitVec)).at []) Q := by
  by_cases hv : v = TOP
  case neg =>
    exact SegWS.empty fun _ _ _ ⟨⟨_, _, _, _, _, _, hF, _⟩, _⟩ => hv hF.1.2.1.1
  subst hv
  have hwf := Scc.Cert.PlaceOK.X64.wf_link_of_placeOKAt i h
  have hL0 : (0 : Int) ≤ L := by omega
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  have hin := Spike.Lib.X64.Rt.mainSIn_of_okS hc
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm
  have hLZ : 8 + 8 + (setupMC sw).Z.toInt + 8 ≤ L := by omega
  have hW := mainSW_ofPlaceOKRL h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (ls := ls) (ab := ab)
    (Post := fun _ _ => False) hp hL hLm hL8 hsw hc hph hgrow hset hfn hLZ hC0 hCS (fun _ _ h => h.elim)
    hQ0 hQS (fun _ _ h => h.elim) hPlS
    ⟨Spike.Lib.X64.Rt.BlkW.ofSt fun _ _ hJ _ => hJ.1.elim,
      Spike.Lib.X64.Rt.NodeW.ofSt fun _ _ ⟨_, _, hJ, _⟩ _ => hJ.1.elim⟩ (TOP)
  have hWx := hWx_ofPlaceOKVL h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (ls := ls) hp hL hLm hL8 hsw hc
    hph hgrow hset hfn hLZ hC0 hov hQP (TOP)
  exact Spike.Lib.X64.Rt.mainS0_segSwF (Ly).lays rfl hin (by rw [hZ]; omega) (show sw ≤ 5 by omega)
    (by show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega)
    (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, hk]; refine ⟨?_, ?_, ?_⟩ <;> omega)
    hD20 hD28 hL2 hL8 msOfAX_K_abi (rS := rS0 (Ly))
    (pinA (Ly).lab + 0#64 + 8#64) (TOP) (TOP) c0 (TP0).toBitVec hok
    (Spike.Lib.X64.Rt.wordsNone_swFSL_fstable hwf (Spike.Lib.X64.Rt.rS0_sub _) hok hL hL8
      (by rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ hL0 hLm)
      (by rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _)
      (by rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hLm)
      (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)))
    (limOk_lvl_ofPlaceOK h i hR hZU) hU hexit
    (hW.sp0.monoF fun _ hm => ⟨hm.1.2, hm.2⟩) (fun fs => (hWx fs).monoF fun _ hm => ⟨hm.1.2, hm.2⟩)

end Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainS0_segL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainS0_segL
