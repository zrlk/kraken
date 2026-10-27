/-
**`scc_rt_main` after the setup block's return at any current placement**
(AArch64; the twin of `Spike/Lib/LowerX64/MainS0L.lean`): `mainS0_segWSF`
(`Spike/Lib/Rt/A64MainS0.lean`) at `W2AtL` / `MSAtL`
(`Spike/Lib/LowerA64/RtMainXRL.lean`), the current placement `L0`, `ls`
reachable from the empty one, at the switch region and its frame condition
with `WordsNone` (`WordsNone ∧ swFSL`, a setup bottom key's `BotH`). The
segment a setup bottom key's `h0` asks (`Spike/Test/A64Hello1BotRes.lean`).

- `mainS0_segL`: from `mainS0` at `[]`, a segment to any `Q`, given the user
  function's call `hU` and its exit `hexit` at `L0`, `ls`: the marshalling
  block from `mainSW_ofPlaceOKRL`, the exit tail from `hWx_ofPlaceOKVL`
  (both under the stronger frame, `blkW_mono`, `nodeW_mono`), the limit
  word's facts at depth (`limOk_lvl_ofPlaceOK`), the frame `FStable`
  (`wordsNone_swFSL_fstable`); off the first stack's top no state is in the
  frame condition.
-/
import Spike.Lib.LowerA64.RtMainXVLA
import Spike.Lib.LowerA64.LimLvl2
import Spike.Lib.Rt.A64MainS0
import Spike.Lib.Rt.A64SwWordsNone

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (InstOk SetupCode setupMC MainSW mainSIn)
open Spike.Lib.A64.Rt.MainS (MainPhS)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.AllocReach (IN Reach)
open Scc.Sem.A64 (abi pcOf)
open Spike.Lib.A64.Flow.Ret0 (blkW_mono nodeW_mono)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB's address. -/
local notation "XT" => Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (XT)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v` (`BotH`'s). -/
local notation "FW" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  Spike.Lib.A64.Rt.swFSL L (Spike.Lib.A64.Rt.rS0 (Ly)) (TOP) (Spike.Lib.A64.Flow.Ret0.limA (TP0)) v m

set_option hygiene false in
/-- `W2AtL` at the current placement. -/
local notation "W2L" => W2AtL h i p rd (Spike.Lib.A64.Rt.rS0 (Ly)) J Dt ls0 L0 ls

set_option hygiene false in
/-- `MSAtL` at the current placement. -/
local notation "MSL" => MSAtL h i p rd J ab ls0 L0 ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (swFSL rS0 MainCallWSF SetupArgs MainExitFA) in
/-- **`scc_rt_main` from the marshalling block at a current placement `L0`,
`ls`** (`mainS0_segWSF` at `W2AtL`, `MSAtL`, the frame with `WordsNone`):
at a placement reachable from the empty one (`hR`) and the user frame's room
(`hZU`), the start control's facts (`hC0`, `hov`, `hQ0`), the setup post's
controls (`hCS`, `hQS`) placed at the marshalling block (`hPlS`), the
user function's post's controls (`hQP`), its call (`hU`) and exit
(`hexit`) at the first stack's top: the segment from `mainS0` at `[]` to any
`Q`, at every top `v`. -/
theorem mainS0_segL {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {L0 : Lbl} {ls : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int}
    (hp : ProgNoS ZBad p) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) (hL2 : (setupMC sw).Z.toInt + D2 ≤ L) {ZU2 : Int64}
    (hR : Reach (Spike.Lib.A64.Rt.arOf Λ) (fun _ => none) (fun _ => 0) L0 ls)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (TOP - (setupMC sw).Z.toBitVec - ZU2.toBitVec).toNat)
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0) (hCS : ∀ c rs, PostS c rs → CFactsC c)
    (hQ0 : MainCtl (Ly).Λ L0 c0) (hQS : ∀ c rs, PostS c rs → MainCtlC c [])
    (hQP : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ L0 c fs v)
    (hPlS : BlkW (fun s c => Placed (Ly).Λ lbl0 s c ∧ PlacedS (Ly).Λ L0 s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc (swR (TOP) (-L) 0) (swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) (TOP))
      (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS ⟨TOP, TP0, c0⟩ (XT))
      (Spike.Lib.A64.Rt.marshal (setupMC sw).sw (setupMC sw).fn))
    (hU : MainCallWSF (W2L) (KT) p L0 (MSL) (Ly).exe (Ly).endPc (swR (TOP) (-L) 0) (FW (TOP))
      (setupMC sw).fn (setupMC sw).Z D2 ZU2 (SetupArgs PostS (setupMC sw).sw (XT)) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (TP0))
    (hexit : ∀ s c fs (v : BitVec 64), Post c fs v →
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (swR (TOP) (-L) 0) (FW (TOP))
        ⟨(Ly).lab (setupMC sw).sp1 + 4 + 4 + 4, ⟨-(setupMC sw).Z.toInt, []⟩,
          fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → MainExitFA p ((MSL) []) s c fs v.toNat)
    {Q : FragS isaLSE2} (v : BitVec 64) :
    SegWS (W2L) (KT) p L0 (MSL)
      ((Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (swR v (-L) 0) (FW v)
        (Spike.Lib.A64.Rt.mainS0 (Ly).lab (setupMC sw) PostS ⟨TOP, TP0, c0⟩ (XT))).at []) Q := by
  by_cases hv : v = TOP
  case neg => exact SegWS.empty fun _ _ _ ⟨⟨_, _, _, _, _, _, hF, _⟩, _⟩ => hv hF.2.1.1
  subst hv
  haveI := (Ly).valid
  have hZ := setupMC_Z sw hsw
  have hL0 : 0 ≤ L := by omega
  have hwf : (Ly).Λ.WF := Scc.Cert.PlaceOK.A64.wf_link_of_placeOKAt (i := i) h
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
  have h16 : (TOP).toNat % 16 = 0 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  have hFS : FStable (swR (TOP) (-L) 0) (FW (TOP)) :=
    Spike.Lib.A64.Rt.wordsNone_swFSL_fstable hwf (Spike.Lib.A64.Rt.rS0_sub _) hok (by omega) hL8
      (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ hL0 hL)
      (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
      (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_houtD _ hL0 hL)
      (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _))
  have hWR := mainSW_ofPlaceOKRL h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (L0 := L0) (ls := ls) (ab := ab)
    (Post := fun _ _ => False) hp hL0 hL hL8 hsw hc hph hgrow hset hfn (by omega) hC0 hCS
    (fun _ _ h => h.elim) hQ0 hQS (fun _ _ h => h.elim) hPlS
    ⟨fun _ _ _ _ _ _ _ _ _ hJ => hJ.elim, fun _ _ ⟨_, _, _, _, _, _, _, _, _, hJ, _⟩ => hJ.elim⟩ (TOP)
  have hWx := hWx_ofPlaceOKVL h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (L0 := L0) (ls := ls) hp hL0 hL hL8
    hsw hc hph hgrow hset hfn (by omega) hC0 hov hQP (TOP)
  have hlim := limOk_lvl_ofPlaceOK h i (p := p) (rd := rd) (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
    (J := IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) ls0 J) (ab := ab) (fs := []) hR hZU
  exact Spike.Lib.A64.Rt.mainS0_segWSF (Ly).lays rfl (Spike.Lib.A64.Rt.mainSIn_of_okS hc) (by rw [hZ]; omega)
    (by rw [hZ]; omega) (show sw ≤ 7 by omega) (by show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega)
    (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, setupMC_k sw hsw]; refine ⟨?_, ?_, ?_⟩ <;> omega)
    hD20 hD28 msOfAX_K_abi hFS hok h16 (by show -L ≤ _; omega) (Int.le_refl _) ⟨TOP, TP0, c0⟩ (XT)
    ⟨hlim.rt, hlim.mp, fun _ hm => hm.2.1.2, hlim.room⟩ hU hexit (blkW_mono hWR.sp0 fun _ h => h.2)
    fun fs => ⟨blkW_mono (hWx fs).w0 fun _ h => h.2, nodeW_mono (hWx fs).w1 fun _ h => h.2⟩

end Place

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.mainS0_segL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainS0_segL
