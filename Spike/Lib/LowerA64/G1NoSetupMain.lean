/-
**`scc_rt_main` without a setup block inside `W2`** (AArch64; the bare
twin of `Spike/Lib/LowerA64/RtMainX.lean` and
`Spike/Lib/LowerA64/RtMainXVA.lean`): its own states (`MainUW`,
`Spike/Lib/Rt/A64Main.lean`) at `bareMC` inside the runtime's world `RtM`,
and with `SFacts` (`mainUW_gen`, `Spike/Lib/Rt/A64RtMainU.lean`) and the
source controls' facts inside `W2`. The prologue and `bl wc_main` run at the
start control; the `exit_group` tail at `main`'s returned controls, held
at pending frames and placed by the value (`MainCtlV`).

- `exitW_sfactsAtU`: the tail's states carry `SFacts` at a fixed control
  `cs` with `CFacts cs`, for any post (`exitW_sfactsAt` at `mainUIn`);
- `bareMC_blks`: `bareMC`'s blocks' labels and falls-through, its labels
  none of the write abort's;
- `mainUW_rtM`: `MainUW` inside `RtM` at `bareMC`, for any program with its
  code (`mainUIn`) and the runtime's, its phase facts, the growth path and
  the user function positioned off the write abort (`hgrow`, `hfn`), the
  limit word unloaded (`hun`);
- `MainUW.ofCtl`, `MainUW.imp`: `MainUW` of a control predicate from the
  node invariants'; `MainUW` inside `W` from two;
- `mainUW_ofPlaceOKU`: the prologue and the call inside `nilW W2At` at a
  placed output at the start control's `MainCtl`, the exit given;
- `hWx_ofPlaceOKU`: the exit tail inside `W2At` at every frames, at held
  controls placed by the value (`hWx_ofPlaceOKV` at `bareMC`).
-/
import Spike.Lib.LowerA64.RtMainXVA

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff MainG limA)
open Scc.Cert.Rt.A64 (blockAt)
open MainU

section Exit

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}

/-- **The `exit_group` tail's states without a setup block carry `SFacts`
at a fixed control `cs`** (`CFacts cs`, `hC`), for any post `Post`:
`mainUW_gen`'s exit part at the nodes with their controls replaced by `cs`
(`exitW_sfactsAt` at `mainUIn`). -/
theorem exitW_sfactsAtU {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {mc : MainCode} (hin : mainUIn prog mc = true) {Post : Ctl → BitVec 64 → Prop} {cs : Ctl}
    (hC : CFacts Λ lbl cs) (hph : MainPh okPc ph lab mc)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -mc.Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (h16 : mc.Z.toInt % 16 = 0) (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    ExitW (fun s _ => SFacts Λ μ own rS Tk lbl s cs) K exe endPc R F
      (mainUR (_root_.Executable.labels exe).label mc Post) mc.k := by
  have h := hin
  simp only [mainUIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨-, bEx, bSvc⟩ := h
  have hR8 : R.base.toNat % 8 = 0 := by omega
  rw [hI.labOk]
  refine ⟨BlkW.ofStar (W := fun s c => SFacts Λ μ own rS Tk lbl s c) (cs := cs) ?_,
    NodeW.ofStar (W := fun s c => SFacts Λ μ own rS Tk lbl s c) (cs := cs) ?_⟩
  · exact blkW_postO hI bEx (ofNat4_zero _) (exitTail_ok (lo := -mc.Z.toInt) (hi := 0) hk
        (by show (-mc.Z.toInt) % 16 = 0; omega)) hR hal hlo hhi (fun _ _ h => h.1 ▸ hC)
      hph.ex (fun _ _ _ k hk r hr => (noRet_false (exitTail_noRet _) k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub
      hfit hFO
  · exact nodeW_svc_postO hI bSvc rfl (pc3 _).symm (fun _ _ h => h.1 ▸ hC) hph.svc.1
      hph.svc.2 hR hR8 hl hh hsub hFO (fun _ _ ⟨_, _, hx, _⟩ => by rw [hx]; decide)

end Exit

end Spike.Lib.A64.Rt

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (InstOk MainCode MainUW mainUIn bareMC)
open Spike.Lib.A64.Rt.MainU (MainPh chkHead_noRet chkBr_noRet blD_noRet exitTail_noRet pc2 pc3 pc5)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Scc.Cert.Rt.A64 (blockAt label_labelGap)
open Scc.Sem.A64 (abi pcOf)

/-- **`bareMC`'s blocks' closed facts**: the prologue's, the call's and the
tail's labels and falls-through, the labels of `scc_rt_main` none of the
write abort's. -/
theorem bareMC_blks :
    blkLabs (chkHead bareMC.Z) = [] ∧ blkLabs (chkBr bareMC.grow) = [bareMC.grow] ∧
    blkLabs (frameSet bareMC.Z [(.X0, 0)]) = [] ∧ blkLabs [blD bareMC.fn] = [bareMC.fn] ∧
    lastFalls [blD bareMC.fn] = false ∧ blkLabs (exitTail bareMC.k) = [] ∧ bareMC.sc ∉ abLabs ∧
    bareMC.e0 ∉ abLabs ∧ bareMC.sp0 ∉ abLabs := by
  decide

/-- `bareMC`'s frame is 48. -/
theorem bareMC_Z : bareMC.Z.toInt = 48 := by decide

/-- `bareMC`'s result slot is 8. -/
theorem bareMC_k : bareMC.k.toInt = 8 := by decide

section Main

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {lab : Label → Int64}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {own : Own} {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat}
  {R : Region} {F : MachineData → Prop}

set_option maxHeartbeats 800000 in
/-- **`scc_rt_main`'s own states without a setup block are inside `RtM`**
(`MainUW` at `bareMC`; `mainSW_rtM` without the setup call), for any
program with its code (`hin`) and the runtime's (`hpr`, `hab`): its phase
facts (`hph`), the growth path and the user function positioned off the
write abort (`hgrow`, `hfn`), in any 16-aligned region holding its frame
(`hlo`, `hhi`), the limit word unloaded under the frame condition
(`hun`). -/
theorem mainUW_rtM {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hin : mainUIn prog bareMC = true)
    (hph : MainPh okPc ph lab bareMC) (hgrow : PosOff prog lab (lab bareMC.grow))
    (hfn : PosOff prog lab (lab bareMC.fn))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -bareMC.Z.toInt) (hhi : 0 ≤ R.hi)
    {ms : MemSide isaLSE2} {Post : Ctl → BitVec 64 → Prop} {g : Spike.Lib.A64.Flow.Ret0.MainG}
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA g.tp) 8 = none) :
    MainUW (RtM μ ar lab) (fun _ _ => False) exe endPc R F ms bareMC Post g := by
  have hZ := bareMC_Z
  have hk := bareMC_k
  obtain ⟨lHd, lBr, lFr, lCall, fCall, lEx, nSc, nE0, nSp0⟩ := bareMC_blks
  have h := hin
  simp only [mainUIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, gE⟩, bCall⟩, -⟩, bEx, bSvc⟩ := h
  have esc := label_labelGap hI.lays hgap
  have ee0 := label_labelGap hI.lays gE
  rw [hI.labOk] at esc ee0
  have h16 : bareMC.Z.toInt % 16 = 0 := by rw [hZ]; decide
  have hZ16 : 16 ≤ bareMC.Z.toInt := by rw [hZ]; decide
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩ <;> rw [hI.labOk]
  · -- the check's head
    refine blkW_rtM hI hpr hab bHd (by rw [esc, ofNat4_zero, ofNat4_zero])
      (chkHead_ok (-bareMC.Z.toInt) 0 _) hR hal hlo hhi hph.hd (chkHead_noRet _) nSc (fun _ => ?_)
      (labs_nil lHd)
    exact posOff_of_blockAt (lab := lab) bLd nSc (i := 0) (by decide)
  · -- the limit's load
    exact nodeW_rtM_ldr hI bLd rfl (by show _ + 4 + 4 = _; rw [esc, ofNat4_zero, pc2]) hph.ld.1
      (by rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']; exact notAb_of_blockAt hI hpr hab bBr nSc (by simp [chkBr]))
      (fun σ c m ⟨_, hJ, he⟩ hF => by
        rw [he, rAddr_chkRegs, Spike.Lib.A64.Flow.Ret0.tcbA_limA hJ.2.2]; exact hun m hF)
  · -- the check's branch
    refine blkW_rtM hI hpr hab bBr (by rw [esc, ofNat4_zero, pc3]; rfl)
      (chkBr_ok (-bareMC.Z.toInt) 0 _ _) hR hal hlo hhi hph.br (chkBr_noRet _) nSc (fun _ => ?_)
      (labs_one lBr hgrow)
    exact posOff_of_blockAt (lab := lab) bFr nSc (i := 0) (by simp [frameSet, frSetup])
  · -- the frame
    refine blkW_rtM hI hpr hab bFr (by rw [esc, ofNat4_zero, pc5]; rfl)
      (frameSet_ok (lo := -bareMC.Z.toInt) (hi := 0) h16 hZ16 (by omega) (Int.le_refl _)
        (by simp [Spike.Lib.offOk]; omega)) hR hal hlo hhi hph.fr (Spike.Lib.A64.Rt.MainU.frameSet_noRet _) nSc (fun _ => ?_)
      (labs_nil lFr)
    have := posOff_of_blockAt (lab := lab) bCall nE0 (i := 0) (by simp)
    rw [Nat.add_zero, ofNat4_zero, ee0] at this
    exact this
  · -- `bl wc_main`
    exact blkW_rtM hI hpr hab bCall (ofNat4_zero _) (okBlk_blD _ _ _ _) hR hal hlo hhi
      (lo := -bareMC.Z.toInt) (hi := 0) hph.call (blD_noRet _) nE0
      (fun h => absurd (fCall.symm.trans h) (by decide)) (labs_one lCall hfn)
  · -- the tail's block
    refine blkW_rtM hI hpr hab bEx (ofNat4_zero _)
      (exitTail_ok (lo := -bareMC.Z.toInt) (hi := 0)
        (by
          show Spike.Lib.offOk _ _ (-bareMC.Z.toInt + bareMC.k.toInt) = true
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hk, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega) (by show (-bareMC.Z.toInt) % 16 = 0; omega))
      hR hal hlo hhi hph.ex (exitTail_noRet _) nSp0 (fun _ => ?_) (labs_nil lEx)
    exact posOff_of_blockAt (lab := lab) bSvc nSp0 (i := 0) (by decide)
  · -- the `exit_group`
    exact nodeW_rtM_exit hI bSvc rfl (pc3 _).symm hph.svc.1 fun _ _ h => h.1

end Main

section Ctl

variable {W W1 W2 : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {Q : Ctl → Prop}

/-- **`scc_rt_main`'s own states without a setup block meet a control
predicate** `Q` of the entry's control (`hC0`) and of every control `Post`
relates (`hP`). -/
theorem MainUW.ofCtl {ms : MemSide isaLSE2} {mc : MainCode} {Post : Ctl → BitVec 64 → Prop}
    {g : Spike.Lib.A64.Flow.Ret0.MainG} (hC0 : Q g.c0) (hP : ∀ c v, Post c v → Q c) :
    MainUW (fun _ c => Q c) (fun _ _ => False) exe endPc R F ms mc Post g :=
  ⟨⟨BlkW.ofCtl fun _ _ hJ => hJ.1 ▸ hC0, NodeW.ofCtl fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hC0,
      BlkW.ofCtl fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0, BlkW.ofCtl fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0⟩,
    BlkW.ofCtl fun _ _ hJ => hJ.1 ▸ hC0,
    ⟨BlkW.ofCtl fun _ _ hJ => hP _ _ hJ, NodeW.ofCtl fun _ _ ⟨_, _, hJ, _⟩ => hP _ _ hJ⟩⟩

/-- **`scc_rt_main`'s own states without a setup block inside `W`** from
two, the second not moved. -/
theorem MainUW.imp {ms : MemSide isaLSE2} {mc : MainCode} {Post : Ctl → BitVec 64 → Prop}
    {g : Spike.Lib.A64.Flow.Ret0.MainG}
    (h1 : MainUW W1 K exe endPc R F ms mc Post g)
    (h2 : MainUW W2 (fun _ _ => False) exe endPc R F ms mc Post g)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : MainUW W K exe endPc R F ms mc Post g :=
  ⟨⟨Spike.Lib.A64.AllocG.BlkW.imp h1.pro.w0 h2.pro.w0 hw, Spike.Lib.A64.AllocG.NodeW.imp h1.pro.w1 h2.pro.w1 hw,
      Spike.Lib.A64.AllocG.BlkW.imp h1.pro.w2 h2.pro.w2 hw, Spike.Lib.A64.AllocG.BlkW.imp h1.pro.w3 h2.pro.w3 hw⟩,
    Spike.Lib.A64.AllocG.BlkW.imp h1.call h2.call hw,
    ⟨Spike.Lib.A64.AllocG.BlkW.imp h1.exit.w0 h2.exit.w0 hw,
      Spike.Lib.A64.AllocG.NodeW.imp h1.exit.w1 h2.exit.w1 hw⟩⟩

end Ctl

/-! ## At a placed output -/

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h i

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (swFSL rS0) in
/-- **`scc_rt_main`'s own states without a setup block inside `W2At`**
(`startUF_segWSF`'s `hW` at `bareMC`) at a placed output: the prologue and
the call from `mainUW_gen` and `mainUW_rtM` at the record, joined by
`rtM_w2` with the start control's `MainCtl` (`hQ0`, `MainUW.ofCtl`); the
exit given (`hWx`). Left: the code and phase facts (`hin`, `hph`), the two
targets positioned off the write abort (`hgrow`, `hfn`), the start
control's `CFacts` (`hC0`), and the frame inside the switch region
(`hLZ`). -/
theorem mainUW_ofPlaceOKU {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    (hin : mainUIn (Ly).prog bareMC = true)
    (hph : MainPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab bareMC)
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.grow))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.fn))
    (hLZ : bareMC.Z.toInt ≤ L) {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hQ0 : MainCtl (Ly).Λ (fun _ => none) c0)
    (hWx : ∀ v, ExitW (Spike.Lib.A64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (Spike.Lib.A64.Rt.mainUR (Ly).lab bareMC Post) bareMC.k) :
    ∀ v, MainUW (Spike.Lib.A64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (MSAt h i p rd J ab ls0 [])
      bareMC Post
      ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩ := by
  intro v
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hZ := bareMC_Z
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
    have h16 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
    have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) false
        ⟨limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
      rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
      exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
    have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
    have HS := Spike.Lib.A64.Rt.mainUW_gen (lbl := lbl0) (Post := fun _ _ => False)
      (ms := MSAt h i p rd J ab ls0 [])
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      hI hin hC0 (fun _ _ h => h.elim) hph
      hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl) (by rw [hZ]; decide) (by rw [hZ]; decide)
      (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, bareMC_k]; refine ⟨?_, ?_, ?_⟩ <;> omega)
      hmr (fun _ hm => hm.1.2) hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (fun _ hm => hm.2)
    have HM := MainUW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Ly).lab s c ∧ MainCtl (Ly).Λ (fun _ => none) c)
      (mainUW_rtM (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ) (Post := fun _ _ => False)
        (ms := MSAt h i p rd J ab ls0 [])
        (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
        (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩) hI
        (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hin hph
        hgrow hfn hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (fun _ hm => hm.1.2))
      (MainUW.ofCtl hQ0 fun _ _ h => h.elim) fun _ _ h1 h2 => ⟨h1, h2⟩
    have HW := MainUW.imp (W := Spike.Lib.A64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0)) HS HM
      fun s c hS ⟨hM, hQ⟩ => rtM_w2 hp hS hM hQ
    exact ⟨HW.pro, HW.call, hWx _⟩
  · exact ⟨(Spike.Lib.A64.Rt.mainUW_ofFalse (Post := Post) (ms := MSAt h i p rd J ab ls0 [])
        (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
        fun m hm => hv hm.1.1).pro,
      (Spike.Lib.A64.Rt.mainUW_ofFalse (Post := Post) (ms := MSAt h i p rd J ab ls0 [])
        (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
        fun m hm => hv hm.1.1).call, hWx v⟩

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (swFSL rS0) in
/-- **The exit tail without a setup block inside `W2At` at every frames,
at held controls placed by the value** (`hWx_ofPlaceOKV` at `bareMC`):
`exitW_sfactsAtU` at the start control `c0` (`hC0`, not at an overflow
`hov`) and `mainUW_rtM`'s exit part, each tail state placing the control
by `x0` (`exitW_placedV`, the post's controls' `MainCtlV` at `fs`, `hQP`),
joined by `rtM_w2V`. -/
theorem hWx_ofPlaceOKU {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    (hin : mainUIn (Ly).prog bareMC = true)
    (hph : MainPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab bareMC)
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.grow))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.fn))
    (hLZ : bareMC.Z.toInt ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0)
    (hQP : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ (fun _ => none) c fs v) :
    ∀ v fs, ExitW (fun s c => W2At h i p rd (rS0 (Ly)) J Dt ls0 s c fs)
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (Spike.Lib.A64.Rt.mainUR (Ly).lab bareMC (fun c v => Post c fs v)) bareMC.k := by
  intro v fs
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hZ := bareMC_Z
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
    have h16 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
    have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
    have H1 := Spike.Lib.A64.Rt.exitW_sfactsAtU (lbl := lbl0) (Post := fun c v => Post c fs v)
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64)) hI hin hC0
      hph hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl) (by rw [hZ]; decide)
      (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, bareMC_k]; refine ⟨?_, ?_, ?_⟩ <;> omega)
      hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (fun _ hm => hm.2)
    have H2 := (mainUW_rtM (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ) (Post := fun c v => Post c fs v)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (ms := MSAt h i p rd J none ls0 [])
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64)) hI
      (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hin hph
      hgrow hfn hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (fun _ hm => hm.1.2)).exit
    have H3 := exitW_placedV (Λ := (Ly).Λ) (L0 := fun _ => none) (fs := fs) (exe := (Ly).exe)
      (endPc := (Ly).endPc) (R := swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0)
      (F := swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64))
      (n := Spike.Lib.A64.Rt.mainUR (Ly).lab bareMC (fun c v => Post c fs v)) (k := bareMC.k)
      fun _ _ hJ => hQP _ _ _ hJ
    exact ExitW.imp H1 (ExitW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.Rt.arOf (Ly).Λ)
        (Ly).lab s c ∧ (FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedS (Ly).Λ (fun _ => none) s c fs))
        H2 H3 fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c hS ⟨hM, hf, hnr, hpl⟩ => rtM_w2V hp hS hov hM hf hnr hpl
  · exact (Spike.Lib.A64.Rt.mainUW_ofFalse (Post := fun c v => Post c fs v)
      (ms := MSAt h i p rd J none ls0 [])
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      fun m hm => hv hm.1.1).exit

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.exitW_sfactsAtU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.exitW_sfactsAtU

/-- info: 'Spike.Lib.LowerA64.mainUW_rtM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainUW_rtM

/-- info: 'Spike.Lib.LowerA64.mainUW_ofPlaceOKU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainUW_ofPlaceOKU

/-- info: 'Spike.Lib.LowerA64.hWx_ofPlaceOKU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWx_ofPlaceOKU

end Spike.Lib.LowerA64
