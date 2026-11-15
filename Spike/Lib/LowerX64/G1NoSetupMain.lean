/-
**`scc_rt_main` without a setup block inside `W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/G1NoSetupMain.lean`, the bare twin of
`Spike/Lib/LowerX64/RtMainX.lean`, `Spike/Lib/LowerX64/RtMainXF.lean` and
`Spike/Lib/LowerX64/RtMainXV.lean`): its own states (`MainUW`,
`Spike/Lib/Rt/X64Main.lean`) at `bareMC` inside the runtime's world `RtM`,
and with `SFacts` (`mainUW_gen`, `Spike/Lib/Rt/X64RtMainU.lean`) and the
source controls' facts inside `W2`. The prologue and `call wc_main` run at
the start control; the `exit_group` tail at `main`'s returned controls,
held at pending frames and placed by the value (`MainCtlV`). The region is
the switch region's callee's, the frame condition the switch's with an
extra frame `Fw` (`startUF_segWSF`'s).

- `exitW_sfactsAtU`: the tail's states carry `SFacts` at a fixed control
  `cs` with `CFacts cs`, for any post (`exitW_sfactsAt` at `mainUIn`);
- `bareMC_blks`, `bareMC_Z`, `bareMC_k`: `bareMC`'s blocks' labels and
  falls-through, its labels none of the write abort's; its frame and result
  slot;
- `mainUW_rtM`: `MainUW` inside `RtM` at `bareMC`, for any program with
  its code (`mainUIn`) and the runtime's, its phase facts, the growth path
  and the user function positioned off the write abort (`hgrow`, `hfn`);
- `MainUW.ofCtl`, `MainUW.imp`: `MainUW` inside `W ∧ Q` from `W` and the
  nodes' controls; `MainUW` inside `W` from two;
- `mainUW_ofPlaceOKU`: the prologue and the call inside `nilW W2At` at a
  placed output at the start control's `MainCtl`, the exit given;
- `hWx_ofPlaceOKU`: the exit tail inside `W2At` at every frames, at held
  controls placed by the value (`hWx_ofPlaceOKV` at `bareMC`).
-/
import Spike.Lib.LowerX64.RtMainXV
import Spike.Lib.LowerX64.RtMainXF

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (NodeW BlkW ND At okBlk okBlk_callB)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add' xHead xLea xCmp xFr xExit xHead_ok xLea_ok xCmp_ok xFr_ok
  xExit_ok prologueIn exitIn XExitW)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk MainCode MainUW mainUIn bareMC mainURR blkW_postO nodeW_syscall_postO)
open Spike.Lib.X64.Rt.MainU (MainPh xHead_noRet xLea_noRet xCmp_noRet xFr_noRet callB_noRet xExit_noRet)
open Scc.Cert.Rt.X64 (blockAtB label_labelGapB)

/-! ## The exit tail at a fixed control -/

section Exit

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {lbl : Lbl}

/-- **The `exit_group` tail's states without a setup block carry `SFacts`
at a fixed control `cs`** (`CFacts cs`, `hC`), for any post `Post`:
`mainUW_gen`'s exit part at the nodes with their controls replaced by `cs`
(`exitW_sfactsAt` at `mainUIn`). -/
theorem exitW_sfactsAtU (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {mc : MainCode} (hin : mainUIn cells mc = true) {Post : Ctl → BitVec 64 → Prop} {cs : Ctl}
    (hC : CFacts Λ lbl cs) (hph : MainPh okPc ph lab mc)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - mc.Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    XExitW (fun s _ => SFacts Λ μ own rS Tk lbl s cs) K exe endPc R F
      (mainURR (_root_.Executable.labels exe).label mc Post) (-8 - mc.Z.toInt) (-8)
      mc.k mc.ze0 mc.ze1 mc.ze2 := by
  have h := hin
  simp only [mainUIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, -⟩, -⟩, bEx, bSvc⟩ := h
  rw [hI.labOk]
  refine ⟨BlkW.ofStar (W := fun s c => SFacts Λ μ own rS Tk lbl s c) ?_,
    NodeW.ofStar (W := fun s c => SFacts Λ μ own rS Tk lbl s c) ?_⟩
  · -- the tail's block
    exact blkW_postO hI bEx (ofNat_zero' _) (xExit_ok (lo := -8 - mc.Z.toInt) (hi := 0) _ _ _ _ hk)
      hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ hC) hph.ex
      (fun _ _ _ k hk hr => (noRet_false (xExit_noRet _ _ _ _) k hk hr).elim) (fun _ _ _ => rfl)
      hsub hfit hFO
  · -- the `exit_group`
    exact nodeW_syscall_postO (p := lab mc.sp0 + Int64.ofNat (mc.ze0 + mc.ze1 + mc.ze2)) hI bSvc rfl
      (by show _ + _ + _ + _ = _; rw [ofNat_add', ofNat_add']; rfl)
      (fun _ _ hJ => hJ.1 ▸ hC) hph.svc.1 hph.svc.2 hR hR8 hl hh hsub hFO
      (fun _ _ ⟨_, _, h, _⟩ => by rw [h]; decide)

end Exit

/-! ## `bareMC`'s closed facts -/

/-- **`bareMC`'s blocks' closed facts**: the prologue's, the call's and
the tail's labels and falls-through, the labels of `scc_rt_main` none of
the write abort's. -/
theorem bareMC_blks :
    blkLabs xHead = [] ∧ blkLabs (xLea bareMC.Z bareMC.zl) = [] ∧
    blkLabs (xCmp bareMC.grow bareMC.z1 bareMC.z2) = [bareMC.grow] ∧
    blkLabs (xFr bareMC.Z bareMC.zs bareMC.ps) = [] ∧ blkLabs (Spike.Lib.X64.callB bareMC.fn) = [bareMC.fn] ∧
    lastFalls (Spike.Lib.X64.callB bareMC.fn) = false ∧
    blkLabs (xExit bareMC.k bareMC.ze0 bareMC.ze1 bareMC.ze2) = [] ∧
    "scc_rt_main" ∉ Spike.Lib.X64.AllocG.abLabs ∧ bareMC.sc ∉ Spike.Lib.X64.AllocG.abLabs ∧
    bareMC.e0 ∉ Spike.Lib.X64.AllocG.abLabs ∧ bareMC.sp0 ∉ Spike.Lib.X64.AllocG.abLabs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | rfl | simp [bareMC, xLea, xCmp, xFr, xExit, Spike.Lib.X64.callB]

/-- `bareMC`'s frame is 32. -/
theorem bareMC_Z : bareMC.Z.toInt = 32 := by decide

/-- `bareMC`'s result slot is at `-16`. -/
theorem bareMC_k : bareMC.k.toInt = -16 := by decide

/-! ## `scc_rt_main` inside `RtM` -/

section Main

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {ar : Arena}
  {R : Region} {F : MachineData → Prop}

/-- A closed side condition at `bareMC`: its labels and blocks unfolded. -/
local macro "bdec" : tactic =>
  `(tactic| (try simp only [bareMC]) <;> first | decide | rfl | simp [xLea, xCmp, xFr, xExit, Spike.Lib.X64.callB])

set_option maxHeartbeats 800000 in
/-- **`scc_rt_main`'s own states without a setup block are inside `RtM`**
(`MainUW` at `bareMC`; `mainSW_rtM` without the setup call), for any
program with its code (`hin`) and the runtime's (`hpr`, `hab`): its phase
facts (`hph`), the growth path and the user function positioned off the
write abort (`hgrow`, `hfn`), in any region holding its frame and the
return address its call pushes (`hlo`, `hhi`). -/
theorem mainUW_rtM (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hin : mainUIn cells bareMC = true)
    (hph : MainPh okPc ph lab bareMC) (hgrow : PosOff cells lab (lab bareMC.grow))
    (hfn : PosOff cells lab (lab bareMC.fn))
    (hR : R.OK) (hlo : R.lo ≤ -8 - bareMC.Z.toInt - 8) (hhi : 0 ≤ R.hi)
    {ms : MemSide isa} {Post : Ctl → BitVec 64 → Prop} {g : Spike.Lib.X64.Flow.Ret0.MainG} :
    MainUW (RtM μ ar lab) (fun _ _ => False) exe endPc R F ms bareMC Post g := by
  have hZ := bareMC_Z
  have hk := bareMC_k
  have hm8 : (-8 : Int64).toInt = -8 := by decide
  have h := hin
  simp only [mainUIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, gE⟩, bCall⟩, -⟩, bEx, bSvc⟩ := h
  have esc := label_labelGapB hI.lays hgap
  have ee0 := label_labelGapB hI.lays gE
  rw [hI.labOk] at esc ee0
  have h4 : lab "scc_rt_main" + 1 + 3 = lab bareMC.sc := by rw [esc, Int64.add_assoc]; rfl
  have hloZ : R.lo ≤ -8 - bareMC.Z.toInt := by omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩ <;> rw [hI.labOk]
  · -- the head
    exact blkW_rtM hI hpr hab bHd (ofNat_zero' _) (xHead_ok (lo := -8 - bareMC.Z.toInt) (hi := 0)
      (by omega) (Int.le_refl _)) hR hloZ hhi (by have := hph.hd; rwa [ofNat_zero'] at this) (by bdec)
      xHead_noRet (by bdec)
      (fun _ => by
        have := posOff_of_blockAtB (lab := lab) bLea (by bdec) (by bdec)
        rw [ofNat_zero', esc] at this
        exact this)
      (labs_nil (by bdec))
  · -- the check's address
    exact blkW_rtM hI hpr hab bLea (by show _ = _ + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -8 - bareMC.Z.toInt) (hi := 0) _ _) hR hloZ hhi
      (by have := hph.lea; rwa [ofNat_zero', ← h4] at this) (by bdec) (xLea_noRet _ _) (noAb_nil (by bdec))
      (fun _ => posOff_of_blockAtB bLd (by bdec) (by bdec)) (labs_nil (by bdec))
  · -- the limit's load
    exact nodeW_rtM_fs (p := lab bareMC.sc + Int64.ofNat 5) hI bLd rfl (by show _ + 1 + 3 + _ = _; rw [h4]; rfl)
      hph.ld.1 (by rw [← ofNat_add']; exact notAb_of_blockAtB hI hpr hab bCmp (by bdec) (by bdec))
  · -- the check
    have e : lab bareMC.sc + Int64.ofNat 14 =
        lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 := by rw [h4, ← ofNat_add']
    exact blkW_rtM hI hpr hab bCmp e (xCmp_ok (lo := -8 - bareMC.Z.toInt) (hi := 0) _ _ _ _) hR hloZ hhi
      (e ▸ hph.cmp) (by bdec) (xCmp_noRet _ _ _) (by bdec)
      (fun _ => posOff_of_blockAtB bFr (by bdec) (by bdec))
      (labs_one (L0 := bareMC.grow) (by bdec) hgrow)
  · -- the frame
    have e : lab bareMC.sc + Int64.ofNat 19 =
        lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 := by
      rw [h4, ← ofNat_add', ← ofNat_add', ← ofNat_add']
    exact blkW_rtM hI hpr hab bFr e (xFr_ok (lo := -8 - bareMC.Z.toInt) (hi := 0) _ _ _
        (fun p hp => by
          simp only [bareMC, List.mem_singleton] at hp
          subst hp
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, hm8]
          refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hloZ hhi (e ▸ hph.fr) (by bdec) (xFr_noRet _ _ _) (noAb_nil (by bdec))
      (fun _ => by
        have := posOff_of_blockAtB (lab := lab) bCall (by bdec) (by bdec)
        rw [ofNat_zero', ee0] at this
        exact this)
      (labs_nil (by bdec))
  · -- `call wc_main`
    exact blkW_rtM hI hpr hab bCall (ofNat_zero' _)
      (okBlk_callB (lo := -8 - bareMC.Z.toInt - 8) (hi := 0) _ (by
        simp only [Spike.Lib.offOk, decide_eq_true_eq, Spike.Lib.X64.Rt.mainU1R, Spike.Lib.X64.Rt.oU, hZ]
        refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hlo hhi (by have := hph.call; rwa [ofNat_zero'] at this) (by bdec) (callB_noRet _) (by bdec)
      (fun h => absurd h (by bdec)) (labs_one (L0 := bareMC.fn) (by bdec) hfn)
  · -- the tail's block
    exact blkW_rtM hI hpr hab bEx (ofNat_zero' _)
      (xExit_ok (lo := -8 - bareMC.Z.toInt) (hi := 0) _ _ _ _ (by
        simp only [Spike.Lib.offOk, decide_eq_true_eq, hk, hZ]
        refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hloZ hhi (by have := hph.ex; rwa [ofNat_zero'] at this) (by bdec) (xExit_noRet _ _ _ _) (noAb_nil (by bdec))
      (fun _ => posOff_of_blockAtB bSvc (by bdec) (by bdec)) (labs_nil (by bdec))
  · -- the `exit_group`
    exact nodeW_rtM_exit (p := lab bareMC.sp0 + Int64.ofNat 13) hI bSvc rfl
      (by
        show lab bareMC.sp0 + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5 = _
        rw [← ofNat_add', ← ofNat_add'])
      hph.svc.1
      (fun σ _ hJ => by
        simp only [Reg64s.get64]
        apply BitVec.eq_of_toNat_eq
        rw [UInt64.toNat_toBitVec, hJ.1]; rfl)

end Main

/-! ## Joining the nodes' facts -/

section Ctl

open Spike.Lib.X64.AllocG (BlkW.imp NodeW.imp)

variable {W W1 W2 : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {mc : MainCode} {Post : Ctl → BitVec 64 → Prop}
  {g : Spike.Lib.X64.Flow.Ret0.MainG}

/-- **`scc_rt_main`'s own states without a setup block inside `W ∧ Q`**
from ones inside `W`, `Q` of the entry's control (`hC0`) and of every
control `Post` relates (`hP`). -/
theorem MainUW.ofCtl {Q : Ctl → Prop} (h : MainUW W K exe endPc R F ms mc Post g) (hC0 : Q g.c0)
    (hP : ∀ c v, Post c v → Q c) : MainUW (fun s c => W s c ∧ Q c) K exe endPc R F ms mc Post g :=
  ⟨⟨BlkW.ofCtl h.pro.w0 fun _ _ hJ => hJ.1 ▸ hC0, BlkW.ofCtl h.pro.w1 fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hC0,
      NodeW.ofCtl h.pro.w2 fun _ _ ⟨_, hJ, _⟩ => hJ.1 ▸ hC0,
      BlkW.ofCtl h.pro.w3 fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0,
      BlkW.ofCtl h.pro.w4 fun _ _ ⟨_, _, hJ, _⟩ => hJ.1 ▸ hC0⟩,
    BlkW.ofCtl h.call fun _ _ hJ => hJ.1.1 ▸ hC0,
    ⟨BlkW.ofCtl h.exit.w0 fun _ _ hJ => hP _ _ hJ.1, NodeW.ofCtl h.exit.w1 fun _ _ ⟨_, _, hJ, _⟩ => hP _ _ hJ.1⟩⟩

/-- **`scc_rt_main`'s own states without a setup block inside `W`** from
ones inside `W1` not moved by `K` and ones inside `W2`, `W1 ∧ W2` inside
`W`. -/
theorem MainUW.imp (h1 : MainUW W1 K exe endPc R F ms mc Post g)
    (h2 : MainUW W2 (fun _ _ => False) exe endPc R F ms mc Post g)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : MainUW W K exe endPc R F ms mc Post g :=
  ⟨⟨BlkW.imp h1.pro.w0 h2.pro.w0 hw, BlkW.imp h1.pro.w1 h2.pro.w1 hw, NodeW.imp h1.pro.w2 h2.pro.w2 hw,
      BlkW.imp h1.pro.w3 h2.pro.w3 hw, BlkW.imp h1.pro.w4 h2.pro.w4 hw⟩,
    BlkW.imp h1.call h2.call hw,
    ⟨BlkW.imp h1.exit.w0 h2.exit.w0 hw, NodeW.imp h1.exit.w1 h2.exit.w1 hw⟩⟩

end Ctl

/-! ## At a placed output -/

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
open Spike.Lib.X64.Rt (swFSL rS0) in
/-- **`scc_rt_main`'s own states without a setup block inside `W2At`**
(`startUF_segWSF`'s `hW` at `bareMC`) at a placed output: the prologue and
the call from `mainUW_gen` and `mainUW_rtM`, joined by `rtM_w2` with the
start control's `MainCtl` (`hQ0`, `MainUW.ofCtl`); the exit given (`hWx`).
Left: the code and phase facts (`hin`, `hph`), the two targets positioned
off the write abort (`hgrow`, `hfn`), the start control's `CFacts`
(`hC0`), and the frame inside the switch region (`hLZ`); the frame
condition any extra frame `Fw` with the switch's. -/
theorem mainUW_ofPlaceOKU {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} {Fw : _root_.Mem 64 → Prop}
    (hp : ProgNoS ZBad p) (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    (hin : mainUIn (Ly).prog bareMC = true)
    (hph : MainPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab bareMC)
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.grow))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.fn))
    (hLZ : 8 + 8 + bareMC.Z.toInt + 8 ≤ L) {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hQ0 : MainCtl (Ly).Λ (fun _ => none) c0)
    (hWx : ∀ v, XExitW (Spike.Lib.X64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainURR (Ly).lab bareMC Post) (-8 - bareMC.Z.toInt) (-8) bareMC.k bareMC.ze0 bareMC.ze1 bareMC.ze2) :
    ∀ v, MainUW (Spike.Lib.X64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) (MSAt h i p rd J ab ls0 [])
      bareMC Post ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩ := by
  intro v
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hZ := bareMC_Z
    have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
    have hL0 : (0 : Int) ≤ L := by omega
    have h8 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm
    have hfit : (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64 := by
      rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
    have hout : ((limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
          (stacksA (Ly).lab + 0#64 + 16384#64).toNat + -L ∨
        ((stacksA (Ly).lab + 0#64 + 16384#64).toNat : Int) + 0 ≤
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat := by
      rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hLm
    have hmr : Scc.Sem.Kernel.mapped (K0 (Ly).Λ) false ⟨limA (tpOf (pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
      rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]; exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
    obtain ⟨hR', -⟩ := Spike.Lib.X64.Rt.mainE_ok (rS := rS0 (Ly)) (tcb := pinA (Ly).lab + 0#64 + 8#64)
      (top := stacksA (Ly).lab + 0#64 + 16384#64) hL hL8 hok hfit hout (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    have hb0 : ((((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) =
        (stacksA (Ly).lab + 0#64 + 16384#64).toNat + (-8 - 0)) :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have HS := Spike.Lib.X64.Rt.mainUW_gen (ms := MSAt h i p rd J ab ls0 []) (lbl := lbl0) hI hin
      (Post := fun _ _ => False)
      (F := fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m) ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      hC0 (fun _ _ h => h.elim) hph hR' (by omega) (by show 8 - L ≤ _; omega)
      (by show (0 : Int) ≤ 8; decide) (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide)
      (by rw [hZ]; decide) (by rw [hZ]; decide) (by decide) (by decide) hmr
      (fun _ h => h.1.2.1.2) hsub (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
      (fun _ h => Spike.Lib.X64.Rt.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by decide) h.1.2.2 h.2)
    have HW := MainUW.imp (MainUW.ofCtl HS (Q := MainCtl (Ly).Λ (fun _ => none)) hQ0 fun _ _ h => h.elim)
      (mainUW_rtM hI (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
        hin hph hgrow hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide))
      (W := Spike.Lib.X64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      fun s c h1 h2 => rtM_w2 hp h1.1 h2 h1.2
    exact ⟨HW.pro, HW.call, hWx _⟩
  · exact Spike.Lib.X64.Rt.mainUW_ofFalse fun m hm => hv hm.1.2.1.1

open Spike.Lib.X64.Flow.Ret0 in
open Spike.Lib.X64.Rt (swFSL rS0) in
/-- **The exit tail without a setup block inside `W2At` at every frames,
at held controls placed by the value** (`hWx_ofPlaceOKV` at `bareMC`):
`exitW_sfactsAtU` at the start control `c0` (`hC0`, not at an overflow
`hov`) and `mainUW_rtM`'s exit part, each tail state placing the control
by the register holding the value (`xExitW_placedV`, the post's controls'
`MainCtlV` at `fs`, `hQP`), joined by `rtM_w2V`. -/
theorem hWx_ofPlaceOKU {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} {Fw : _root_.Mem 64 → Prop} (hp : ProgNoS ZBad p)
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    (hin : mainUIn (Ly).prog bareMC = true)
    (hph : MainPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab bareMC)
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.grow))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab bareMC.fn))
    (hLZ : 8 + 8 + bareMC.Z.toInt + 8 ≤ L) {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hov : ¬ OvfReady c0)
    (hQP : ∀ c fs v, Post c fs v → MainCtlV (Ly).Λ (fun _ => none) c fs v) :
    ∀ v fs, XExitW (fun s c => W2At h i p rd (rS0 (Ly)) J Dt ls0 s c fs)
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainURR (Ly).lab bareMC (fun c v => Post c fs v)) (-8 - bareMC.Z.toInt) (-8)
      bareMC.k bareMC.ze0 bareMC.ze1 bareMC.ze2 := by
  intro v fs
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hZ := bareMC_Z
    have hk := bareMC_k
    have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
    have hL0 : (0 : Int) ≤ L := by omega
    have h8 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hLm
    have hfit : (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64 := by
      rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
    have hout : ((limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
          (stacksA (Ly).lab + 0#64 + 16384#64).toNat + -L ∨
        ((stacksA (Ly).lab + 0#64 + 16384#64).toNat : Int) + 0 ≤
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))).toNat := by
      rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hLm
    obtain ⟨hR', -⟩ := Spike.Lib.X64.Rt.mainE_ok (rS := rS0 (Ly)) (tcb := pinA (Ly).lab + 0#64 + 8#64)
      (top := stacksA (Ly).lab + 0#64 + 16384#64) hL hL8 hok hfit hout (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
    have hb0 : ((((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) =
        (stacksA (Ly).lab + 0#64 + 16384#64).toNat + (-8 - 0)) :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have H1 := exitW_sfactsAtU (lbl := lbl0) hI hin (Post := fun c v => Post c fs v)
      (F := fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m) ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      hC0 hph hR' (by omega) (by show 8 - L ≤ _; omega)
      (by show (0 : Int) ≤ 8; decide) (by show (8 - L) % 8 = 0; omega) (by show (8 : Int) % 8 = 0; decide)
      (by decide) hsub (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
      (fun _ h => Spike.Lib.X64.Rt.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by decide) h.1.2.2 h.2)
    have H2 := (mainUW_rtM (ar := arOf (Ly).Λ) (Post := fun c v => Post c fs v)
      (g := ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), c0⟩)
      (ms := MSAt h i p rd J none ls0 [])
      (F := fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m) ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m) hI
      (Scc.Cert.PlaceOK.X64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.X64.abortIn_of_placeOKAt h)
      hin hph hgrow hfn hR' (by show 8 - L ≤ _; omega) (by show (0 : Int) ≤ 8; decide)).exit
    have H3 := xExitW_placedV (Λ := (Ly).Λ) (L0 := fun _ => none) (fs := fs) (exe := (Ly).exe)
      (endPc := (Ly).endPc) (R := (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (F := fun m => (Fw m.dmem ∧ swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m) ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (n := mainURR (Ly).lab bareMC (fun c v => Post c fs v)) (k := bareMC.k) (z0 := bareMC.ze0)
      (z1 := bareMC.ze1) (z2 := bareMC.ze2) rfl fun _ _ hJ => hQP _ _ _ hJ.1
    have hw : ∀ s c, SFacts (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
        (Spike.Lib.X64.PhRec.Tk (Ly)) lbl0 s c0 →
        (RtM (Spike.Lib.X64.PhRec.μ (Ly)) (arOf (Ly).Λ) (Ly).lab s c ∧
          (FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedS (Ly).Λ (fun _ => none) s c fs)) →
        W2At h i p rd (rS0 (Ly)) J Dt ls0 s c fs :=
      fun _ _ h1 h2 => rtM_w2V hp h1 hov h2.1 h2.2.1 h2.2.2.1 h2.2.2.2
    exact ⟨BlkW.imp H1.w0 (BlkW.imp H2.w0 H3.w0 fun _ _ a b => ⟨a, b⟩) hw,
      NodeW.imp H1.w1 (NodeW.imp H2.w1 H3.w1 fun _ _ a b => ⟨a, b⟩) hw⟩
  · exact ⟨Spike.Lib.X64.Rt.blkW_ofFalse fun m hm => hv hm.1.2.1.1,
      Spike.Lib.X64.Rt.nodeW_ofFalse fun m hm => hv hm.1.2.1.1⟩

end Place

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.exitW_sfactsAtU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.exitW_sfactsAtU

/-- info: 'Spike.Lib.LowerX64.mainUW_rtM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainUW_rtM

/-- info: 'Spike.Lib.LowerX64.mainUW_ofPlaceOKU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainUW_ofPlaceOKU

/-- info: 'Spike.Lib.LowerX64.hWx_ofPlaceOKU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hWx_ofPlaceOKU
