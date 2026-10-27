/-
**`scc_rt_main` after a setup block inside `W2`** (AArch64; the twin of
`Spike/Lib/LowerX64/RtMainX.lean`): its own states (`MainSW`,
`Spike/Lib/Rt/A64MainS.lean`) inside the runtime's world `RtM` (the write
abort's phase kept and no write to the arena), and with `SFacts`
(`mainSW_sfacts`, `Spike/Lib/Rt/A64RtMainS.lean`) and the source controls'
facts (`MainCtl`) inside `W2` at no frame.

- `RtM`, `RtX.toM`: `RtX` without the control's facts (`scc_rt_main` runs
  at the source's controls after `c0`);
- `blkW_rtM`, `nodeW_rtM_ldr`, `nodeW_rtM_exit`: a covered block without
  `ret`, a load and the `exit_group` `svc` inside `RtM`;
- `marshal_facts`, `setupMC_Z`, `setupMC_k`: the marshalling block's label
  and end, and the frame's sizes, at each `sw < 8`;
- `mainSW_rtM`: `MainSW` inside `RtM` at `setupMC sw`, for any program with
  its code (`mainSIn`) and the runtime's, its phase facts, the growth path,
  the setup block and the user function positioned off the write abort
  (`hgrow`, `hset`, `hfn`), the limit word unloaded (`hun`);
- `rtM_sfacts_setupEntry`: the setup call's node (`mainSC`, at the setup
  function's label with the entry's control) inside `RtM` and `SFacts`,
  from the setup function's prologue head;
- `MainCtl`: a control's facts `W2` asks at no frame beyond `SFacts`
  (`FrOk2`, not at an overflow, placed at no frame); `BlkW.ofCtl`,
  `NodeW.ofCtl`, `MainSW.ofCtl`: obligations of a control predicate from
  the node invariants'; `MainSW.imp`: `MainSW` inside `W` from two;
- `rtM_w2`: `W2` at no frame from `SFacts`, `RtM` and `MainCtl`;
- `mainSW_w2`: `MainSW` inside `nilW W2` from `mainSW_sfacts`,
  `mainSW_rtM` and `MainSW.ofCtl`;
- `hWC_ofPlaceOK`: the setup call's node inside `W2At` at a placed output
  (`h0_ofPlaceOK`'s `hWC`), from `rtM_sfacts_setupEntry` and `rtM_w2`.
-/
import Spike.Lib.LowerA64.Start2W2
import Spike.Lib.Rt.A64RtMainS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (InstOk SetupCode setupMC marshal MainSW mainSIn okBlk_marshal)
open Spike.Lib.A64.Rt.MainS (MainPhS marshal_noRet)
open Spike.Lib.A64.Rt.MainU (chkHead_noRet chkBr_noRet blD_noRet exitTail_noRet pc2 pc3 pc5)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Scc.Cert.Rt.A64 (blockAt label_labelGap)
open Scc.Sem.A64 (abi pcOf atSvc_of_cellAt)

/-! ## `scc_rt_main`'s world -/

/-- **The runtime's remaining facts inside `scc_rt_main`**: `RtX` without
the control's facts (`scc_rt_main` runs at the source's controls after
`c0`): the write abort's phase kept and no write to the arena's heap nor its
counter. -/
def RtM (μ : Marks) (ar : Arena) (lab : Label → Int64) : Frag isaLSE2 := fun s _ =>
  AbSt μ (Ab lab) s ∧ WrOff ar s

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {lbl : Lbl} {lab : Label → Int64} {c0 : Ctl}

/-- `RtX` gives `RtM`. -/
theorem RtX.toM {s : State} {c : Ctl} (h : RtX Λ μ ar lbl lab c0 s c) : RtM μ ar lab s c :=
  ⟨h.1, h.2.2.1⟩

section Nodes

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {own : Own} {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat}
  {R : Region} {F : MachineData → Prop}

/-- **A covered runtime block inside `RtM`**: `blkW_rtX` without the
control's facts; its phase check at the block's pc. -/
theorem blkW_rtM {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat (4 * k)) ra blk = true) (hnr : noRetBlk blk = true)
    (hl : l ∉ abLabs)
    (hnext : lastFalls blk = true → PosOff prog lab (lab l + Int64.ofNat (4 * (k + blk.length))))
    (hlabs : ∀ L ∈ blkLabs blk, PosOff prog lab (lab L)) :
    BlkW (RtM μ ar lab) (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  have hA := blkW_abSt_pos hI hpr hab (F := F) (dead := dead) (ra := ra) hcode hok hR hal hlo hhi hph hnr
    (htgt_posOff hb he hl hnr hnext hlabs)
  have hW := Spike.Lib.A64.AllocG.blkW_noWr hI hb he hok hR hal hlo hhi (F := F)
  intro s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h1 := hA s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h2 := hW s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  exact ⟨⟨h1.1, fun L hL => (h2.1 L hL).elim⟩, fun _ h => h⟩

/-- **A runtime node at a load inside `RtM`**: `nodeW_rtX_ldr` without the
control's facts. -/
theorem nodeW_rtM_ldr {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {t b : XReg}
    {i : Int64} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.ldrDir t b i] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none) :
    NodeW (RtM μ ar lab) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs b i = Spike.Lib.A64.Flow.rAddr σ.regs b i := by rw [hA.regs]
  have hex := Kraken.Promising.Lower.A64.exec_ldr_agrees hc ha' (ha σ c s.st.1 hJ hD)
    (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)
  refine ⟨⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc (by intro imm h; cases h))
    fun tr ht => ?_, fun L hL => (noWr_load hex L hL).elim⟩, fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact fun _ _ => Spike.Lib.A64.AllocG.not_ab_after hpc hnx

/-- **An `exit_group` `svc #0` inside `RtM`**: at `x8 = 94` (`hx`) the call
resumes in no state; its pc off the sites. -/
theorem nodeW_rtM_exit {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.svcDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hx : ∀ σ c, n.J σ c → σ.regs.X8.toNat = 94) :
    NodeW (RtM μ ar lab) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have hsys : abi.atSys s = true := atSvc_of_cellAt hc
  have hd : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup σ.regs.X0.toNat) := by
    rw [← Spike.Lib.A64.Flow.svcCall_exitGroup (hx σ c hJ), Spike.Lib.A64.Flow.svcCall, ← hA.regs]; rfl
  refine ⟨⟨⟨fun _ h => (by rw [hsys] at h; cases h), fun _ _ call hd' s' hs' _ => ?_,
    fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩, fun L hL => ?_⟩, fun _ h => h⟩
  · rw [hd] at hd'
    cases hd'
    rw [Spike.Lib.A64.Flow.certSuccs_exitGroup] at hs'
    cases hs'
  · rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;>
      rw [Kraken.Promising.Lower.A64.exec_svc hc] at h <;> cases h

end Nodes

/-! ## The setup code's facts -/

/-- **The marshalling block at each `sw < 8`**: its one label the user
function, its last instruction (the call) not falling through. -/
theorem marshal_facts : ∀ sw < 8, blkLabs (marshal sw "wc_main") = ["wc_main"] ∧
    lastFalls (marshal sw "wc_main") = false := by
  decide

/-- The frame's size at `sw` words. -/
theorem setupMC_Z : ∀ sw < 8, (setupMC sw).Z.toInt = (((8 * (sw + 3) + 16 + 15) / 16 * 16 : Nat) : Int) := by
  decide

/-- The result's slot at `sw` words. -/
theorem setupMC_k : ∀ sw < 8, (setupMC sw).k.toInt = ((8 * (1 + sw) : Nat) : Int) := by
  decide

/-- **The blocks' closed facts at each `sw < 8`**: the prologue's, the setup
call's and the tail's labels and falls-through, the runtime's labels of
`scc_rt_main` none of the write abort's. -/
theorem setupMC_blks : ∀ sw < 8,
    blkLabs (chkHead (setupMC sw).Z) = [] ∧ blkLabs (chkBr (setupMC sw).grow) = [(setupMC sw).grow] ∧
    blkLabs (frameSet (setupMC sw).Z [(.X0, 0)]) = [] ∧ blkLabs [blD (setupMC sw).setup] =
      [(setupMC sw).setup] ∧ lastFalls [blD (setupMC sw).setup] = false ∧
    blkLabs (exitTail (setupMC sw).k) = [] ∧ (setupMC sw).sc ∉ abLabs ∧ (setupMC sw).e0 ∉ abLabs ∧
    (setupMC sw).sp0 ∉ abLabs ∧ (setupMC sw).sp1 ∉ abLabs := by
  decide

section Main

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {own : Own} {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat}
  {R : Region} {F : MachineData → Prop}

set_option maxHeartbeats 800000 in
/-- **`scc_rt_main`'s own states after a setup block are inside `RtM`**
(`MainSW` at `setupMC sw`, `sw < 8`), for any program with its code
(`hin`) and the runtime's (`hpr`, `hab`): its phase facts (`hph`), the
growth path, the setup block and the user function positioned off the
write abort (`hgrow`, `hset`, `hfn`), in any 16-aligned region holding its
frame (`hlo`, `hhi`), the limit word unloaded under the frame condition
(`hun`). -/
theorem mainSW_rtM {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {sw : Nat} (hsw : sw < 8) (hin : mainSIn prog (setupMC sw) = true)
    (hph : MainPhS okPc ph lab (setupMC sw)) (hgrow : PosOff prog lab (lab (setupMC sw).grow))
    (hset : PosOff prog lab (lab (setupMC sw).setup)) (hfn : PosOff prog lab (lab (setupMC sw).fn))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(setupMC sw).Z.toInt) (hhi : 0 ≤ R.hi)
    {ms : MemSide isaLSE2} {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    {g : Spike.Lib.A64.Flow.Ret0.MainG} {x0 : BitVec 64}
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.Ret0.limA g.tp) 8 = none) :
    MainSW (RtM μ ar lab) (fun _ _ => False) exe endPc R F ms (setupMC sw) PostS Post g x0 := by
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  obtain ⟨lHd, lBr, lFr, lCall, fCall, lEx, nSc, nE0, nSp0, nSp1⟩ := setupMC_blks sw hsw
  have hmf : blkLabs (marshal (setupMC sw).sw (setupMC sw).fn) = [(setupMC sw).fn] ∧
      lastFalls (marshal (setupMC sw).sw (setupMC sw).fn) = false := marshal_facts sw hsw
  have h := hin
  simp only [mainSIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLd⟩, bBr⟩, bFr⟩, gE⟩, bCall⟩, -⟩, bMsh⟩, -⟩, bEx, bSvc⟩ := h
  have esc := label_labelGap hI.lays hgap
  have ee0 := label_labelGap hI.lays gE
  rw [hI.labOk] at esc ee0
  have h16 : (setupMC sw).Z.toInt % 16 = 0 := by rw [hZ]; omega
  have hZ16 : 16 ≤ (setupMC sw).Z.toInt := by rw [hZ]; omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩ <;> rw [hI.labOk]
  · -- the check's head
    refine blkW_rtM hI hpr hab bHd (by rw [esc, ofNat4_zero, ofNat4_zero])
      (chkHead_ok (-(setupMC sw).Z.toInt) 0 _) hR hal hlo hhi hph.hd (chkHead_noRet _) nSc (fun _ => ?_)
      (labs_nil lHd)
    exact posOff_of_blockAt (lab := lab) bLd nSc (i := 0) (by decide)
  · -- the limit's load
    exact nodeW_rtM_ldr hI bLd rfl (by show _ + 4 + 4 = _; rw [esc, ofNat4_zero, pc2]) hph.ld.1
      (by rw [Spike.Lib.A64.Flow.Ret0.ofNat4_succ']; exact notAb_of_blockAt hI hpr hab bBr nSc (by simp [chkBr]))
      (fun σ c m ⟨_, hJ, he⟩ hF => by
        rw [he, rAddr_chkRegs, Spike.Lib.A64.Flow.Ret0.tcbA_limA hJ.1.2.2]; exact hun m hF)
  · -- the check's branch
    refine blkW_rtM hI hpr hab bBr (by rw [esc, ofNat4_zero, pc3]; rfl)
      (chkBr_ok (-(setupMC sw).Z.toInt) 0 _ _) hR hal hlo hhi hph.br (chkBr_noRet _) nSc (fun _ => ?_)
      (labs_one lBr hgrow)
    exact posOff_of_blockAt (lab := lab) bFr nSc (i := 0) (by simp [frameSet, frSetup])
  · -- the frame
    refine blkW_rtM hI hpr hab bFr (by rw [esc, ofNat4_zero, pc5]; rfl)
      (frameSet_ok (lo := -(setupMC sw).Z.toInt) (hi := 0) h16 hZ16 (by omega) (Int.le_refl _)
        (by simp [Spike.Lib.offOk]; omega)) hR hal hlo hhi hph.fr (frameSet_noRet _ _) nSc (fun _ => ?_)
      (labs_nil lFr)
    have := posOff_of_blockAt (lab := lab) bCall nE0 (i := 0) (by simp)
    rw [Nat.add_zero, ofNat4_zero, ee0] at this
    exact this
  · -- `bl setup`
    exact blkW_rtM hI hpr hab bCall (ofNat4_zero _) (okBlk_blD _ _ _ _) hR hal hlo hhi
      (lo := -(setupMC sw).Z.toInt) (hi := 0) hph.call0 (blD_noRet _) nE0
      (fun h => absurd (fCall.symm.trans h) (by decide)) (labs_one lCall hset)
  · -- the marshalling block and `bl fn`
    exact blkW_rtM hI hpr hab bMsh (ofNat4_zero _)
      (okBlk_marshal (lo := -(setupMC sw).Z.toInt) (hi := 0) (by omega) (show sw ≤ 7 by omega) _
        (fun j hj => by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]; refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hal hlo hhi hph.sp0 (marshal_noRet _ _) nSp0 (fun h => absurd (hmf.2.symm.trans h) (by decide))
      (labs_one hmf.1 hfn)
  · -- the tail's block
    refine blkW_rtM hI hpr hab bEx (ofNat4_zero _)
      (exitTail_ok (lo := -(setupMC sw).Z.toInt) (hi := 0)
        (by
          show Spike.Lib.offOk _ _ (-(setupMC sw).Z.toInt + (setupMC sw).k.toInt) = true
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hk, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega) (by show (-(setupMC sw).Z.toInt) % 16 = 0; omega))
      hR hal hlo hhi hph.ex (exitTail_noRet _) nSp1 (fun _ => ?_) (labs_nil lEx)
    exact posOff_of_blockAt (lab := lab) bSvc nSp1 (i := 0) (by decide)
  · -- the `exit_group`
    exact nodeW_rtM_exit hI bSvc rfl (pc3 _).symm hph.svc.1 fun _ _ h => h.1

/-- **The setup block's call node is inside `RtM` and `SFacts`**
(`mainSC_segWS`'s `hWC` without the control's facts): at the setup
function's label, at `scc_rt_main`'s frame offsets (`bl` pushes nothing),
with its prologue (`hpro`: the stack check label `chk` right after the
label, the check's head and the limit's load after it), the head's phase
facts (`hph`) and `chk` off the write abort (`hl`), in any 16-aligned
region holding the frame: the head's block (`blkW_rtM`, `blkW_postO` at
`okBlk_chkHead_at`, the entry's control's `CFacts`) at its first
instruction. -/
theorem rtM_sfacts_setupEntry {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {sc : SetupCode} {chk entry : Label} {Z lim : Int64} {Lg : Label} {ps : List (XReg × Int64)}
    (hpro : prologueIn prog sc.setup chk entry Z lim Lg ps = true)
    (hph : blkPh okPc ph (fun _ => false) lab (lab chk + Int64.ofNat (4 * 0)) 0 (chkHead Z) = true)
    (hl : chk ∉ abLabs) {lo : Int} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : 0 ≤ R.hi)
    (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) {rS : Range} (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → Spike.Lib.A64.Flow.Ret0.StackOff rS R m) {lbl0 : Lbl}
    {g : Spike.Lib.A64.Flow.Ret0.MainG} {x0 : BitVec 64} (hC0 : CFacts Λ lbl0 g.c0) :
    ∀ s c, At exe endPc R F (Spike.Lib.A64.Rt.mainSC (_root_.Executable.labels exe).label sc g x0) s c →
      RtM μ ar lab s c ∧ SFacts Λ μ own rS Tk lbl0 s c := by
  simp only [prologueIn, Bool.and_eq_true] at hpro
  obtain ⟨⟨⟨⟨⟨hgap, hb⟩, bLd⟩, -⟩, -⟩, -⟩ := hpro
  have he : lab chk + Int64.ofNat (4 * 0) =
      (Spike.Lib.A64.Rt.mainSC (_root_.Executable.labels exe).label sc g x0).pc := by
    show _ = (_root_.Executable.labels exe).label sc.setup
    rw [← hI.labOk, label_labelGap hI.lays hgap, ofNat4_zero, ofNat4_zero]
  have hok : okBlk lo 0 (Spike.Lib.A64.Rt.mainSC (_root_.Executable.labels exe).label sc g x0).o (chkHead Z) =
      true := by
    show okBlk lo 0 ⟨-sc.Z.toInt, []⟩ (chkHead Z) = true
    simp [chkHead, okBlk, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly, Spike.Lib.A64.Flow.AI.ok,
      Spike.Lib.A64.Flow.AI.so, Spike.Lib.A64.Flow.AI.isTerm, Spike.Lib.A64.Flow.soReg, Spike.Lib.A64.Flow.regDst,
      Spike.Lib.A64.Flow.zrB, SO.write, SO.kill, Spike.Lib.rm, SO.set, SO.get]
  have hne : chkHead Z ≠ [] := by simp [chkHead]
  have HM := blkW_rtM (ar := ar) (F := F) hI hpr hab hb he hok hR hal hlo hhi hph
    (chkHead_noRet Z) hl (fun _ => posOff_of_blockAt (lab := lab) bLd hl (i := 0) (by simp))
    (labs_nil (by rfl))
  have HS := Spike.Lib.A64.Rt.blkW_postO (lbl := lbl0) (F := F) (dead := fun _ => false) (ra := 0) hI hb he hok
    hR hal hlo hhi (fun _ _ h => h.1.1 ▸ hC0) hph
    (fun _ _ _ k hk r hr => (noRet_false (chkHead_noRet Z) k hk r hr).elim) (fun _ _ _ => rfl) hl8 hh8 hsub
    hfit hFO
  intro s c hA
  exact ⟨(BlkW.nodeW HM hne s c hA).1, (BlkW.nodeW HS hne s c hA).1⟩

end Main

/-! ## The source controls' facts -/

/-- **A source control's facts `W2` asks at no frame beyond `SFacts`**: its
frame runs free of `ZBad` (`FrOk2`), not at an overflow (so no abort site
is a pc of its states), placed at no frame under the labels' placement
`L0`. -/
def MainCtl (Λ : Scc.Sem.Layout) (L0 : Lbl) (c : Ctl) : Prop :=
  FrOk2 c [] ∧ ¬ OvfReady c ∧ ∀ s, PlacedS Λ L0 s c []

section Ctl

variable {W W1 W2 : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {Q : Ctl → Prop}

/-- A block's states meet a control predicate its node's invariant gives,
with no outside moves. -/
theorem BlkW.ofCtl {n : ND} {blk : List Directive} (hq : ∀ σ c, n.J σ c → Q c) :
    BlkW (fun _ c => Q c) (fun _ _ => False) exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨hq σ c hJ, fun _ h => h⟩

/-- A node's states meet a control predicate its invariant gives, with no
outside moves. -/
theorem NodeW.ofCtl {n : ND} (hq : ∀ σ c, n.J σ c → Q c) :
    NodeW (fun _ c => Q c) (fun _ _ => False) exe endPc R F n :=
  fun _ c ⟨_, _, _, _, σ, _, _, hJ⟩ => ⟨hq σ c hJ, fun _ h => h⟩

/-- **`scc_rt_main`'s own states after a setup block meet a control
predicate** `Q` of the entry's control (`hC0`), of every control `PostS`
relates (`hPS`) and of every control `Post` relates (`hP`). -/
theorem MainSW.ofCtl {ms : MemSide isaLSE2} {sc : SetupCode} {PostS : Ctl → Reg64s → Prop}
    {Post : Ctl → BitVec 64 → Prop} {g : Spike.Lib.A64.Flow.Ret0.MainG} {x0 : BitVec 64} (hC0 : Q g.c0)
    (hPS : ∀ c rs, PostS c rs → Q c) (hP : ∀ c v, Post c v → Q c) :
    MainSW (fun _ c => Q c) (fun _ _ => False) exe endPc R F ms sc PostS Post g x0 :=
  ⟨⟨BlkW.ofCtl fun _ _ hJ => hJ.1.1 ▸ hC0, NodeW.ofCtl fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ hC0,
      BlkW.ofCtl fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0, BlkW.ofCtl fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0⟩,
    BlkW.ofCtl fun _ _ hJ => hJ.1 ▸ hC0, BlkW.ofCtl fun _ _ hJ => hPS _ _ hJ.1,
    ⟨BlkW.ofCtl fun _ _ hJ => hP _ _ hJ, NodeW.ofCtl fun _ _ ⟨_, _, hJ, _⟩ => hP _ _ hJ⟩⟩

/-- **`scc_rt_main`'s own states after a setup block inside `W`** from
two, the second not moved. -/
theorem MainSW.imp {ms : MemSide isaLSE2} {sc : SetupCode} {PostS : Ctl → Reg64s → Prop}
    {Post : Ctl → BitVec 64 → Prop} {g : Spike.Lib.A64.Flow.Ret0.MainG} {x0 : BitVec 64}
    (h1 : MainSW W1 K exe endPc R F ms sc PostS Post g x0)
    (h2 : MainSW W2 (fun _ _ => False) exe endPc R F ms sc PostS Post g x0)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : MainSW W K exe endPc R F ms sc PostS Post g x0 :=
  ⟨⟨Spike.Lib.A64.AllocG.BlkW.imp h1.pro.w0 h2.pro.w0 hw, Spike.Lib.A64.AllocG.NodeW.imp h1.pro.w1 h2.pro.w1 hw,
      Spike.Lib.A64.AllocG.BlkW.imp h1.pro.w2 h2.pro.w2 hw, Spike.Lib.A64.AllocG.BlkW.imp h1.pro.w3 h2.pro.w3 hw⟩,
    Spike.Lib.A64.AllocG.BlkW.imp h1.call0 h2.call0 hw, Spike.Lib.A64.AllocG.BlkW.imp h1.sp0 h2.sp0 hw,
    ⟨Spike.Lib.A64.AllocG.BlkW.imp h1.exit.w0 h2.exit.w0 hw,
      Spike.Lib.A64.AllocG.NodeW.imp h1.exit.w1 h2.exit.w1 hw⟩⟩

end Ctl

/-- **`W2` at a runtime state at no frame, at a source control**: `SFacts`
at the control, `RtM`, and the control's `MainCtl` (`rtX_w2G` at any
control). -/
theorem rtM_w2 {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {rS : Range}
    {Tk : State → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl} {lsize : Lsize} (hp : ProgNoS ZBad p)
    {s : State} {c : Ctl} (hS : SFacts Λ μ own rS Tk lbl0 s c) (hM : RtM μ ar lab s c) (hQ : MainCtl Λ lbl c) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c [] := by
  have hP := w2Part_of_wrOff (J := J) (rd := rd) (G := G) (p := p) (lsize := lsize) hM.1 (hQ.2.2 s) hM.2 hS
  exact w2_of hp hQ.1 (hS.toSt.dt_mono fun _ h => h.elim) hP.1 (fun _ => hS.noRet) (.of_placedS hP.2.1) hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts hQ.2.1 hS)) hP.2.2.2

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
/-- **`scc_rt_main`'s own states after a setup block inside `W2At`**
(`h0_ofPlaceOK`'s `hW` at `setupMC sw`) at a placed output: `mainSW_sfacts`
and `mainSW_rtM` at the record, joined by `rtM_w2` with the source controls'
`MainCtl` (`MainSW.ofCtl`); left: the code and phase facts at `sw`
(`hsw`, `hc`, `hph`, from `mainPhS_of_placeOKAt`), the three targets
positioned off the write abort (`hgrow`, `hset`, `hfn`), the controls'
facts at the entry (`hC0`, `hQ0`), after the setup block (`hCS`, `hQS`) and
at the return point (`hCP`, `hQP`), and the frame inside the switch region
(`hLZ`). -/
theorem mainSW_ofPlaceOK {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {ab : Option (State → Prop)} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p)
    (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 8) (hc : Spike.Lib.A64.Rt.rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    (hLZ : (setupMC sw).Z.toInt ≤ L)
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hC0 : CFacts (Ly).Λ lbl0 c0) (hCS : ∀ c rs, PostS c rs → CFacts (Ly).Λ lbl0 c)
    (hCP : ∀ c v, Post c v → CFacts (Ly).Λ lbl0 c)
    (hQ0 : MainCtl (Ly).Λ (fun _ => none) c0) (hQS : ∀ c rs, PostS c rs → MainCtl (Ly).Λ (fun _ => none) c)
    (hQP : ∀ c v, Post c v → MainCtl (Ly).Λ (fun _ => none) c) :
    ∀ v, MainSW (Spike.Lib.A64.Rt.nilW (W2At h i p rd (rS0 (Ly)) J Dt ls0))
      (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v) (MSAt h i p rd J ab ls0 [])
      (setupMC sw) PostS Post
      ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
      (pinA (Ly).lab + 0#64 + 8#64) := by
  intro v
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hin := Spike.Lib.A64.Rt.mainSIn_of_okS hc
    have hZ := setupMC_Z sw hsw
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
    have h16 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
    have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) false
        ⟨limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
      rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
      exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
    have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
    refine MainSW.imp
      (Spike.Lib.A64.Rt.mainSW_sfacts (lbl := lbl0) hI hin hC0 hCS hCP hph
        hok h16 (by show -L ≤ _; omega) (Int.le_refl _) (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by rw [hZ]; omega) (by rw [hZ]; omega) (show sw ≤ 7 by omega)
        (by show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, setupMC_k sw hsw]; refine ⟨?_, ?_, ?_⟩ <;> omega)
        hmr (fun _ hm => hm.1.2) hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (fun _ hm => hm.2))
      (MainSW.imp (W := fun s c => RtM (Spike.Lib.A64.PhRec.μ (Ly)) (Spike.Lib.A64.Rt.arOf (Ly).Λ) (Ly).lab s c ∧
          MainCtl (Ly).Λ (fun _ => none) c) (mainSW_rtM hI (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h)
          (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hsw hin hph hgrow hset hfn hok h16
          (by show -L ≤ _; omega) (Int.le_refl _) (fun _ hm => hm.1.2))
        (MainSW.ofCtl hQ0 hQS hQP) fun _ _ h1 h2 => ⟨h1, h2⟩)
      fun s c hS ⟨hM, hQ⟩ => rtM_w2 hp hS hM hQ
  · exact Spike.Lib.A64.Rt.mainSW_ofFalse fun m hm => hv hm.1.1

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (swFSL rS0) in
/-- **The setup block's call node inside `W2At`** (`h0_ofPlaceOK`'s `hWC`
at `setupMC sw`) at a placed output: `rtM_sfacts_setupEntry` at the record,
joined by `rtM_w2` with the entry's control's `MainCtl` (`hQ0`); left: the
setup function's prologue (`hpro`), its head's phase facts (`hph`), its
stack check label off the write abort (`hl`), and the entry's control's
`CFacts` (`hC0`). -/
theorem hWC_ofPlaceOK {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
    {ls0 : Lsize} {c0 : Ctl} {L : Int} (hp : ProgNoS ZBad p) (hL0 : 0 ≤ L) (hL : L ≤ 16384) (hL8 : L % 8 = 0)
    {sc : SetupCode} {chk entry : Label} {Z lim : Int64} {Lg : Label} {ps : List (XReg × Int64)}
    (hpro : prologueIn (Ly).prog sc.setup chk entry Z lim Lg ps = true)
    (hph : blkPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab chk + Int64.ofNat (4 * 0)) 0 (chkHead Z) = true)
    (hl : chk ∉ abLabs) (hC0 : CFacts (Ly).Λ lbl0 c0) (hQ0 : MainCtl (Ly).Λ (fun _ => none) c0) :
    ∀ v s c, Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (swR v (-L) 0)
      (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64) (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (Spike.Lib.A64.Rt.mainSC (Ly).lab sc
        ⟨stacksA (Ly).lab + 0#64 + 16384#64, UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64), c0⟩
        (pinA (Ly).lab + 0#64 + 8#64)) s c → W2At h i p rd (rS0 (Ly)) J Dt ls0 s c [] := by
  intro v
  by_cases hv : v = stacksA (Ly).lab + 0#64 + 16384#64
  · subst hv
    have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS0 (Ly))
    have hok : (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hL
    have h16 : (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
    have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
    intro s c hA
    obtain ⟨hM, hS⟩ := rtM_sfacts_setupEntry (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ) (lbl0 := lbl0) hI
      (Scc.Cert.PlaceOK.A64.printIn_of_placeOKAt h) (Scc.Cert.PlaceOK.A64.abortIn_of_placeOKAt h) hpro hph hl
      hok h16 (Int.le_refl _) (Int.le_refl _) (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
      hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (fun _ hm => hm.2) hC0 s c hA
    obtain ⟨-, -, -, -, _, -, -, hJ⟩ := hA
    exact rtM_w2 hp hS hM (hJ.1.1 ▸ hQ0)
  · rintro s c ⟨-, -, -, -, -, -, hD, -⟩
    exact (hv hD.1.1).elim

open Spike.Lib.A64.Flow.Ret0 in
open Spike.Lib.A64.Rt (SetupCallWS MainCallWS SetupArgs swFSL rS0 entryR rtF) in
/-- **The consumer's `h0` at a placed output with a setup block**
(`h0_ofPlaceOK` at `setupMC sw`, `hW` from `mainSW_ofPlaceOK`): the frame's
facts decided at `sw < 8`, the start control's `MainCtl` from `hf0`, `hov`,
`hpl0`; left beyond `h0_ofPlaceOK`'s: the code and phase facts at `sw`
(`hc`, `hph`), the three targets off the write abort (`hgrow`, `hset`,
`hfn`), the source controls' facts under `PostS` and `Post`
(`hPostS`, `hPost`), the setup call's target and frame pop (`hcall`,
`hPS`), and, for `hWC_ofPlaceOK`, the setup function's prologue, its
head's phase facts and its stack check label off the write abort
(`hproS`, `hphS`, `hlS`). -/
theorem h0_ofPlaceOK_setup {p : Prog} {rd : TermRun.Word → Prop} {J : InvS} {Dt : State → Prop} {lbl0 : Lbl}
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
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hL1 : (setupMC sw).Z.toInt + D1 ≤ L) (hL2 : (setupMC sw).Z.toInt + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - (setupMC sw).Z.toBitVec - ZU2.toBitVec).toNat)
    (hPostS : ∀ c rs, PostS c rs → CFacts (Ly).Λ lbl0 c ∧ MainCtl (Ly).Λ (fun _ => none) c)
    (hPost : ∀ c v, Post c v → CFacts (Ly).Λ lbl0 c ∧ MainCtl (Ly).Λ (fun _ => none) c)
    (hS : ∀ v, SetupCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).e0 + 4).toBitVec c0
      (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.A64.Flow.CallTo p c0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.A64.Flow.CallTo p c0 cE fr → PostR c rs →
      ∃ c'', Spike.Lib.FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    {chk entry : Label} {Zs lim : Int64} {Lg : Label} {ps : List (XReg × Int64)}
    (hproS : prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg ps = true)
    (hphS : blkPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab chk + Int64.ofNat (4 * 0)) 0 (chkHead Zs) = true)
    (hlS : chk ∉ abLabs)
    (hU : ∀ v, MainCallWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSAt h i p rd J ab ls0) (Ly).exe (Ly).endPc
      (swR v (-L) 0) (swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) v)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2 (SetupArgs PostS (setupMC sw).sw (pinA (Ly).lab + 0#64 + 8#64)) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R' F' ⟨(Ly).lab (setupMC sw).sp1 + 4 + 4 + 4,
        ⟨-(setupMC sw).Z.toInt, []⟩, fun σ _ => σ.regs.X0.toBitVec = v⟩ s c →
        ¬ (MSAt h i p rd J ab ls0 []).abortAt s → MainExitS p (MSAt h i p rd J ab ls0 []) s c v.toNat) :
    SegWS (W2At h i p rd (rS0 (Ly)) J Dt ls0) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p (fun _ => none)
      (MSAt h i p rd J ab ls0)
      ((Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (entryR E) FE (entryN (Ly).lab c0)).at [])
      fun _ _ _ => False := by
  have hZ := setupMC_Z sw hsw
  have hW := mainSW_ofPlaceOK h i (rd := rd) (J := J) (Dt := Dt) (ls0 := ls0) (ab := ab) hp hL0 hL hL8 hsw hc hph
    hgrow hset hfn (by omega) hC0 (fun c rs h => (hPostS c rs h).1) (fun c v h => (hPost c v h).1)
    ⟨hf0, hov, hpl0⟩ (fun c rs h => (hPostS c rs h).2) (fun c v h => (hPost c v h).2)
  have h16 : (setupMC sw).Z.toInt % 16 = 0 := by rw [hZ]; omega
  have hZ16 : 16 ≤ (setupMC sw).Z.toInt := by rw [hZ]; omega
  have hZw : 8 * ((setupMC sw).sw : Int) + 8 ≤ (setupMC sw).Z.toInt := by
    show 8 * (sw : Int) + 8 ≤ _; rw [hZ]; omega
  have hk : Spike.Lib.offOk (-(setupMC sw).Z.toInt) 0 (-(setupMC sw).Z.toInt + (setupMC sw).k.toInt) = true := by
    simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, setupMC_k sw hsw]; refine ⟨?_, ?_, ?_⟩ <;> omega
  have hsw7 : (setupMC sw).sw ≤ 7 := show sw ≤ 7 by omega
  exact h0_ofPlaceOK h i hE hFE hFEs hFEk hp hf0 hov hC0 hpl0 hL0 hL hL8
    (Spike.Lib.A64.Rt.mainSIn_of_okS hc) h16 hZ16 hsw7 hZw hk hD10 hD18 hD20 hD28 hL1 hL2 hZM hZS hZU hS hcall hPS
    (hWC_ofPlaceOK h i (sc := setupMC sw) hp hL0 hL hL8 hproS hphS hlS hC0 ⟨hf0, hov, hpl0⟩) hU hexit hW

end Place

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.mainSW_rtM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_rtM

/-- info: 'Spike.Lib.LowerA64.rtM_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_w2

/-- info: 'Spike.Lib.LowerA64.mainSW_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.rtM_sfacts_setupEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_sfacts_setupEntry

/-- info: 'Spike.Lib.LowerA64.hWC_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hWC_ofPlaceOK

end Spike.Lib.LowerA64
