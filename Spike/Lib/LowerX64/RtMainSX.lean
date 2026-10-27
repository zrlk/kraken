/-
**`scc_rt_main` after a setup block inside `SFacts`** (x86-64): the twin of
`Spike/Lib/Rt/A64RtMainS.lean`'s `mainSW_sfacts`, at `setupMC sw`.

- `mainSW_sfacts`: `MainSW` inside `SFacts` at `setupMC sw` (`sw < 6`), for
  any program with its code (`mainSIn`), with the source control's facts at
  the entry (`hC0`), back from the setup block under `PostS` (`hPostS`) and
  back from the user function under `Post` (`hPost`), its phase facts
  (`MainPhS`), the limit word mapped (`hmr`) and unmapped in private memory
  under the frame condition (`hun`), in any 8-aligned region holding its
  frame and the return address its calls push, its frame condition giving
  the words of `rS` off it (`hFO`). As `mainUW_gen`
  (`Spike/Lib/Rt/X64RtMainU.lean`), with the setup call and the
  marshalling block in place of the user call;
- `xHead_ok_at`: the prologue's head covered at any 8-aligned `sp`;
- `rtM_sfacts_setupEntry`: the setup call's node (`mainSC`, at the setup
  function's label with the entry's control) inside `RtM` and `SFacts`,
  from the setup function's prologue head.
-/
import Spike.Lib.LowerX64.RtMainX

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64 (NodeW BlkW ND classify okBlk okBlk_callB)
open Spike.Lib.X64.Flow (ofNat_zero' ofNat_add' xHead xLea xCmp xFr xExit xS2 xS1 hdRegs xHead_ok xLea_ok xCmp_ok
  xFr_ok xExit_ok prologueIn exitIn)
open Spike.Lib.X64.Flow.Ret0 (MainG StackOff limA)
open Spike.Lib.X64.Rt (InstOk SetupCode setupMC marshal MainSW mainSIn okBlk_marshal blkW_postO nodeW_fsld_postO
  nodeW_syscall_postO)
open Spike.Lib.X64.Rt.MainU (xHead_noRet xLea_noRet xCmp_noRet xFr_noRet callB_noRet xExit_noRet)
open Scc.Cert.Rt.X64 (blockAtB label_labelGapB)

section Main

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {lbl : Lbl}

set_option maxHeartbeats 800000 in
/-- **`scc_rt_main`'s own states after a setup block are inside `SFacts`**
(`MainSW` at `setupMC sw`, `sw < 6`), for any program with its code
(`hin`): the source control's facts at the entry (`hC0`), back from the
setup block (`hPostS`) and from the user function (`hPost`), its phase
facts (`hph`), the limit word `limA g.tp` mapped (`hmr`) and unmapped in
private memory under the frame condition (`hun`), in any 8-aligned region
holding its frame and the return address its calls push (`hlo`), `rS` in
the pool (`hsub`) and not wrapping (`hfit`), the frame condition giving the
words of `rS` off the region (`hFO`). -/
theorem mainSW_sfacts {ms : MemSide isa} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {sw : Nat} (hsw : sw < 6) (hin : mainSIn cells (setupMC sw) = true)
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop} {g : MainG} {x0 : BitVec 64}
    (hC0 : CFacts Λ lbl g.c0) (hPostS : ∀ c rs, PostS c rs → CFacts Λ lbl c)
    (hPost : ∀ c v, Post c v → CFacts Λ lbl c) (hph : MainPhS okPc ph lab (setupMC sw))
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (setupMC sw).Z.toInt - 8) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA g.tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA g.tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    MainSW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ms (setupMC sw) PostS Post g x0 := by
  have hZ := setupMC_Z sw hsw
  have hk := setupMC_k sw hsw
  have hm8 : (-8 : Int64).toInt = -8 := by decide
  have hmf : noRetBlk (marshal (setupMC sw).sw (setupMC sw).fn) = true ∧
      blkLabs (marshal (setupMC sw).sw (setupMC sw).fn) = [(setupMC sw).fn] ∧
      lastFalls (marshal (setupMC sw).sw (setupMC sw).fn) = false := marshal_facts sw hsw
  have h := hin
  simp only [mainSIn, prologueIn, exitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩, bCall⟩, -⟩, bMsh⟩, -⟩, bEx, bSvc⟩ := h
  have esc := label_labelGapB hI.lays hgap
  rw [hI.labOk] at esc
  have h4 : lab "scc_rt_main" + 1 + 3 = lab (setupMC sw).sc := by rw [esc, Int64.add_assoc]; rfl
  have hloZ : R.lo ≤ -8 - (setupMC sw).Z.toInt := by omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩⟩ <;> rw [hI.labOk]
  · -- the head
    exact blkW_postO hI bHd (ofNat_zero' _) (xHead_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0)
      (by omega) (Int.le_refl _)) hR hloZ hhi hR8 hl hh (fun _ _ hJ => hJ.1.1 ▸ hC0) hph.hd
      (fun _ _ _ k hk hr => (noRet_false xHead_noRet k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO
  · -- the check's address
    exact blkW_postO hI bLea (by show _ = _ + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _) hR hloZ hhi hR8 hl hh
      (fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.lea
      (fun _ _ _ k hk hr => (noRet_false (xLea_noRet _ _) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO
  · -- the limit's load
    exact nodeW_fsld_postO (p := lab (setupMC sw).sc + Int64.ofNat 5) hI bLd rfl
      (by show _ + 1 + 3 + _ = _; rw [h4]) (fun _ _ ⟨_, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.ld.1 hph.ld.2
      (fun _ _ ⟨σ0, hJ, he⟩ => by
        rw [he, show (xS2 (setupMC sw).Z σ0).regs.fsBase = σ0.regs.fsBase by simp [xS2, xS1, hdRegs, Reg64s.set64],
          hJ.1.2.2]
        rfl)
      hmr hun hR hR8 hl hh hsub hFO
  · -- the check
    have e : lab (setupMC sw).sc + Int64.ofNat 14 =
        lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 := by rw [h4, ← ofNat_add']
    exact blkW_postO hI bCmp e (xCmp_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _ _) hR hloZ hhi hR8 hl
      hh (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.cmp
      (fun _ _ _ k hk hr => (noRet_false (xCmp_noRet _ _ _) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit
      hFO
  · -- the frame
    have e : lab (setupMC sw).sc + Int64.ofNat 19 =
        lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 := by
      rw [h4, ← ofNat_add', ← ofNat_add', ← ofNat_add']
    exact blkW_postO hI bFr e (xFr_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _
        (fun p hp => by
          simp only [List.mem_singleton] at hp
          subst hp
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ, hm8]
          refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hloZ hhi hR8 hl hh (fun _ _ ⟨_, _, hJ, _⟩ => hJ.1.1 ▸ hC0) hph.fr
      (fun _ _ _ k hk hr => (noRet_false (xFr_noRet _ _ _) k hk hr).elim)
      (fun _ _ _ => rfl) hsub hfit hFO
  · -- the setup call
    exact blkW_postO hI bCall (ofNat_zero' _)
      (okBlk_callB (lo := -8 - (setupMC sw).Z.toInt - 8) (hi := 0) _ (by
        simp only [Spike.Lib.offOk, decide_eq_true_eq, Spike.Lib.X64.Rt.mainS1R, Spike.Lib.X64.Rt.oU, hZ]
        refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1.1 ▸ hC0) hph.call0
      (fun _ _ _ k hk hr => (noRet_false (callB_noRet _) k hk hr).elim) (fun _ _ _ => rfl) hsub
      hfit hFO
  · -- the marshalling block
    exact blkW_postO hI bMsh (ofNat_zero' _)
      (okBlk_marshal (lo := -8 - (setupMC sw).Z.toInt - 8) (hi := 0) (show sw ≤ 5 by omega) _
        (fun i hi => by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega)
        (by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega)
        (by
          simp only [Spike.Lib.offOk, decide_eq_true_eq, hZ]
          refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hlo hhi hR8 hl hh (fun _ _ hJ => hPostS _ _ hJ.1.1) hph.sp0
      (fun _ _ _ k hk hr => (noRet_false hmf.1 k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO
  · -- the tail's block
    exact blkW_postO hI bEx (ofNat_zero' _)
      (xExit_ok (lo := -8 - (setupMC sw).Z.toInt) (hi := 0) _ _ _ _ (by
        simp only [Spike.Lib.offOk, decide_eq_true_eq, hk, hZ]
        refine ⟨?_, ?_, ?_⟩ <;> omega))
      hR hloZ hhi hR8 hl hh (fun _ _ hJ => hPost _ _ hJ.1) hph.ex
      (fun _ _ _ k hk hr => (noRet_false (xExit_noRet _ _ _ _) k hk hr).elim) (fun _ _ _ => rfl)
      hsub hfit hFO
  · -- the `exit_group`
    exact nodeW_syscall_postO (p := lab (setupMC sw).sp1 + Int64.ofNat 13) hI bSvc rfl
      (by
        show lab (setupMC sw).sp1 + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5 = _
        rw [← ofNat_add', ← ofNat_add'])
      (fun _ _ ⟨_, _, hJ, _⟩ => hPost _ _ hJ.1) hph.svc.1 hph.svc.2 hR hR8 hl hh hsub hFO
      (fun _ _ h => by rw [h.1]; decide)

/-- **The prologue's head is covered at any `sp` offset** with no register
offsets, `sp` 8-aligned and the push's cell `8` below it inside. -/
theorem xHead_ok_at {lo hi sp : Int} (h8 : sp % 8 = 0) (hlo : lo ≤ sp - 8) (hhi : sp ≤ hi) :
    okBlk lo hi ⟨sp, []⟩ xHead = true := by
  simp [xHead, okBlk, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly, Spike.Lib.X64.AI.ok, Spike.Lib.X64.AI.so,
    Spike.Lib.X64.AI.isTerm, Spike.Lib.X64.soReg, Spike.Lib.X64.SO.get, Spike.Lib.X64.SO.set,
    Spike.Lib.X64.SO.kill, Spike.Lib.rm, Spike.Lib.offOk]
  omega

/-- **The setup block's call node is inside `RtM` and `SFacts`**
(`mainSC_segWS`'s `hWC` without the control's facts): at the setup
function's label, `8` below `scc_rt_main`'s frame (the return address
pushed), with its prologue (`hpro`: its head there, the stack check label
`chk` after it and the check's first block), the head's phase facts
(`hph`), both labels off the write abort (`hl`, `hlc`), in any 8-aligned
region holding the head's push of `%rbp` `8` further below (`hlo`): the
head's block (`blkW_rtM`, `blkW_postO` at `xHead_ok_at`, the entry's
control's `CFacts`) at its first instruction. -/
theorem rtM_sfacts_setupEntry {ar : Arena} {F : MachineData → Prop}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {sc : SetupCode} {chk entry : Label} {Z lim : Int64} {Lg : Label} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} (hpro : prologueIn cells sc.setup chk entry Z lim Lg zl zf z1 z2 zs ps = true)
    (hph : blkPh okPc ph (fun _ => false) lab (lab sc.setup + Int64.ofNat 0) 0 xHead = true)
    (hl : sc.setup ∉ Spike.Lib.X64.AllocG.abLabs) (hlc : chk ∉ Spike.Lib.X64.AllocG.abLabs)
    (hZ0 : 0 ≤ sc.Z.toInt) (hZ8 : sc.Z.toInt % 8 = 0) {R : Region} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - sc.Z.toInt - 8 - 8)
    (hhi : 0 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) {g : MainG} {x0 : BitVec 64}
    (hC0 : CFacts Λ lbl g.c0) :
    ∀ s c, Spike.Lib.X64.At exe endPc R F (Spike.Lib.X64.Rt.mainSC (_root_.Executable.labels exe).label sc g x0) s c →
      RtM μ ar lab s c ∧ SFacts Λ μ own rS Tk lbl s c := by
  simp only [prologueIn, Bool.and_eq_true] at hpro
  obtain ⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, -⟩, -⟩, -⟩, -⟩ := hpro
  have esc := label_labelGapB hI.lays hgap
  rw [hI.labOk] at esc
  have he : lab sc.setup + Int64.ofNat 0 =
      (Spike.Lib.X64.Rt.mainSC (_root_.Executable.labels exe).label sc g x0).pc := by
    show _ = (_root_.Executable.labels exe).label sc.setup
    rw [← hI.labOk]; simp
  have hok : okBlk (-8 - sc.Z.toInt - 8 - 8) 0 (Spike.Lib.X64.Rt.mainSC (_root_.Executable.labels exe).label sc g x0).o
      xHead = true :=
    xHead_ok_at (by show (-8 - sc.Z.toInt - 8) % 8 = 0; omega) (by omega) (by omega)
  have hne : xHead ≠ [] := by simp [xHead]
  have HM := blkW_rtM (ar := ar) (F := F) hI hpr hab bHd he hok hR hlo hhi (he ▸ hph) hl xHead_noRet
    (noAb_nil (by decide))
    (fun _ => by
      have := posOff_of_blockAtB (lab := lab) bLea hlc (by simp [xLea])
      rw [ofNat_zero', esc] at this
      exact this)
    (labs_nil (by decide))
  have HS := blkW_postO (lbl := lbl) (F := F) (dead := fun _ => false) (ra := 0) hI bHd he hok hR hlo hhi hR8
    hl8 hh8 (fun _ _ hJ => hJ.1.1 ▸ hC0) hph (fun _ _ _ k hk hr => (noRet_false xHead_noRet k hk hr).elim)
    (fun _ _ _ => rfl) hsub hfit hFO
  intro s c hA
  exact ⟨(BlkW.nodeW HM hne s c hA).1, (BlkW.nodeW HS hne s c hA).1⟩

end Main

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainSW_sfacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainSW_sfacts

/-- info: 'Spike.Lib.LowerX64.rtM_sfacts_setupEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtM_sfacts_setupEntry

end Spike.Lib.LowerX64
