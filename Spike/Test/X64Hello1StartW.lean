/-
**`hello1.w`'s start inside `Wr` up to `scc_rt_main`'s entry** (x86-64):
the obligations `StartEW` (`Spike/Lib/Rt/X64StartE.lean`) of `hello1.x`'s
`_start` and `scc_rt_start` at its hand instance (`Wr`, `Kr`,
`Spike/Lib/X64Hello1I.lean`), `scc_rt_thread_init` returning to `.x8`
(after `scc_rt_main`'s setup block), from the generic block and node lemmas
(`Spike/Lib/Rt/X64RtW.lean`) at `hello1_instOk` and the code checks
`hello1_rtCodeInTi`. This is the premise `hW` of `hello1_setup_chainWS`
(`Spike/Test/X64Hello1SetupChain.lean`) at `Wr` and `Kr` (with the setup
control: any `c0` with `CFacts`).

- `hello1_tiPhAt`, `hello1_takePhX8`: `scc_rt_thread_init`'s phase facts
  returning to `.Lscc_rt_start.x1` with its return point at `.x8`, and
  `scc_rt_stack_take`'s returning to `.x8`, each decided by the kernel
  (`ret0_tiPh`, `ret0_takePh` at `.x7`, `Spike/Test/X64RtTi.lean`,
  `Spike/Test/X64RtTake.lean`).
- `entryW`: `_start`'s three nodes (`entryW_of_instOk`).
- `st0W`: `scc_rt_start` up to `.x0` (as `st0W_gen`,
  `Spike/Lib/Rt/X64RtStartU.lean`), `scc_rt_alloc_tcb` by the hand `tcbW`.
- `x0WAt`: from `.x0` to the switch (as `x0WAt_gen`),
  `scc_rt_thread_init` by `tiWAt_gen` at `.x8`; the TCB's six words among
  `hello1Words` (`hello1_tiAddrs`), the stack range off the region (`hout`).
- `swEW`: the switch, `xorl %ebp, %ebp` and the call block (as `swUW_gen`'s
  first three parts, `Spike/Lib/Rt/X64RtMainU.lean`).
- `startEW`: all of it, `scc_rt_start` in `_start`'s call's callee region
  at `n0 = 0`; `startEW_c0` at the source start `c0`.
-/
import Spike.Test.X64Hello1RtW
import Spike.Test.X64Hello1StartE
import Spike.Lib.Rt.X64RtStartU
import Spike.Lib.Rt.X64EntryW
import Spike.Lib.Rt.X64RtMainU

namespace Spike.Test.X64Hello1StartW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib (Ctl Region)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero' startE siSig xStart0 xStart0_ok xStartArgs xStartArgs_ok startIn)
open Spike.Lib.X64.Flow.Ret0 (St0W StackM pinA lockA freeNA nextA stacksA limA tpOf x0L x1L startCall_ok
  startCall2_ok startFs_ok startSw_ok startCallIn startCall2In startTailIn stackM_stable startMain)
open Spike.Lib.X64.Rt
open Spike.Lib.X64.Rt.StartU (xStart0_noRet xStartArgs_noRet startCall_noRet startCall2_noRet startFs_noRet
  startSw_noRet startE41)
open Spike.Lib.X64.Rt.MainU (startMain_noRet)
open Spike.Lib.X64.Rt.Ti (TiPhAt preTkPcs tiAddrs)
open Spike.Lib.X64.Rt.Take (TakePh takePcs)
open Spike.Lib.X64.Flow.Hello1.Inst (labT hello1_labT Wr Kr okPc ph Tk own ownOf μ0 bT not_tk not_own labT_pinA
  labT_lockA labT_freeNA labT_nextA tcbW)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End hello1Words hello1F hello1Words_mapped)
open Spike.Test.X64Hello1RtW (hello1_instOk)
open Spike.Lib.X64.Rt.Test (hello1_rtCodeInTi)
open SccCode (hello1Λ hello1Cells)

/-! ## The callees' phase facts at `.x8` -/

/-- The pcs of `scc_rt_thread_init` before its call, before the take. -/
theorem hello1_tiBT : ∀ p ∈ preTkPcs labT, bT p.toBitVec.toNat = true := by decide +kernel

/-- **`hello1.x`'s `scc_rt_thread_init` phase facts**, returning to
`.Lscc_rt_start.x1`, its own return point at `.x8`. -/
theorem hello1_tiPhAt : TiPhAt okPc ph Tk labT (fun _ => labT ".Lscc_rt_start.x1") x8L where
  e := by decide +kernel
  entry := by decide +kernel
  c7 := by decide +kernel
  x7 := by decide +kernel
  f1 := by decide +kernel
  f2 := by decide +kernel
  f3 := by decide +kernel
  f4 := by decide +kernel
  f5 := by decide +kernel
  ret := by decide +kernel
  st := by decide +kernel
  noTk := fun p hp s hs => not_tk (hs ▸ hello1_tiBT p hp)

/-- Every pc of `scc_rt_stack_take` before the take. -/
theorem hello1_takeBT : ∀ p ∈ takePcs labT, bT p.toBitVec.toNat = true := by decide +kernel

/-- **`hello1.x`'s `scc_rt_stack_take` phase facts**, returning to
`scc_rt_thread_init`'s `.x8`. -/
theorem hello1_takePhX8 : TakePh okPc ph Tk ownOf μ0 labT (fun _ => labT x8L) where
  e := by decide +kernel
  entry := by decide +kernel
  cls := by decide +kernel
  j1 := by decide +kernel
  d7 := by decide +kernel
  d33 := by decide +kernel
  d59 := by decide +kernel
  sp0 := by decide +kernel
  sp14 := by decide +kernel
  lk0 := by decide +kernel
  lk7 := by decide +kernel
  b7 := by decide +kernel
  b38 := by decide +kernel
  b61 := by decide +kernel
  b108 := by decide +kernel
  ok7 := by decide +kernel
  tk := by decide +kernel
  ret := by decide +kernel
  si := by decide +kernel
  swpOk := by decide +kernel
  ldnOk := by decide +kernel
  unlOk := by decide +kernel
  nxtOk := by decide +kernel
  ldnPh := by decide +kernel
  noTk := fun p hp s hs => not_tk (hs ▸ hello1_takeBT p hp)
  swpIn := by rw [labT_lockA]; exact ⟨_, .tail _ (.head _)⟩
  swpUpd := by rw [labT_lockA]; decide +kernel
  unlIn := by rw [labT_lockA]; exact ⟨_, .tail _ (.head _)⟩
  unlUpd := by rw [labT_lockA]; decide +kernel
  nxtIn := by rw [labT_nextA]; exact ⟨_, .tail _ (.tail _ (.tail _ (.head _)))⟩
  nxtUpd := by rw [labT_nextA]; decide +kernel
  siteRel := fun a ha => by cases ha; decide +kernel
  siteAb := fun k a ha => by cases k <;> cases ha <;> decide +kernel
  siteAt := by decide +kernel
  siteOwn := by decide +kernel
  tk1 := fun s hs => by show ph (pcOf s) / 8 % 2 = 0; rw [hs]; decide +kernel

/-- The first TCB, at `scc_rt_pinned + 8`. -/
theorem tcbA0 : pinA labT + 0#64 + 8#64 = 134217736#64 := by rw [labT_pinA]; decide

/-- The TCB's six words among `hello1.x`'s, owned at no phase. -/
theorem hello1_tiAddrs : ∀ a ∈ tiAddrs 134217736#64,
    a ∈ hello1Words ∧ a ∉ [6291472#64, 6291496#64, 6291504#64, 6291488#64] := by
  intro a ha
  simp only [tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- `hello1.x`'s stack pool does not wrap. -/
theorem fitS_of_sub {rS : Range} (hsub : rS.Sub hello1Λ.stackPool) : rS.lo + rS.size ≤ 2 ^ 64 := by
  have : hello1Λ.stackPool.lo + hello1Λ.stackPool.size < 2 ^ 64 := by decide +kernel
  obtain ⟨-, h⟩ := hsub; omega

variable {rS : Range} {c0 : Ctl} {F : MachineData → Prop}

/-! ## `_start` and `scc_rt_start` -/

/-- **`_start`'s nodes are inside `Wr`**, in a region with room for the
call's return address. -/
theorem entryW (hC0 : CFacts hello1Λ hello1Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -8)
    (hhi : 0 ≤ R.hi) : EntryW (Wr rS) (Kr rS) hello1Exe hello1End R F labT c0 :=
  entryW_of_instOk hello1_instOk hello1_rtCodeInTi.start0 hR hlo hhi hC0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ hs => not_tk (by rw [hs]; decide +kernel)) (fun _ hs => not_tk (by rw [hs]; decide +kernel))
    (fun _ hs => not_tk (by rw [hs]; decide +kernel))

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_start` up to `.x0` is inside `Wr`** (`St0W`), in any region
holding its frame and `scc_rt_alloc_tcb`'s below, at `n0 = 0`, with the
source control `c0` (`hC0`, its facts) and the frame condition implying
`hello1F`. -/
theorem st0W (hC0 : CFacts hello1Λ hello1Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -296)
    (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → hello1F m) :
    St0W (Wr rS) (Kr rS) hello1Exe hello1End R F 0#64 c0 := by
  have hst := hello1_rtCodeInTi.start
  simp only [startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨-, cb0⟩, cbSi⟩, cbArgs⟩, cbSys⟩ := hst
  have hcl := hello1_rtCodeInTi.call
  simp only [startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun g hg j => ?_⟩
  · -- The frame's setup.
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_pre (dead := fun _ => false) (ra := 0) hello1_instOk cb0 (ofNat_zero' _) xStart0_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r => (noRet_false xStart0_noRet k hk r).elim) (fun _ _ _ => rfl)
      (fun _ hs => not_tk (by rw [hs]; decide +kernel))
  · -- The handler's `lea`.
    show NodeW _ _ _ _ _ _ _
    rw [hello1_labT]
    exact nodeW_si_pre (si := siSig) (p := labT startE + Int64.ofNat 0) hello1_instOk cbSi rfl
      (ofNat_zero' _).symm (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) (by decide +kernel)
      (fun _ hs => not_tk (by rw [hs]; decide +kernel)) (by decide +kernel)
  · -- The arguments.
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_pre (dead := fun _ => false) (ra := 0) hello1_instOk cbArgs rfl xStartArgs_ok hR
      (by omega) (by omega) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r => (noRet_false xStartArgs_noRet k hk r).elim) (fun _ _ _ => rfl)
      (fun _ hs => not_tk (by rw [hs]; decide +kernel))
  · -- `rt_sigaction`'s `syscall`.
    show NodeW _ _ _ _ _ _ _
    rw [hello1_labT]
    exact nodeW_syscall_pre (p := labT startE + Int64.ofNat 41) hello1_instOk cbSys rfl (startE41 labT)
      (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) (by decide +kernel) (fun _ hs => not_tk (by rw [hs]; decide +kernel))
      (by decide +kernel) (fun _ _ ⟨_, _, he⟩ => by rw [he, Flow.Ret0.Inst.startS2_rax]; decide)
  · -- The call block.
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_pre (dead := fun _ => false) (ra := 0) hello1_instOk cc rfl startCall_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r => (noRet_false startCall_noRet k hk r).elim) (fun _ _ _ => rfl)
      (fun _ hs => not_tk (by rw [hs]; decide +kernel))
  · -- `scc_rt_alloc_tcb`.
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -184) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    rw [hello1_labT] at hg
    exact tcbW hC0 hR' (by show (-184 : Int) ≤ -184; omega) (by show (8 : Int) ≤ 8; omega) hFr
      ⟨g, 0#64, c0⟩ rfl rfl hg j

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_start` from `.x0` to the switch is inside `Wr`** (`X0WAt` at
`.x8`), in any region holding its frame and `scc_rt_thread_init`'s and
`scc_rt_stack_take`'s below, at `n0 = 0`, with the source control `c0`
(`hC0`), the frame condition implying `hello1F`, the take's range `rS` at
`k0` (`hrS`) in the pool (`hsub`) and off the region (`hout`). -/
theorem x0WAt (hC0 : CFacts hello1Λ hello1Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -296)
    (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → hello1F m) {k0 : BitVec 64}
    (hrS : rS = ⟨(stacksA labT + k0).toNat, 16384⟩) (hsub : rS.Sub hello1Λ.stackPool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) :
    X0WAt (Wr rS) (Kr rS) hello1Exe hello1End R F rS 0#64 k0 c0 x8L := by
  have hfit := fitS_of_sub hsub
  have hSM := stackM_stable hfit hout
  have hcl2 := hello1_rtCodeInTi.call2
  simp only [startCall2In, Bool.and_eq_true] at hcl2
  obtain ⟨cc2, -⟩ := hcl2
  have htl := hello1_rtCodeInTi.tail
  simp only [startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨tFs, tSys⟩, tSw⟩, -⟩, -⟩, -⟩ := htl
  refine ⟨?_, fun g hg i => ?_, ?_, ?_, ?_⟩
  · -- `.x0`'s block.
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_pre (dead := fun _ => false) (ra := 0) hello1_instOk cc2 (ofNat_zero' _) startCall2_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r => (noRet_false startCall2_noRet k hk r).elim) (fun _ _ _ => rfl)
      (fun _ hs => not_tk (by rw [hs]; decide +kernel))
  · -- `scc_rt_thread_init`, returning to `.x1`, its take returning to `.x8`.
    have hR1 := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    have ho1 := Flow.Ret0.Inst.out_callee hR (kc := -48 - 0) (lo' := -248) (hi' := 8) (by omega) (by decide)
      (by omega) (by omega) hout
    have ho2 := Flow.Ret0.Inst.out_callee hR1 (kc := -48 - 0) (lo' := -200) (hi' := 8)
      (by show (-248 : Int) ≤ _; omega) (by decide) (by show (-48 - 0 : Int) < 8; omega)
      (by show (-48 - 0 + 8 : Int) ≤ 8; omega) ho1
    have hta : ∀ a ∈ tiAddrs (pinA labT + 0#64 + 8#64),
        a ∈ hello1Words ∧ a ∉ [6291472#64, 6291496#64, 6291504#64, 6291488#64] :=
      fun a ha => hello1_tiAddrs a (by rw [← tcbA0]; exact ha)
    rw [hello1_labT] at hg ⊢
    exact tiWAt_gen (ownOf := ownOf) hello1_instOk (fun _ => rfl) hello1_rtCodeInTi.ti hC0 hR1
      (by show (-248 : Int) ≤ -248; omega) (by show (8 : Int) ≤ 8; omega) ⟨g, pinA labT + 0#64 + 8#64, k0, c0⟩
      rfl hg hello1_tiPhAt
      (fun a ha => (hello1Words_mapped (hta a ha).1).1)
      (fun a ha m hm => hFr m hm a (hta a ha).1)
      (fun a ha => not_own (hta a ha).2)
      hsub (stackM_stable hfit ho1) (stackM_stable hfit ho2) hello1_rtCodeInTi.take hello1_takePhX8
      (by rw [labT_lockA]; exact (hello1Words_mapped (by decide)).1)
      (by rw [labT_freeNA]; exact (hello1Words_mapped (by decide)).2.1)
      (by rw [labT_nextA]; exact (hello1Words_mapped (by decide)).1)
      (fun m hm => by rw [labT_lockA]; exact hFr m hm _ (by decide))
      (fun m hm => by rw [labT_freeNA]; exact hFr m hm _ (by decide))
      (fun m hm => by rw [labT_nextA]; exact hFr m hm _ (by decide))
      hrS (by unfold Scc.Sem.Range.Disjoint; decide +kernel) i
  · -- `.x1`'s block.
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_post (dead := fun _ => false) (ra := 0) hello1_instOk tFs (ofNat_zero' _) startFs_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r => (noRet_false startFs_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM
  · -- `arch_prctl`'s `syscall`.
    show NodeW _ _ _ _ _ _ _
    rw [hello1_labT]
    exact nodeW_syscall_post (p := labT x1L + Int64.ofNat 18) hello1_instOk tSys rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel) (by decide +kernel) hsub (fun _ _ hJ => by rw [hJ.2.1]; decide)
  · -- The block before the switch.
    show BlkW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact blkW_post (dead := fun _ => false) (ra := 0) hello1_instOk tSw rfl startSw_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel)
      (fun _ _ _ k hk r => (noRet_false startSw_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM

set_option maxHeartbeats 800000 in
/-- **From the switch to `call scc_rt_main`, inside `Wr`** (`SwEW`): the
switch in any region with the stack range in private memory; `xorl %ebp,
%ebp` and the call block in the new stack's region of depth `L` (8-aligned,
at least `8`) at its 8-aligned top `top` (vacuous off it), `rS` in the pool. -/
theorem swEW (hC0 : CFacts hello1Λ hello1Λ.static c0) {R : Region} {tcb top : BitVec 64} {L : Int}
    (h8 : top.toNat % 8 = 0) (hok : (swR top (-L) 0).OK) (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hsub : rS.Sub hello1Λ.stackPool) :
    SwEW (Wr rS) (Kr rS) hello1Exe hello1End R (fun m => F m ∧ StackM rS m) rS tcb top c0 L := by
  have hfit := fitS_of_sub hsub
  have h := hello1_rtCodeInTi.tail
  simp only [startTailIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, bSw⟩, bXor⟩, bMain⟩ := h
  refine ⟨?_, fun v => ?_, fun v => ?_⟩
  · show NodeW _ _ _ _ _ _ _
    rw [hello1_labT]
    exact nodeW_reg_post (p := labT x1L + Int64.ofNat 28) hello1_instOk (by rfl) bSw rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel) (by decide +kernel) hsub
  · by_cases hv : v = top
    · subst hv
      show NodeW _ _ _ _ _ _ _
      rw [hello1_labT]
      exact nodeW_fi_postO (p := labT x1L + Int64.ofNat 31) hello1_instOk bXor rfl rfl
        (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel) (by decide +kernel) hok h8
        (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) hsub (fun _ h => h.2)
    · exact nodeW_ofFalse fun _ h => hv h.1.1
  · by_cases hv : v = top
    · subst hv
      show BlkW _ _ _ _ _ _ _ _
      rw [hello1_labT]
      exact blkW_postO (dead := fun _ => false) (ra := 0) hello1_instOk bMain rfl (startMain_okL hL) hok
        (Int.le_refl _) (Int.le_refl _) h8 (by show (-L) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
        (fun _ _ hJ => hJ.1 ▸ hC0) (by decide +kernel)
        (fun _ _ _ k hk r => (noRet_false startMain_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hfit
        (fun _ h => h.2)
    · exact blkW_ofFalse fun _ h => hv h.1.1

/-! ## The start -/

/-- **`hello1.x`'s start is inside `Wr` up to `scc_rt_main`'s entry**
(`StartEW` at `n0 = 0`, `scc_rt_thread_init` returning to `.x8`): `_start`
in a region holding `scc_rt_start`'s callee region (`hR`, `hlo`, `hhi`), the
source control `c0` (`hC0`), the frame condition implying `hello1F`, the
take's range at `k0` (`hrS`) in the pool (`hsub`) and off the region
(`hout`), the new stack's region of depth `L` at its top (`h8`, `hok`,
`hL`, `hL8`). -/
theorem startEW (hC0 : CFacts hello1Λ hello1Λ.static c0) {R : Region} (hR : R.OK) (hlo : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → hello1F m) {k0 : BitVec 64} {L : Int}
    (hrS : rS = ⟨(stacksA labT + k0).toNat, 16384⟩) (hsub : rS.Sub hello1Λ.stackPool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (h8 : (stacksA labT + k0 + 16384#64).toNat % 8 = 0) (hok : (swR (stacksA labT + k0 + 16384#64) (-L) 0).OK)
    (hL : 8 ≤ L) (hL8 : L % 8 = 0) :
    StartEW (Wr rS) (Kr rS) hello1Exe hello1End R F rS 0#64 k0 c0 L x8L := by
  refine ⟨?_, fun F' _ _ hF' => ?_⟩
  · show EntryW _ _ _ _ _ _ _ _
    rw [hello1_labT]
    exact entryW hC0 hR (by omega) hhi
  · have hR' := Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    have ho := Flow.Ret0.Inst.out_callee hR (kc := -8) (lo' := -296) (hi' := 8) (by omega) (by decide)
      (by omega) (by omega) hout
    have hFr' : ∀ m, F' m → hello1F m := fun m hm => hFr m (hF' m hm)
    refine ⟨st0W hC0 hR' (by show (-296 : Int) ≤ -296; omega) (by show (8 : Int) ≤ 8; omega) hFr',
      x0WAt hC0 hR' (by show (-296 : Int) ≤ -296; omega) (by show (8 : Int) ≤ 8; omega) hFr' hrS hsub ho, ?_⟩
    show SwEW _ _ _ _ _ _ _ (pinA (_root_.Executable.labels hello1Exe).label + 0#64 + 8#64)
      (stacksA (_root_.Executable.labels hello1Exe).label + k0 + 16384#64) _ _
    rw [hello1_labT]
    exact swEW hC0 h8 hok hL hL8 hsub

/-- **`startEW` at the source start `c0`** (`cfacts_c0`). -/
theorem startEW_c0 {R : Region} (hR : R.OK) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → hello1F m)
    {k0 : BitVec 64} {L : Int} (hrS : rS = ⟨(stacksA labT + k0).toNat, 16384⟩) (hsub : rS.Sub hello1Λ.stackPool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (h8 : (stacksA labT + k0 + 16384#64).toNat % 8 = 0) (hok : (swR (stacksA labT + k0 + 16384#64) (-L) 0).OK)
    (hL : 8 ≤ L) (hL8 : L % 8 = 0) :
    StartEW (Wr rS) (Kr rS) hello1Exe hello1End R F rS 0#64 k0 Spike.Lib.X64Consumer.c0 L x8L :=
  startEW Flow.Ret0.Inst.cfacts_c0 hR hlo hhi hFr hrS hsub hout h8 hok hL hL8

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.X64Hello1StartW.hello1_tiPhAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_tiPhAt

/--
info: 'Spike.Test.X64Hello1StartW.hello1_takePhX8' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_takePhX8

/--
info: 'Spike.Test.X64Hello1StartW.startEW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms startEW

/--
info: 'Spike.Test.X64Hello1StartW.startEW_c0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms startEW_c0

end Spike.Test.X64Hello1StartW
