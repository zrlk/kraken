/-
**wake.w's `scc_rt_start` at `phW`: the obligations** (x86-64; the
obligations half of `Spike/Lib/A64WakeStart.lean`): the
runtime's start from `_start` to `call scc_rt_main` inside `SFacts` at
wake.w's extended phase `phW` (`Spike/Lib/X64WakePh.lean`) with the owned
words `ownW` (the thread counter at `a`) and the canonical take's phase (bit
`3` of `phW`), for a layout of wakeCells at the canonical base:
`startEW_sfacts` (`Spike/Lib/LowerX64/StartEW2.lean`) with the facts
decided on wakeCells' labels (`Spike/Lib/X64WakeStartEWF.lean`) instead of
A6's table at a placed output.

- `instOkWS`: the instance at `phW` with `ownW` and the canonical take's
  phase.
- `entryW_wake`: `_start`'s nodes (`entryW_of_instOk`).
- `startSpW`: `scc_rt_start` up to `.x0` (`St0W`) and from `.x0` to the
  switch (`X0WAt` at `.x7`), `st0W_gen`'s and `x0WAt_gen`'s bodies with
  `tcbPhW`, `tiPhW`, `takePhW`.
- `startEW_wake`: `StartEW` (`entryW_wake`, `startSpW` in the callee region
  `R.callee (-8) (-296) 8`, `swEW_gen` with `swPhW`).

**Unlike AArch64**: the x86-64 regions (`scc_rt_start` in `_start`'s call's
callee region, the return address above every frame, `8 ≤ R.hi`), no
16-alignment (no `hal`, `h16`); the new stack's depth `D` takes `8 ≤ D`
(`hL`) besides `hL8` (`swEW_gen`); the stack range off the region (`hout`,
moved to the callees by `out_callee`, `stackM_stable`) instead of `hSM`,
`hSMi`, `hSMt`; the return point of `scc_rt_thread_init` is `.x7`
(`X0WAt`, from `X0W` by `X0W.toAt`). `scc_rt_start`'s first TCB is
`n0 = 0` (`hn0`) as on AArch64.
-/
import Spike.Lib.X64WakeStartEWF
import Spike.Lib.Rt.X64RtStartU
import Spike.Lib.Rt.X64EntryW
import Spike.Lib.Rt.X64StartE
import Spike.Lib.LowerX64.StartEW2

namespace Spike.Lib.X64.WakePh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Cert.Rt.X64 (PhFact okPcOf codeT codeT_eq factOk)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64Consumer
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (TN TK TI TcbG TiG TakeG TcbW TiW TakeW StackM pinA pnA lockA freeNA nextA stacksA
  St0W X0W x0L x1L startCall startCall2 startFs startSw startCall_ok startCall2_ok startFs_ok startSw_ok
  startCallIn startCall2In startTailIn stackM_stable)
open Spike.Lib.X64.Rt (InstOk RuntimeLayout StartEW X0WAt rtF startPhTab)
open Spike.Lib.X64.Rt.PhOfTab

section Start

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Range} {lbl : Lbl}

/-- The instance at `phW` with `ownW` and the canonical take's phase. -/
theorem instOkWS (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s)))
      (fun s => phW (pcOf s) / 8 % 2 = 0) (Spike.Lib.X64.PhRec.K L rS) (okPcOf lo wakeCells L.Λ) phW L.pfx :=
  instOkW hp hlo a (fun i => i / 8 % 2 = 0) (siteW hp hlo hlab)

/-- **`_start`'s nodes inside `SFacts`** at `phW` (`entryW_of_instOk`, as
`entryW_ofPlaceOK`), in any region with room for the call's return
address. -/
theorem entryW_wake (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hlo8 : R.lo ≤ -8) (hhi : 0 ≤ R.hi) {c0 : Ctl} (hC0 : CFacts L.Λ lbl c0) :
    Spike.Lib.X64.Rt.EntryW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS
        (fun s => phW (pcOf s) / 8 % 2 = 0) lbl s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F L.lab c0 := by
  have hrc : Spike.Lib.X64.Rt.RtCodeIn0 L.prog := hp ▸ wake_rtCodeIn0
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startW_fact hΛ (f := f) (start_memW hf)
  have hs0 := step_of_factOk hlab (hf (.step "_start" 0 2) (by simp only [startPhTab, List.mem_cons, true_or]))
  have hs2 := step_of_factOk hlab (hf (.step "_start" 2 4)
    (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hb := blkPh_of_factOk hlab (l := "_start") (o := 6) (b := Spike.Lib.X64.Rt.Code.Start.entryCall)
    (ra := none) (dead := none) (rapc := 0) (dset := fun _ => false) (fun _ _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h)
    (hf (.blk "_start" 6 Spike.Lib.X64.Rt.Code.Start.entryCall none none)
      (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hp0 := ph_of_factOk hlab (hf (.ph "_start" 0 13) (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hp2 := ph_of_factOk hlab (hf (.ph "_start" 2 13) (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hp6 := ph_of_factOk hlab (hf (.ph "_start" 6 13) (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  exact Spike.Lib.X64.Rt.entryW_of_instOk (instOkWS (a := a) (rS := rS) hp hlo hlab) hrc.start0 hR hlo8 hhi hC0
    hs0.1 hs0.2 hs2.1 hs2.2 hb (noTk_phW hp0 (by decide)) (noTk_phW hp2 (by decide)) (noTk_phW hp6 (by decide))

set_option maxHeartbeats 1600000 in
open Spike.Lib.X64.Rt Spike.Lib.X64.Rt.StartU in
/-- **`scc_rt_start`'s states up to the switch are inside `SFacts`** at
`phW` with `ownW` (`St0W`, `X0WAt` at `.x7`; `st0W_gen`'s and
`x0WAt_gen`'s bodies), the words separated (`hs`), `.rodata` off the pool
(`hro`), in any region holding its frame and its callees' below and the
return address above (`hR` … `hhi`), the stack range off it (`hout`). -/
theorem startSpW (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    {c0 : Ctl} {R : Region} {F : MachineData → Prop} {n0 k0 : BitVec 64}
    (hC0 : CFacts L.Λ lbl c0) (hR : R.OK) (hlo' : R.lo ≤ -296)
    (hhi : 8 ≤ R.hi) (hFr : ∀ m, F m → rtF L m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a) :
    St0W (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS
        (fun s => phW (pcOf s) / 8 % 2 = 0) lbl s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F n0 c0 ∧
      X0WAt (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS
        (fun s => phW (pcOf s) / 8 % 2 = 0) lbl s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F rS n0 k0
        c0 Code.Ti.x7L := by
  subst hn0
  have hI := instOkWS (a := a) (rS := rS) hp hlo hlab
  have hrc : RtCodeIn0 L.prog := hp ▸ wake_rtCodeIn0
  have hti : Flow.Ret0.ThreadInit.threadInitIn L.prog = true := hp ▸ wake_tiIn
  have hl := hlab
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startW_fact hΛ (f := f) (start_memW hf)
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (codeLabel lo wakeCells) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = L.lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hpn : pnA L.lab = L.pnA := L.lab_pn
  have hpin : pinA L.lab = L.pinA := L.lab_pin
  have hlk : lockA L.lab = L.lockA := L.lab_lock
  have hfr : freeNA L.lab = L.freeNA := L.lab_freeN
  have hnx : nextA L.lab = L.nextA := L.lab_next
  have h0 : ∃ j < 7, L.pinA + 0#64 = L.pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hfit := fitS_of_sub L hsub
  have hR1 := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR (by omega) (by decide) (by omega)
    (by omega)
  have ho1 := Flow.Ret0.Inst.out_callee hR (kc := -48 - 0) (lo' := -248) (hi' := 8) (by omega) (by decide)
    (by omega) (by omega) hout
  have ho2 := Flow.Ret0.Inst.out_callee hR1 (kc := -48 - 0) (lo' := -200) (hi' := 8)
    (by show (-248 : Int) ≤ _; omega) (by decide) (by show (-48 - 0 : Int) < 8; omega)
    (by show (-48 - 0 + 8 : Int) ≤ 8; omega) ho1
  have hSM := stackM_stable hfit hout
  have hst := hrc.start
  simp only [startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨-, cb0⟩, cbSi⟩, cbArgs⟩, cbSys⟩ := hst
  have hcl := hrc.call
  simp only [startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  have hcl2 := hrc.call2
  simp only [startCall2In, Bool.and_eq_true] at hcl2
  obtain ⟨cc2, -⟩ := hcl2
  have htl := hrc.tail
  simp only [startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨tFs, tSys⟩, tSw⟩, -⟩, -⟩, -⟩ := htl
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun g hg j => ?_⟩, X0W.toAt ⟨?_, fun g hg j => ?_, ?_, ?_, ?_⟩⟩
  · -- The frame's setup.
    exact blkW_pre (dead := fun _ => false) (ra := 0) hI cb0 (ofNat_zero' _) xStart0_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk "scc_rt_start" 0 xStart0 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false xStart0_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_phW (ph_of_factOk hl (hf (.ph "scc_rt_start" 0 13) (by simp [startPhTab]))) (by decide))
  · -- The handler's `lea`.
    have hs := step_of_factOk hl (hf (.step startE 0 7) (by simp [startPhTab]))
    exact nodeW_si_pre (si := siSig) (p := L.lab startE + Int64.ofNat 0) hI cbSi rfl
      (ofNat_zero' _).symm (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_phW (ph_of_factOk hl (hf (.ph startE 0 13) (by simp [startPhTab]))) (by decide)) hs.2
  · -- The arguments.
    exact blkW_pre (dead := fun _ => false) (ra := 0) hI cbArgs rfl xStartArgs_ok hR
      (by omega) (by omega) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 7 xStartArgs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false xStartArgs_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_phW (ph_of_factOk hl (hf (.ph startE 7 13) (by simp [startPhTab]))) (by decide))
  · -- `rt_sigaction`'s `syscall`.
    have hs := step_of_factOk hl (hf (.step startE 41 2) (by simp [startPhTab]))
    exact nodeW_syscall_pre (p := L.lab startE + Int64.ofNat 41) hI cbSys rfl
      (startE41 L.lab) (fun _ _ ⟨_, hJ, _⟩ => hJ ▸ hC0) hs.1
      (noTk_phW (ph_of_factOk hl (hf (.ph startE 41 13) (by simp [startPhTab]))) (by decide)) hs.2
      (fun _ _ ⟨_, _, he⟩ => by rw [he, Flow.Ret0.Inst.startS2_rax]; decide)
  · -- The call block.
    exact blkW_pre (dead := fun _ => false) (ra := 0) hI cc rfl startCall_ok hR
      (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk startE 43 Code.Start.startCall none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startCall_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_phW (ph_of_factOk hl (hf (.ph startE 43 13) (by simp [startPhTab]))) (by decide))
  · -- `scc_rt_alloc_tcb`.
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -184) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    exact tcbW_gen hI (fun _ => rfl) hrc.tcb hC0 hR' (by show (-184 : Int) ≤ -184; omega)
      (by show (8 : Int) ≤ 8; omega) ⟨g, 0#64, c0⟩ rfl hg (tcbPhW hΛ hlab hs)
      (by rw [hpn]; exact (L.words_mapped _ L.pn_mem).1)
      (by rw [hpin]; exact Spike.Lib.X64.PhRec.mapped_tcb h0)
      (fun m hm => by rw [hpn]; exact Spike.Lib.X64.PhRec.rtF_pn (hFr m hm))
      (fun m hm => by rw [hpin]; exact Spike.Lib.X64.PhRec.rtF_tcb (hFr m hm) h0) j
  · -- `.x0`'s block.
    exact blkW_pre (dead := fun _ => false) (ra := 0) hI cc2 (ofNat_zero' _) startCall2_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x0L 0 Code.Start.startCall2 none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startCall2_noRet k hk r).elim) (fun _ _ _ => rfl)
      (noTk_phW (ph_of_factOk hl (hf (.ph Code.Start.x0L 0 12) (by simp [startPhTab]))) (by decide))
  · -- `scc_rt_thread_init`, returning to `.x1`, its take to `.x7`.
    exact tiW_gen hI (fun _ => rfl) hti hC0 hR1 (by show (-248 : Int) ≤ -248; omega)
      (by show (8 : Int) ≤ 8; omega) ⟨g, pinA L.lab + 0#64 + 8#64, k0, c0⟩ rfl hg (tiPhW hΛ hlab)
      (fun _ ha => Spike.Lib.X64.PhRec.mapped_tcb (tcb_fld ha))
      (fun _ ha m hm => Spike.Lib.X64.PhRec.rtF_tcb (hFr m hm) (tcb_fld ha))
      (fun _ ha => tcb_not_ownW hs (tcb_fld ha))
      hsub (stackM_stable hfit ho1) (stackM_stable hfit ho2) hrc.take
      (takePhW hp hlo hΛ hlab hs.pn_next hs.pn_lock hs.pn_freeN hs.next_lock hs.next_freeN hs.lock_freeN
        hs.lock_a hs.next_a)
      (by rw [hlk]; exact (L.words_mapped _ L.lock_mem).1)
      (by rw [hfr]; exact (L.words_mapped _ L.freeN_mem).2.1)
      (by rw [hnx]; exact (L.words_mapped _ L.next_mem).1)
      (fun m hm => by rw [hlk]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr m hm))
      (fun m hm => by rw [hfr]; exact Spike.Lib.X64.PhRec.rtF_freeN (hFr m hm))
      (fun m hm => by rw [hnx]; exact Spike.Lib.X64.PhRec.rtF_next (hFr m hm))
      hrS hro j
  · -- `.x1`'s block.
    exact blkW_post (dead := fun _ => false) (ra := 0) hI tFs (ofNat_zero' _) startFs_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x1L 0 Code.Start.startFs none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startFs_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM
  · -- `arch_prctl`'s `syscall`.
    have hs := step_of_factOk hl (hf (.step Code.Start.x1L 18 2) (by simp [startPhTab]))
    exact nodeW_syscall_post (p := L.lab x1L + Int64.ofNat 18) hI tSys rfl rfl
      (fun _ _ hJ => hJ.1 ▸ hC0) hs.1 hs.2 hsub (fun _ _ hJ => by rw [hJ.2.1]; decide)
  · -- The block before the switch.
    exact blkW_post (dead := fun _ => false) (ra := 0) hI tSw rfl startSw_ok
      hR (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ hC0)
      (blkPh_of_factOk hl hr hn (hf (.blk Code.Start.x1L 20 Code.Start.startSw none none) (by simp [startPhTab])))
      (fun _ _ _ k hk r => (noRet_false startSw_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hSM

/-- **`scc_rt_start`'s states are inside `SFacts`** (`StartEW`, from
`_start` to `call scc_rt_main`, the return point inside
`scc_rt_thread_init` `.x7`) at `phW` with `ownW` (`startEW_sfacts`):
`_start`'s nodes (`entryW_wake`), the start up to the switch (`startSpW`)
in the callee region, and the switch (`swEW_gen`, `swPhW`). -/
theorem startEW_wake (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) (hs : WSep L a)
    (hro : L.Λ.rodata.Disjoint L.Λ.stackPool)
    {c0 : Ctl} {R : Region} {F : MachineData → Prop} {n0 k0 : BitVec 64} {D : Int}
    (hC0 : CFacts L.Λ lbl c0) (hR : R.OK) (hlo' : R.lo ≤ -304)
    (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → rtF L m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (h8 : (stacksA L.lab + k0 + 16384#64).toNat % 8 = 0)
    (hok : (swR (stacksA L.lab + k0 + 16384#64) (-D) 0).OK) (hL : 8 ≤ D) (hL8 : D % 8 = 0) :
    StartEW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS
        (fun s => phW (pcOf s) / 8 % 2 = 0) lbl s c) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F rS n0 k0
      c0 D Spike.Lib.X64.Rt.Code.Ti.x7L := by
  have hI := instOkWS (a := a) (rS := rS) hp hlo hlab
  have hR' := Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR (by omega) (by decide) (by omega)
    (by omega)
  have hout' := Spike.Lib.X64.Flow.Ret0.Inst.out_callee hR (kc := -8) (lo' := -296) (hi' := 8) (by omega)
    (by decide) (by omega) (by omega) hout
  refine ⟨entryW_wake hp hlo hΛ hlab hR (by omega) hhi hC0, fun F' _ _ hF' => ?_⟩
  have hsp := startSpW hp hlo hΛ hlab hs hro hC0 hR' (by show (-296 : Int) ≤ -296; omega)
    (by show (8 : Int) ≤ 8; omega) (fun m hm => hFr m (hF' m hm)) hn0 hrS hsub hout'
  refine ⟨hsp.1, hsp.2, ?_⟩
  subst hn0
  rw [hI.labOk]
  exact Spike.Lib.LowerX64.swEW_gen hI (hp ▸ wake_rtCodeIn0 : Spike.Lib.X64.Rt.RtCodeIn0 L.prog).tail hC0
    (swPhW hΛ hlab) h8 hok hL hL8 hsub (Spike.Lib.X64.Rt.fitS_of_sub L hsub)

end Start

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.instOkWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.instOkWS

/-- info: 'Spike.Lib.X64.WakePh.entryW_wake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.entryW_wake

/-- info: 'Spike.Lib.X64.WakePh.startSpW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.startSpW

/-- info: 'Spike.Lib.X64.WakePh.startEW_wake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.startEW_wake
