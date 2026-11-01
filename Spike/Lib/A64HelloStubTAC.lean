/-
**The threads abort path's obligations inside `SFactsAC`, generic in the
spawn's pcs**: `Spike/Lib/A64StubTAC.lean`'s
`stubTW_sfactsAC` at `W := SFactsAC … frs Dt (fun _ => False) Cl
(Hello.ThreadsAb.Ac lab pfx n cl off)` (`Spike/Lib/A64HelloThreadsAb.lean`),
wake's at `13 ".clone9" 48`, hello's (`AcH`) at `25 ".clone13" 112`. The
path (the dispatcher from its prologue and the threads stub to its exit
call) reads none of the spawn's pcs, so the proof is wake's with the phase's
introductions at the generic `Ac` (`ac_g5G`, `ac_stubG` here,
`HelloThreadsAcSt.ac_dispEA`, `ac_dispTA`).

- `ac_g5G`, `ac_stubG`: the jump to the stub's and the stub's states in
  `Ac`, from the abstract state.
- `stubTW_sfactsACG`: `Abort.Disp.StubTW` at the return address
  `ThreadsAb.raT lab pfx`, as wake's `stubTW_sfactsAC`.

wake's `sfactsAC_doneT`, `sfactsAC_svcT`, `blkW_threadsAC`,
`nodeW_si_threadsAC`, `seg_svcTW` and `stubTW_of_code` are generic in the
phase and reused.
-/
import Spike.Lib.A64HelloThreadsAcSt
import Spike.Lib.A64StubTAC

namespace Spike.Lib.A64.Hello.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi atSvc_of_cellAt atSvc_false_of_cellAt mem_certSuccs_svc)
open Spike.Lib.Consumer1 (allInv_true OneCellTy)
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerS (OwnS PlacedS)
open Spike.Lib.A64ConsumerA
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff stackOff_stable)
open Spike.Lib.A64.Rt (InstOk owned_off)
open Scc.Cert.Rt.A64 (blockAt Lays endOf)
open Scc.Cert.Rt.A64.Print (code_field add4 add0)
open Kraken.Promising.Lower.A64 (CellAt after)
open Spike.Lib.A64.StubW hiding ac_g5A ac_stubA stubTW_sfactsAC

/-! ## The stub's states in the phase -/

section Phase

variable {lab : Label → Int64} {pfx : String} {n : Nat} {cl : String} {off : BitVec 64}

/-- A state of the jump to the threads stub with the threads return address,
from the abstract state, is in `Ac`. -/
theorem ac_g5G {R : Spike.Lib.Region} {o : Flow.SO} {s : State} {σ : Flow.AS}
    (hmem : s.st.2 ∈ ThreadsAb.g5Pcs lab) (hA : Flow.Abs R o s.st.1 σ)
    (hr : σ.regs.X30.toBitVec = ThreadsAb.raT lab pfx) : ThreadsAb.Ac lab pfx n cl off s :=
  ThreadsAb.ac_g5 hmem (by rw [hA.regs]; exact hr)

/-- A state of the threads stub with the threads return address, from the
abstract state, is in `Ac`. -/
theorem ac_stubG {R : Spike.Lib.Region} {o : Flow.SO} {s : State} {σ : Flow.AS}
    (hmem : s.st.2 ∈ ThreadsAb.stubPcs lab) (hA : Flow.Abs R o s.st.1 σ)
    (hr : σ.regs.X30.toBitVec = ThreadsAb.raT lab pfx) : ThreadsAb.Ac lab pfx n cl off s :=
  ThreadsAb.ac_stub hmem (by rw [hA.regs]; exact hr)

end Phase

/-! ## `StubTW` inside `SFactsAC` (the phase check `abortPhThreadsOk`) -/

section Stub

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.A64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame}
  {al : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {R : Region} {F : MachineData → Prop}

open Spike.Lib.A64ConsumerA.ThreadsAcSt (memE5 memT5 memJ5 memG5 memB0T memN1T memB1T memB2T memSvcT memExT
  d0_x30 t_run5 g5_x30 b0_x30 b1T_x30 b2_x30)
open Spike.Lib.A64ConsumerA.HelloThreadsAcSt (ac_dispEA ac_dispTA)

/-- **The threads abort path's obligations inside `SFactsAC … frs Dt
(fun _ => False) Cl (ThreadsAb.Ac lab pfx n cl off)`** (`Abort.Disp.StubTW` at the
return address `ThreadsAb.raT lab pfx`), for a program with the abort code
(`hprog`), an instance's facts at the frames `frs` (`hI`) and the path's
phase check (`hphs`); as `stubWW_sfactsA`. Every `Cl` state is at a `clone`
(`hCl`). The exit call is the threads abort site: off the release and take
sites (`hrel`, `htk`), no other kind's (`hk`), no outside move (`hKex`), the
memory side's abort (`hms`). The write tail `Dt` holds at the stub's
`write` (`hwr`). -/
theorem stubTW_sfactsACG {kp : Nat} (hI : InstOk exe endPc prog lab μ (fun s => own s frs) Tk K okPc ph kp)
    {c0 : Ctl} {Dt : State → Prop} {pfx : String} {n : Nat} {cl : String} {off : BitVec 64}
    {Cl : State → Prop}
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hphs : abortPhThreadsOk okPc ph lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p own lbl F c0 frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.threads.exit).toBitVec.toNat = a → k = .threads)
    (hKex : ∀ s s', pcOf s = (lab Abort.threads.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.threads.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.NT lab Abort.threads c0 (ThreadsAb.raT lab pfx) .svc) s c → Dt s) :
    Abort.Disp.StubTW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
        (ThreadsAb.Ac lab pfx n cl off))
      K p al ms exe endPc R F c0 (ThreadsAb.raT lab pfx) := by
  have hlab := hI.labOk
  subst hlab
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hoff : R.Off (-32) := ⟨by decide, by omega, by omega⟩
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, hj4, -, ht5, -, hg5, -⟩ := hdi
  simp only [abortPhThreadsOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pj2, pt3, pj3, pt4, pj4, pt5, pg5, pb0, o1, q1, o1b, q1b, pb1, o7, q7, pb2, qx⟩ :=
    hphs
  have hown : ∀ (s : State) (o : SO) σ, Flow.Abs R o s.st.1 σ → F s.st.1 → Tk s → Owned Λ rS s :=
    fun s _ σ hA hD _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have he7 : (_root_.Executable.labels exe).label Abort.threads.entry + Int64.ofNat (4 * 7) =
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .svc).pc := by
    simp only [Abort.NT, Abort.pcSvc, add4, add0]
  have hsvcT : NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
      (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx n cl off)) K exe endPc R F
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .svc) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
    have hc0 : c = c0 := hJ.1
    subst hc0
    have hAc : ThreadsAb.Ac (_root_.Executable.labels exe).label pfx n cl off s :=
      ac_stubG (by rw [hpc]; exact memSvcT) hA hJ.2
    rw [← he7] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o7)
    exact ⟨sfactsAC_svcT hc (hc.place s hD) hP.1.noSite hP.1.noTake
      (Spike.Lib.A64.Rt.cellOf hI hsvcIn rfl hs hn hpc) (Spike.Lib.A64.Rt.next_same hI hpc q7) (hown s _ σ hA hD)
      (fun k a ha e => (hP.1.noAbort k a ha e).elim) (fun _ _ _ _ => hwr s c hAt) hAc (hCl s), hP.2⟩
  have hsex : NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
      (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx n cl off)) K exe endPc R F
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .ex) := by
    rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, ⟨hc0, hra⟩, h8, h0⟩
    change c = c0 at hc0
    subst hc0
    have hpcN : pcOf s = ((_root_.Executable.labels exe).label Abort.threads.exit).toBitVec.toNat := by
      unfold pcOf; rw [hpc]; rfl
    have hAc : ThreadsAb.Ac (_root_.Executable.labels exe).label pfx n cl off s :=
      ac_stubG (by rw [hpc]; exact memExT) hA hra
    have hd : Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
        some (.exitGroup σ.regs.X0.toNat) := by
      rw [← svcCall_exitGroup (by rw [h8]; rfl), svcCall, ← hA.regs]; rfl
    refine ⟨sfactsAC_svcT hc (hc.place s hD) (fun a ha => hpcN ▸ hrel a ha)
      (fun a ha => hpcN ▸ htk a ha) (Spike.Lib.A64.Rt.cellOf hI hx (add0 _) hs hn hpc)
      (Spike.Lib.A64.Rt.next_same hI hpc qx) (hown s _ σ hA hD)
      (fun k a ha e => ⟨hk k a ha (hpcN ▸ e), fun v hv => ?_⟩)
      (fun _ _ _ h => by rw [hd] at h; cases h) hAc (hCl s), fun s' => hKex s s' hpcN⟩
    rw [hd] at hv
    cases hv
    rw [h0]; rfl
  have hT1 : Abort.Disp.t1 = Abort.Disp.t1 ∨ Abort.Disp.t1 = Abort.Disp.t2 ∨ Abort.Disp.t1 = Abort.Disp.t3 ∨
    Abort.Disp.t1 = Abort.Disp.t4 ∨ Abort.Disp.t1 = Abort.Disp.t5 := .inl rfl
  have hT2 : Abort.Disp.t2 = Abort.Disp.t1 ∨ Abort.Disp.t2 = Abort.Disp.t2 ∨ Abort.Disp.t2 = Abort.Disp.t3 ∨
    Abort.Disp.t2 = Abort.Disp.t4 ∨ Abort.Disp.t2 = Abort.Disp.t5 := .inr (.inl rfl)
  have hT3 : Abort.Disp.t3 = Abort.Disp.t1 ∨ Abort.Disp.t3 = Abort.Disp.t2 ∨ Abort.Disp.t3 = Abort.Disp.t3 ∨
    Abort.Disp.t3 = Abort.Disp.t4 ∨ Abort.Disp.t3 = Abort.Disp.t5 := .inr (.inr (.inl rfl))
  have hT4 : Abort.Disp.t4 = Abort.Disp.t1 ∨ Abort.Disp.t4 = Abort.Disp.t2 ∨ Abort.Disp.t4 = Abort.Disp.t3 ∨
    Abort.Disp.t4 = Abort.Disp.t4 ∨ Abort.Disp.t4 = Abort.Disp.t5 := .inr (.inr (.inr (.inl rfl)))
  have hT5 : Abort.Disp.t5 = Abort.Disp.t1 ∨ Abort.Disp.t5 = Abort.Disp.t2 ∨ Abort.Disp.t5 = Abort.Disp.t3 ∨
    Abort.Disp.t5 = Abort.Disp.t4 ∨ Abort.Disp.t5 = Abort.Disp.t5 := .inr (.inr (.inr (.inr rfl)))
  have hj : ∀ {j : Nat}, j < Abort.Disp.j1.length → j < 1 := fun h => h
  exact stubTW_of_code hI.lays hI.endOk hprog hK hF
    (blkW_threadsAC hI hd0 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.d0_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pd0 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispEA (memE5 hk) hA ((congrArg (fun x => x.toBitVec.toNat) (d0_x0 _ _ hk)).trans hJ.2.1)
          ((congrArg (fun x => x.toBitVec) (d0_x30 _ _ hk)).trans hJ.2.2))
    (blkW_threadsAC hI ht1 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t1_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inl rfl) hT1 hk) hA (t_run5 hT1 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT1 _ _ hk).2.1).trans hJ.2.1)
        ((congrArg (fun x => x.toBitVec) (t_run5 hT1 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hj1 (by simp only [Abort.Disp.DN.nd5, add4, add0]) Abort.Disp.j1_ok hR hal (by omega) hhi
      hl hh hF hsub hfit hFO pj1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ac_dispTA (memJ5 (.inl rfl) (by decide)) hA rfl hoff hJ.2.1 hJ.2.2.2)
    (blkW_threadsAC hI ht2 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t2_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inr (.inl rfl)) hT2 hk) hA (t_run5 hT2 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT2 _ _ hk).2.1).trans hJ.2.1)
        ((congrArg (fun x => x.toBitVec) (t_run5 hT2 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hj2 (by simp only [Abort.Disp.DN.nd5, add4, add0]) Abort.Disp.j2_ok hR hal (by omega) hhi
      hl hh hF hsub hfit hFO pj2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ac_dispTA (memJ5 (.inr (.inl rfl)) (by decide)) hA rfl hoff hJ.2.1 hJ.2.2.2)
    (blkW_threadsAC hI ht3 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t3_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt3 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inr (.inr (.inl rfl))) hT3 hk) hA (t_run5 hT3 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT3 _ _ hk).2.1).trans hJ.2.1)
        ((congrArg (fun x => x.toBitVec) (t_run5 hT3 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hj3 (by simp only [Abort.Disp.DN.nd5, add4, add0]) Abort.Disp.j3_ok hR hal (by omega) hhi
      hl hh hF hsub hfit hFO pj3 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ac_dispTA (memJ5 (.inr (.inr (.inl rfl))) (by decide)) hA rfl hoff hJ.2.1 hJ.2.2.2)
    (blkW_threadsAC hI ht4 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t4_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt4 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispTA (memT5 (.inr (.inr (.inr (.inl rfl)))) hT4 hk) hA (t_run5 hT4 _ _ hk).1 hoff
          ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT4 _ _ hk).2.1).trans hJ.2.1)
          ((congrArg (fun x => x.toBitVec) (t_run5 hT4 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hj4 (by simp only [Abort.Disp.DN.nd5, add4, add0]) Abort.Disp.j4_ok hR hal (by omega) hhi
      hl hh hF hsub hfit hFO pj4 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ac_dispTA (memJ5 (.inr (.inr (.inr rfl))) (by decide)) hA rfl hoff hJ.2.1 hJ.2.2.2)
    (blkW_threadsAC hI ht5 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t5_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt5 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispTA (memT5 (.inr (.inr (.inr (.inr rfl)))) hT5 hk) hA (t_run5 hT5 _ _ hk).1 hoff
          ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT5 _ _ hk).2.1).trans hJ.2.1)
          ((congrArg (fun x => x.toBitVec) (t_run5 hT5 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hg5 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.g5_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pg5 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_g5G (memG5 hk) hA (g5_x30 _ _ hJ.2.1 hJ.2.2 hk))
    (blkW_threadsAC hI hb0 (by simp only [Abort.NT, add0]) Abort.b0_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb0 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_stubG (memB0T hk) hA ((congrArg (fun x => x.toBitVec) (b0_x30 _ _ hk)).trans hJ.2))
    (nodeW_si_threadsAC (si := .adrp .X9 Abort.threads.msg) hI hn1 rfl (by simp only [Abort.NT, add0]) o1 q1
      hR hR8 hl hh hsub hFO (fun _ _ h => h.1) hc hCl
      fun _ _ _ hJ hA h => ac_stubG (by rw [h, add0]; exact memN1T.1) hA hJ.2)
    (nodeW_si_threadsAC (si := .addLo12 .X9 .X9 Abort.threads.msg) hI hn1b rfl
      (by simp only [Abort.NT, add4, add0]) o1b q1b hR hR8 hl hh hsub hFO (fun _ _ h => h.1) hc hCl
      fun _ _ _ hJ hA h => ac_stubG (by rw [h, add4, add0]; exact memN1T.2) hA hJ.2)
    (blkW_threadsAC hI hb1 (by simp only [Abort.NT, add4, add0]) Abort.b1Threads_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_stubG (memB1T hk) hA ((congrArg (fun x => x.toBitVec) (b1T_x30 _ _ hk)).trans hJ.2))
    hsvcT
    (blkW_threadsAC hI hb2 (by simp only [Abort.NT, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_stubG (memB2T hk) hA ((congrArg (fun x => x.toBitVec) (b2_x30 _ _ hk)).trans hJ.2))
    hsex
    (fun s c ⟨hs, _, _, hpc, _⟩ => hms s hs hpc)

end Stub

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Hello.StubW.stubTW_sfactsACG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubTW_sfactsACG

end Spike.Lib.A64.Hello.StubW
