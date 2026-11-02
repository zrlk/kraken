/-
**The threads abort path's obligations inside `SFactsAC`, generic in the
spawn's pcs** (x86-64; the twin of `Spike/Lib/A64HelloStubTAC.lean`):
`Spike/Lib/X64StubTAC.lean`'s `stubTW_sfactsAC` at `W := SFactsAC … frs Dt
(fun _ => False) Cl (Hello.ThreadsAb.Ac lab pfx cl n st off)`
(`Spike/Lib/X64HelloThreadsAb.lean`), hello's (`AcH`) at
`".x25" 94 ".x26" (-120)`. The path (the dispatcher from its prologue and
the threads stub to its exit call) reads none of the spawn's pcs, so the
proof is wake's with the phase's introductions at the generic `Ac`
(`ac_g5G`, `ac_stubG` here, `HelloThreadsAcSt.ac_dispEA`, `ac_dispTA`).

- `ac_g5G`, `ac_stubG`: the jump to the stub's and the stub's states in
  `Ac`, from the abstract state.
- `stubTW_sfactsACG`: `Abort.Disp.StubTW` at the return address
  `ThreadsAb.raT lab pfx`, as wake's `stubTW_sfactsAC`.

wake's `sfactsAC_doneT`, `sfactsAC_svcT`, `blkW_threadsAC`,
`nodeW_si_threadsAC`, `seg_svcTW` and `stubTW_of_code` are generic in the
phase and reused.

## Differences from the AArch64 version

- The return address is the pushed word at the frame's `slot 8`, not `x30`:
  `ac_g5G`/`ac_stubG` take `R.Off 8`, the offsets' position
  (`ThreadsAcSt.RaPos`) and `σ.slot 8 = raT` (`raW_of_abs`), as
  `X64StubTAC.ac_g5A`/`ac_stubA`.
- `stubTW_sfactsACG` has `X64StubTAC.stubTW_sfactsAC`'s premises (no `hal`,
  `hR8`, the region `[-24, 16)`, the exit `NT … .sys`); its proof is that
  one's at the generic phase.
-/
import Spike.Lib.X64HelloThreadsAcSt
import Spike.Lib.X64StubTAC

namespace Spike.Lib.X64.Hello.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf abi atSyscall_of_cellAt atSyscall_false_of_cellAt mem_certSuccs_syscall
  certSuccs_archSetFs)
open Spike.Lib.Consumer1 (allInv_true OneCellTy)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerS (OwnS PlacedS)
open Spike.Lib.X64ConsumerA
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (StackOff stackOff_stable)
open Spike.Lib.X64.Rt (InstOk owned_off)
open Scc.Cert.Rt.X64 (blockAtB code_field Lays endOf)
open Kraken.Promising.Lower.X64 (op64)

open Spike.Lib.X64.StubW hiding ac_g5A ac_stubA stubTW_sfactsAC

/-! ## The stub's states in the phase -/

section Phase

variable {lab : Label → Int64} {pfx : String} {n : Nat} {cl : String} {st : String} {off : BitVec 64}

/-- A state of the jump to the threads stub with the threads return address
at `slot 8`, from the abstract state, is in `Ac`. -/
theorem ac_g5G {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS}
    (hmem : s.st.2 ∈ Spike.Lib.X64.ThreadsAb.g5Pcs lab) (hA : Abs R o s.st.1 σ) (hoff : R.Off 8)
    (hpos : ThreadsAcSt.RaPos lab s.st.2 o) (hr : σ.slot 8 = Spike.Lib.X64.ThreadsAb.raT lab pfx) :
    Hello.ThreadsAb.Ac lab pfx cl n st off s :=
  Hello.ThreadsAb.ac_g5 hmem (ThreadsAcSt.raW_of_abs hA hoff hpos hr)

/-- A state of the threads stub with the threads return address at
`slot 8`, from the abstract state, is in `Ac`. -/
theorem ac_stubG {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS}
    (hmem : s.st.2 ∈ Spike.Lib.X64.ThreadsAb.stubPcs lab) (hA : Abs R o s.st.1 σ) (hoff : R.Off 8)
    (hpos : ThreadsAcSt.RaPos lab s.st.2 o) (hr : σ.slot 8 = Spike.Lib.X64.ThreadsAb.raT lab pfx) :
    Hello.ThreadsAb.Ac lab pfx cl n st off s :=
  Hello.ThreadsAb.ac_stub hmem (ThreadsAcSt.raW_of_abs hA hoff hpos hr)

end Phase

/-! ## `StubTW` inside `SFactsAC` (the phase check `abortPhThreadsOk`) -/

section Stub

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame}
  {al : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {R : Region} {F : MachineData → Prop}

open Spike.Lib.X64ConsumerA.ThreadsAcSt hiding ac_dispEA ac_dispTA
open Spike.Lib.X64ConsumerA.HelloThreadsAcSt (ac_dispEA ac_dispTA)

set_option maxHeartbeats 800000 in
/-- **The threads abort path's obligations inside `SFactsAC … frs Dt
(fun _ => False) Cl (Hello.ThreadsAb.Ac lab pfx cl n st off)`**, generic
in the spawn's pcs (`Abort.Disp.StubTW` at the
return address `ThreadsAb.raT lab pfx`), for a program with the abort code
(`hprog`), an instance's facts at the frames `frs` (`hI`) and the path's
phase check (`hphs`); as `stubWW_sfactsA`. Every `Cl` state is at a `clone`
(`hCl`). The exit call is the threads abort site: off the release and take
sites (`hrel`, `htk`), no other kind's (`hk`), no outside move (`hKex`), the
memory side's abort (`hms`). The write tail `Dt` holds at the stub's
`write` (`hwr`). -/
theorem stubTW_sfactsACG {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {c0 : Ctl} {Dt : State → Prop} {pfx : String} {cl : String} {n : Nat} {st : String} {off : BitVec 64}
    {Cl : State → Prop}
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hphs : abortPhThreadsOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p own lbl F c0 frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.threads.exit).toBitVec.toNat = a → k = .threads)
    (hKex : ∀ s s', pcOf s = (lab Abort.threads.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.threads.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.NT lab Abort.threads c0 (ThreadsAb.raT lab pfx) .sys) s c → Dt s) :
    Abort.Disp.StubTW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
        (Hello.ThreadsAb.Ac lab pfx cl n st off))
      K p al ms exe endPc R F c0 (ThreadsAb.raT lab pfx) := by
  have hlab := hI.labOk
  subst hlab
  have hoff : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  have hoff8 : R.Off 8 := ⟨by decide, by omega, by omega⟩
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hb1, hsysIn, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, hj4, -, ht5, -, hg5, -⟩ := hdi
  simp only [abortPhThreadsOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pj2, pt3, pj3, pt4, pj4, pt5, pg5, pb0, o1, q1, pb1, o34, q34, pb2, qx⟩ := hphs
  have hown : ∀ (s : State) (o : SO) σ, Abs R o s.st.1 σ → F s.st.1 → Tk s → Owned Λ rS s :=
    fun s _ σ hA hD _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have he34 : (_root_.Executable.labels exe).label Abort.threads.entry + Int64.ofNat 34 =
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .sys).pc := rfl
  have hsysT : NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
      (Hello.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx cl n st off)) K exe endPc R F
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .sys) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
    have hc0 : c = c0 := hJ.1
    subst hc0
    have hAc : Hello.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx cl n st off s :=
      ac_stubG (by rw [hpc]; exact memSysT.1) hA hoff8 (.inr (.inr ⟨by rw [hpc]; exact memSysT.2, rfl⟩)) hJ.2
    rw [← he34] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o34)
    exact ⟨sfactsAC_svcT hc (hc.place s hD) hP.1.noSite hP.1.noTake
      (Spike.Lib.X64.Rt.cellOf hI hsysIn rfl hs hn hpc) (Spike.Lib.X64.Rt.next_same hI hpc q34)
      (hown s _ σ hA hD) (fun k a ha e => (hP.1.noAbort k a ha e).elim) (fun _ _ _ _ => hwr s c hAt) hAc (hCl s),
      hP.2⟩
  have hsex : NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
      (Hello.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx cl n st off)) K exe endPc R F
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .ex) := by
    rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, ⟨hc0, hra⟩, hax, hdi⟩
    change c = c0 at hc0
    subst hc0
    have hpcN : pcOf s = ((_root_.Executable.labels exe).label Abort.threads.exit).toBitVec.toNat := by
      unfold pcOf; rw [hpc]; rfl
    have hAc : Hello.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx cl n st off s :=
      ac_stubG (by rw [hpc]; exact memExT.1) hA hoff8 (.inr (.inr ⟨by rw [hpc]; exact memExT.2, rfl⟩)) hra
    have hx231 : σ.regs.rax.toNat = 231 := by
      simp only [Reg64s.get64] at hax
      rw [← UInt64.toNat_toBitVec, hax]; rfl
    have hd : Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
        some (.exitGroup σ.regs.rdi.toNat) := by
      rw [← syscallCall_exitGroup hx231, syscallCall, ← hA.regs]; rfl
    refine ⟨sfactsAC_svcT hc (hc.place s hD) (fun a ha => hpcN ▸ hrel a ha)
      (fun a ha => hpcN ▸ htk a ha) (Spike.Lib.X64.Rt.cellOf hI hx (ofNat_zero' _) hs hn hpc)
      (Spike.Lib.X64.Rt.next_same hI hpc qx) (hown s _ σ hA hD)
      (fun k a ha e => ⟨hk k a ha (hpcN ▸ e), fun v hv => ?_⟩)
      (fun _ _ _ h => by rw [hd] at h; cases h) hAc (hCl s), fun s' => hKex s s' hpcN⟩
    rw [hd] at hv
    cases hv
    simp only [Reg64s.get64] at hdi
    rw [← UInt64.toNat_toBitVec, hdi]; rfl
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
  have hj : ∀ {blk : List (Directive × Nat)} {j : Nat},
      (blk = Abort.Disp.j1 ∨ blk = Abort.Disp.j2 ∨ blk = Abort.Disp.j3 ∨ blk = Abort.Disp.j4) →
      j < blk.length → j = 0 := by
    intro blk j hb hk
    rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [Abort.Disp.j1, Abort.Disp.j2, Abort.Disp.j3, Abort.Disp.j4, List.length_zip, List.length_cons,
        List.length_nil] at hk <;> omega
  have hoD : Abort.Disp.oD.get .rbp = some 0 := by simp [SO.get, Spike.Lib.lk]
  have hoI : Abort.oI.get .rbp = some 0 := by simp [SO.get, Spike.Lib.lk]
  exact stubTW_of_code hI.lays hI.endOk hprog hK hF
    (blkW_threadsAC hI hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pd0 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispEA (memE5 hk) hA ((d0_run5 _ _ hk).1.trans hJ.2.1) hoff8
        (d0_run5 _ _ hk).2.2 ((d0_run5 _ _ hk).2.1.trans hJ.2.2))
    (blkW_threadsAC hI ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inl rfl) hT1 hk) hA (t_run5 hT1 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run5 hT1 _ _ hk).2).trans hJ.2.1) hoff8
        ((congrArg (fun f => f 8) (t_run5 hT1 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hj1 rfl Abort.Disp.j1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inl rfl) hk
        exact ac_dispTA (memJ5 (.inl rfl) (.inl rfl) hk) hA hoD hoff hJ.2.1 hoff8 hJ.2.2)
    (blkW_threadsAC hI ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inr (.inl rfl)) hT2 hk) hA (t_run5 hT2 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run5 hT2 _ _ hk).2).trans hJ.2.1) hoff8
        ((congrArg (fun f => f 8) (t_run5 hT2 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hj2 rfl Abort.Disp.j2_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inr (.inl rfl)) hk
        exact ac_dispTA (memJ5 (.inr (.inl rfl)) (.inr (.inl rfl)) hk) hA hoD hoff hJ.2.1 hoff8 hJ.2.2)
    (blkW_threadsAC hI ht3 (ofNat_zero' _) Abort.Disp.t3_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt3 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inr (.inr (.inl rfl))) hT3 hk) hA (t_run5 hT3 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run5 hT3 _ _ hk).2).trans hJ.2.1) hoff8
        ((congrArg (fun f => f 8) (t_run5 hT3 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hj3 rfl Abort.Disp.j3_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj3 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inr (.inr (.inl rfl))) hk
        exact ac_dispTA (memJ5 (.inr (.inr (.inl rfl))) (.inr (.inr (.inl rfl))) hk) hA hoD hoff hJ.2.1 hoff8
          hJ.2.2)
    (blkW_threadsAC hI ht4 (ofNat_zero' _) Abort.Disp.t4_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt4 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispTA (memT5 (.inr (.inr (.inr (.inl rfl)))) hT4 hk) hA (t_run5 hT4 _ _ hk).1 hoff
          ((congrArg (fun f => f (-8)) (t_run5 hT4 _ _ hk).2).trans hJ.2.1) hoff8
          ((congrArg (fun f => f 8) (t_run5 hT4 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hj4 rfl Abort.Disp.j4_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj4 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inr (.inr (.inr rfl))) hk
        exact ac_dispTA (memJ5 (.inr (.inr (.inr rfl))) (.inr (.inr (.inr rfl))) hk) hA hoD hoff hJ.2.1 hoff8
          hJ.2.2)
    (blkW_threadsAC hI ht5 (ofNat_zero' _) Abort.Disp.t5_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt5 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispTA (memT5 (.inr (.inr (.inr (.inr rfl)))) hT5 hk) hA (t_run5 hT5 _ _ hk).1 hoff
          ((congrArg (fun f => f (-8)) (t_run5 hT5 _ _ hk).2).trans hJ.2.1) hoff8
          ((congrArg (fun f => f 8) (t_run5 hT5 _ _ hk).2).trans hJ.2.2))
    (blkW_threadsAC hI hg5 (ofNat_zero' _) Abort.Disp.g5_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pg5 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_g5G (memG5 hk) hA hoff8 (g5_run _ _ hk).2 ((g5_run _ _ hk).1.trans hJ.2))
    (blkW_threadsAC hI hb0 (ofNat_zero' _) Abort.x0_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb0 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_stubG (memX0T hk) hA hoff8 (x0_run5 _ _ hk).2 ((x0_run5 _ _ hk).1.trans hJ.2))
    (nodeW_si_threadsAC (si := Abort.siMsg Abort.threads) hI hn1 rfl (ofNat_zero' _).symm o1 q1
      hR hR8 hl hh hsub hFO (fun _ _ h => h.1) hc hCl
      fun _ _ _ hJ hA h => ac_stubG (by rw [h, ofNat_zero']; exact memN1T.1) hA hoff8
        (.inr (.inr ⟨by rw [h, ofNat_zero']; exact memN1T.2, hoI⟩)) hJ.2)
    (blkW_threadsAC hI hb1 rfl Abort.x1Threads_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_stubG (memX1T hk).1 hA hoff8 (.inr (.inr ⟨(memX1T hk).2, (x1T_run _ _ hk).1⟩))
        ((x1T_run _ _ hk).2.trans hJ.2))
    hsysT
    (blkW_threadsAC hI hb2 rfl Abort.x2_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_stubG (memX2T hk).1 hA hoff8 (.inr (.inr ⟨(memX2T hk).2, (x2_run5 _ _ hk).1⟩))
        ((x2_run5 _ _ hk).2.trans hJ.2))
    hsex
    (fun s c ⟨hs, _, _, hpc, _⟩ => hms s hs hpc)

end Stub

end Spike.Lib.X64.Hello.StubW

/-- info: 'Spike.Lib.X64.Hello.StubW.ac_g5G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Hello.StubW.ac_g5G

/-- info: 'Spike.Lib.X64.Hello.StubW.ac_stubG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Hello.StubW.ac_stubG

/-- info: 'Spike.Lib.X64.Hello.StubW.stubTW_sfactsACG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Hello.StubW.stubTW_sfactsACG
