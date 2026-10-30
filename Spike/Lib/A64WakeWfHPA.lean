/-
**wake.w's heap abort path keeps both abort phases** (`Wf`'s `AbSt`/`AcSt`,
AArch64): `hpathW_ph`, every obligation of `Abort.Disp.HPathW` (the
dispatcher at the heap code `2` with a return address `ra`, then
`scc_rt_abort_heap`) at `AbSt μ (WriteAb.Ab lab) ∧ AcSt μ Cl
(ThreadsAb.Ac lab pfxM)`, for an executable with `InstOk`, its program
holding the runtime's abort code (`abortIn`) and passing the path's phase
check (`abortPhHeapOk`), its labels wake's code labels where they resolve
(`hlab`), the heap stub's exit call off the take site (`htk`), `ra` not the
threads abort's return address (`hra`).

The dispatcher's prologue and its tests against `1` and `2` reach pcs of
both phases: the code `2` (in `x0`, then at `[sp]`) keeps the write abort
out, `x30 = ra` the threads abort (`blkW_dispI`). Every other block and
instruction of the path reaches neither phase's pcs (`blkW_phI`,
`nodeW_siI`, `nodeW_svcI`); the exit call resumes in no state
(`nodeW_exitI`). Each check is decided at wake's code labels.
-/
import Spike.Lib.A64WakeWfHP

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.LowerA64 (labC)
open Spike.Lib.A64.StubW (abortPhHeapOk phOne)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)

/-! ## The checks at wake's code labels -/

theorem chH_d0 : dChkW pfxM "scc_rt_abort" 0 [0, 1, 2, 3] [4] Abort.Disp.d0 = true := by
  simp only [dChkW, labC, ← codeT_eq]; decide +kernel
theorem chH_t1 : dChkW pfxM ".L12_scc_rt_abort.0_entry" 0 [] [0, 1, 2, 3] Abort.Disp.t1 = true := by
  simp only [dChkW, labC, ← codeT_eq]; decide +kernel
theorem chH_j1 : dChkW pfxM ".L12_scc_rt_abort.0_entry" 4 [] [0] Abort.Disp.j1 = true := by
  simp only [dChkW, labC, ← codeT_eq]; decide +kernel
theorem chH_t2 : dChkW pfxM ".L12_scc_rt_abort.2_next1" 0 [] [0, 1, 2, 3] Abort.Disp.t2 = true := by
  simp only [dChkW, labC, ← codeT_eq]; decide +kernel
theorem chH_g2 :
    phOffW pfxM ".L12_scc_rt_abort.3_is2" 0 ".L12_scc_rt_abort.3_is2" Abort.Disp.g2 = true := by
  simp only [phOffW, ← codeT_eq]; decide +kernel
theorem chH_b0 : phOffW pfxM Abort.heap.fn 0 Abort.heap.fn Abort.b0 = true := by
  simp only [phOffW, ← codeT_eq]; decide +kernel
theorem chH_n1 : siOffW pfxM Abort.heap.entry 0 = true := by
  simp only [siOffW, ← codeT_eq]; decide +kernel
theorem chH_n1b : siOffW pfxM Abort.heap.entry 1 = true := by
  simp only [siOffW, ← codeT_eq]; decide +kernel
theorem chH_b1 : phOffW pfxM Abort.heap.entry 2 Abort.heap.entry Abort.b1Heap = true := by
  simp only [phOffW, ← codeT_eq]; decide +kernel
theorem chH_svc : siOffW pfxM Abort.heap.entry 7 = true := by
  simp only [siOffW, ← codeT_eq]; decide +kernel
theorem chH_b2 : phOffW pfxM Abort.heap.entry 8 Abort.heap.entry Abort.b2 = true := by
  simp only [phOffW, ← codeT_eq]; decide +kernel

/-! ## The path -/

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl} {ra : BitVec 64}

set_option maxHeartbeats 800000 in
/-- **The heap abort path's nodes keep both abort phases.** -/
theorem hpathW_ph (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhHeapOk okPc ph lab = true)
    (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l = some x →
      lab l = Int64.ofNat x)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.heap.exit).toBitVec.toNat ≠ a)
    (hra : ra ≠ ThreadsAb.raT lab pfxM) :
    Abort.Disp.HPathW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab lab) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac lab pfxM) s) (fun _ _ => False) exe endPc R F c0 ra := by
  have hl := hI.labOk
  subst hl
  have hsd := hab
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  have hst := hsd.1.1.1.1.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, hx, -, -⟩ := hst
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, pb0, o1, -, o1b, -, pb1, o7, -, pb2, -⟩ := hphs
  have hoff : R.Off (-32) := ⟨by decide, by omega, by omega⟩
  -- the tests' data: the code `2` at `[sp]`, `x30 = ra`
  have hTt : ∀ {blk : List Directive}, (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) →
      ∀ (pc : Int64) (σ : Spike.Lib.A64.Flow.AS), (σ.slot (-32)).toNat = 2 → ∀ k, k < blk.length →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).so.sp = -32 ∧
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).σ.slot (-32) ≠ 4#64 := fun hb pc σ h2 k hk => by
    obtain ⟨h1, h3⟩ := Spike.Lib.LowerA64.tj_keep _ hb pc σ (j := k + 1) (by omega)
    refine ⟨h1, fun h => ?_⟩
    rw [h3] at h
    rw [h] at h2
    exact absurd h2 (by decide)
  have hXt : ∀ {blk : List Directive}, (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) →
      ∀ (pc : Int64) (σ : Spike.Lib.A64.Flow.AS), σ.regs.X30.toBitVec = ra → ∀ k, k < blk.length →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
        ⟨pc, Abort.Disp.oD, σ⟩).σ.regs.X30.toBitVec ≠ ThreadsAb.raT (_root_.Executable.labels exe).label pfxM :=
    fun hb pc σ hr k hk => by rw [tj_x30 _ hb pc σ (by omega), hr]; exact hra
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkW_dispI hI hd0 (add0 _) Abort.Disp.d0_ok hR hal (by omega) (by omega) hoff pd0 (by decide)
      (dChkW_sound hlab chH_d0) (fun σ c hJ k hk hkE => ?_) (fun σ c hJ k hk hkT => ?_)
      (fun σ c hJ k hk => ?_)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      have hk4 : k + 1 < Abort.Disp.d0.length := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkE
        have : Abort.Disp.d0.length = 5 := by decide
        omega
      rw [Spike.Lib.A64.StubW.d0_x0 _ σ hk4]
      intro h
      have h2 := hJ.2.1
      rw [h] at h2
      exact absurd h2 (by decide)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      obtain rfl : k = 4 := by simpa using hkT
      obtain ⟨hsp, hsl⟩ := Spike.Lib.LowerA64.d0_end (_root_.Executable.labels exe).label
        ((_root_.Executable.labels exe).label "scc_rt_abort") σ
      refine ⟨hsp, fun h => ?_⟩
      have h' := congrArg BitVec.toNat (hsl.symm.trans h)
      rw [hJ.2.1] at h'
      exact absurd h' (by decide)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      rw [d0_x30' _ _ σ (by omega), hJ.2.2]
      exact hra
  · refine blkW_dispI hI ht1 (add0 _) Abort.Disp.t1_ok hR hal (by omega) (by omega) hoff pt1 (by decide)
      (dChkW_sound hlab chH_t1) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (fun σ c hJ k hk => ?_)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hTt (.inl rfl) _ σ hJ.2.1 k hk
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hXt (.inl rfl) _ σ hJ.2.2.2 k hk
  · refine blkW_dispI hI hj1 (by simp only [Abort.Disp.DN.nd2R, add4, add0]) Abort.Disp.j1_ok hR hal
      (by omega) (by omega) hoff pj1 (by decide) (dChkW_sound hlab chH_j1) (fun _ _ _ _ _ h => by simp at h)
      (fun σ c hJ k hk _ => ?_) (fun σ c hJ k hk => ?_)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hTt (.inr (.inr rfl)) _ σ hJ.2.1 k hk
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hXt (.inr (.inr rfl)) _ σ hJ.2.2.2 k hk
  · refine blkW_dispI hI ht2 (add0 _) Abort.Disp.t2_ok hR hal (by omega) (by omega) hoff pt2 (by decide)
      (dChkW_sound hlab chH_t2) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (fun σ c hJ k hk => ?_)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hTt (.inr (.inl rfl)) _ σ hJ.2.1 k hk
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      exact hXt (.inr (.inl rfl)) _ σ hJ.2.2.2 k hk
  · exact blkW_phI hI hg2 (add0 _) Abort.Disp.g2_ok hR hal (by omega) (by omega) pg2 (by decide)
      (phOffW_sound hlab chH_g2)
  · exact blkW_phI hI hb0 (add0 _) Abort.b0_ok hR hal (by omega) (by omega) pb0 (by decide)
      (phOffW_sound hlab chH_b0)
  · exact nodeW_siI hI hn1 (add0 _) o1 (siOffW_sound hlab chH_n1)
  · exact nodeW_siI hI hn1b (by simp only [Abort.NT, add4, add0]) o1b (siOffW_sound hlab chH_n1b)
  · exact blkW_phI hI hb1 (by simp only [Abort.NT, add4, add0]) Abort.b1Heap_ok hR hal (by omega) (by omega)
      pb1 (by decide) (phOffW_sound hlab chH_b1)
  · exact nodeW_svcI hI hsvcIn (by simp only [Abort.NT, Abort.pcSvc, add4, add0]) o7
      (siOffW_sound hlab chH_svc)
  · exact blkW_phI hI hb2 (by simp only [Abort.NT, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal (by omega)
      (by omega) pb2 (by decide) (phOffW_sound hlab chH_b2)
  · exact nodeW_exitI hI hx (add0 _) rfl htk fun _ _ h => h.2.1

/-- **`hpathW_ph`'s `hra` at wake's heap abort entry**: the return address
past the full branch of `scc_rt_alloc` is not the threads abort's. -/
theorem hra_alloc
    (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l = some x →
      lab l = Int64.ofNat x) :
    (lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec ≠ Spike.Lib.A64.ThreadsAb.raT lab pfxM := by
  have h1 : lab ".L2_scc_rt_alloc.4_full" = Int64.ofNat 2164480 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have h2 : lab (pfxM ++ ".1_spawnfail5") = Int64.ofNat 2169376 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  simp only [Spike.Lib.A64.ThreadsAb.raT, h1, h2]
  decide

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.chH_d0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.chH_d0

/-- info: 'Spike.Lib.A64.WakeWf.hpathW_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.hpathW_ph

/-- info: 'Spike.Lib.A64.WakeWf.hra_alloc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.hra_alloc
