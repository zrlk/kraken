/-
**wake.w's heap abort path keeps both abort phases** (`Wf`'s `AbSt`/`AcSt`,
x86-64; the twin of `Spike/Lib/A64WakeWfHPA.lean`): every obligation of
`Abort.Disp.HPathW` (the dispatcher at the heap code `2` with the pushed
return address `ra`, then `scc_rt_abort_heap`) at
`AbSt μ (WriteAb.Ab lab) ∧ AcSt μ Cl (ThreadsAb.Ac lab pfxM)`, for an
executable with `InstOk`, its cells holding the runtime's abort code
(`abortIn`) and passing the path's phase check (`abortPhHeapOk`), its labels
wake's code labels where they resolve (`hlab`), `ra` not the threads
abort's return address (`hra`).

The dispatcher's prologue and first tests are at pcs of both phases: the
code `2` (in `%rdi`, then at `-8(%rbp)`) keeps the write abort out, the
pushed `ra` (`slot 8`) the threads abort (`blkW_dispI`, `hX_of`). Every
other block and instruction of the path reaches neither phase's pcs; the
exit call resumes in no state.

- `chH_*`: the phase checks at wake's code labels; `rH_*`: where each
  dispatcher target reads the pushed word (`rChkW`).
- `hpathW_ph`, `hra_alloc`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- offsets are bytes (`j1` at `.entry + 16`; the stub's `leaq` at
  `entry + 0`, its block at `+ 7`, the `syscall` at `+ 34`, the last block
  at `+ 36`); the labels are `wakeCells`' (`codeLabel`, no numbering);
- the stub's `leaq` is one instruction (A64's `adrp`/`add`, `chH_n1b`), and
  the `write` call is a `syscall` (`chH_sys`, `nodeW_sysI`; A64's `svc`);
- the return address is the pushed word, so `hX` of each dispatcher block
  comes from `rChkW` (`rH_*`, no A64 counterpart) and the run's offsets
  (`d0_sp1`, `d0_bp`, `tj_keep`), with `slot 8` kept (`d0_ra`, `tj_ra`;
  A64's `x30`, `d0_x30'`/`tj_x30`);
- the region is `[-24, 16)` (`R.Off (-8)`, `R.Off 8`; A64's `[-48, 0)`,
  `R.Off (-32)`), no alignment premise;
- `hra_alloc`'s return address is past `scc_rt_alloc`'s `call scc_rt_abort`
  at `.Lscc_rt_alloc.full + 12` (A64's `bl` at `+ 8`).
-/
import Spike.Lib.X64WakeWfRa
import Spike.Lib.X64WakeStartWfL

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.StubW (abortPhHeapOk phOne)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.Flow (ofNat_zero')
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)

/-! ## The checks at wake's code labels -/

theorem chH_d0 : dChkW pfxM "scc_rt_abort" 0 [0, 1, 2] [3] Abort.Disp.d0 = true := by
  unfold dChkW; decide +kernel
theorem chH_t1 : dChkW pfxM ".Lscc_rt_abort.entry" 0 [] [0, 1, 2, 3] Abort.Disp.t1 = true := by
  unfold dChkW; decide +kernel
theorem chH_j1 : dChkW pfxM ".Lscc_rt_abort.entry" 16 [] [0] Abort.Disp.j1 = true := by
  unfold dChkW; decide +kernel
theorem chH_t2 : dChkW pfxM ".Lscc_rt_abort.next1" 0 [] [0, 1, 2, 3] Abort.Disp.t2 = true := by
  unfold dChkW; decide +kernel
theorem rH_d0 : rChkW "scc_rt_abort" 0 [] [0] [1, 2, 3] Abort.Disp.d0 = true := by
  unfold rChkW; decide +kernel
theorem rH_t1 : rChkW ".Lscc_rt_abort.entry" 0 [] [] [0, 1, 2, 3] Abort.Disp.t1 = true := by
  unfold rChkW; decide +kernel
theorem rH_j1 : rChkW ".Lscc_rt_abort.entry" 16 [] [] [0] Abort.Disp.j1 = true := by
  unfold rChkW; decide +kernel
theorem rH_t2 : rChkW ".Lscc_rt_abort.next1" 0 [] [] [0, 1, 2, 3] Abort.Disp.t2 = true := by
  unfold rChkW; decide +kernel
theorem chH_g2 :
    phOffW pfxM ".Lscc_rt_abort.is2" 0 ".Lscc_rt_abort.is2" Abort.Disp.g2 = true := by
  unfold phOffW; decide +kernel
theorem chH_x0 : phOffW pfxM Abort.heap.fn 0 Abort.heap.fn Abort.x0 = true := by
  unfold phOffW; decide +kernel
theorem chH_n1 : siOffW pfxM Abort.heap.entry 0 7 = true := by
  unfold siOffW; decide +kernel
theorem chH_x1 : phOffW pfxM Abort.heap.entry 7 Abort.heap.entry Abort.x1Heap = true := by
  unfold phOffW; decide +kernel
theorem chH_sys : siOffW pfxM Abort.heap.entry 34 2 = true := by
  unfold siOffW; decide +kernel
theorem chH_x2 : phOffW pfxM Abort.heap.entry 36 Abort.heap.entry Abort.x2 = true := by
  unfold phOffW; decide +kernel

/-! ## The path -/

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region}
  {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

set_option maxHeartbeats 800000 in
/-- **The heap abort path's nodes keep both abort phases.** -/
theorem hpathW_ph (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hphs : abortPhHeapOk okPc ph lab = true)
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some a → lab l = Int64.ofNat a)
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.heap.exit).toBitVec.toNat ≠ a)
    (hra : ra ≠ ThreadsAb.raT lab pfxM) :
    Abort.Disp.HPathW (fun s _ => AbSt μ (WriteAb.Ab lab) s ∧
      AcSt μ Cl (ThreadsAb.Ac lab pfxM) s) (fun _ _ => False) exe endPc R F c0 ra := by
  have hl := hI.labOk
  subst hl
  have hsd := hab
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  have hst := hsd.1.1.1.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hx0, hn1, hx1, hsysIn, hx2, hx, -, -⟩ := hst
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, px0, o1, -, px1, o34, -, px2, -⟩ := hphs
  have hoff : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  have hoff8 : R.Off 8 := ⟨by decide, by omega, by omega⟩
  -- the tests' data: the code `2` at `-8(%rbp)`, `slot 8 = ra`
  have hTt : ∀ {blk : List (Directive × Nat)}, (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) →
      ∀ (pc : Int64) (σ : Spike.Lib.X64.AS), σ.slot (-8) = 2#64 → ∀ k, k < blk.length →
      (Spike.Lib.X64.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).so.get .rbp = some 0 ∧
        (Spike.Lib.X64.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).σ.slot (-8) ≠ 4#64 := fun hb pc σ h2 k hk => by
    obtain ⟨h1, h3⟩ := Spike.Lib.LowerX64.tj_keep _ hb pc σ (j := k + 1) (by omega)
    refine ⟨h1, fun h => ?_⟩
    rw [h3, h2] at h
    exact absurd h (by decide)
  have hXt : ∀ {blk : List (Directive × Nat)} {pc : Int64} {S P B : List Nat},
      (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) → S = [] → P = [] →
      rChk (_root_.Executable.labels exe).label pc S P B blk = true →
      ∀ σ c, (fun σ c => c = c0 ∧ σ.slot (-8) = 2#64 ∧ σ.slot 8 = ra) σ c →
      ∀ k (hk : k < blk.length) a, Spike.Lib.X64.classify blk[k].1 = some a → ∀ s' : State,
      s'.st.2 ∈ aiTgts (_root_.Executable.labels exe).label
        (pc + Int64.ofNat (Spike.Lib.X64.cellOff blk k) + Int64.ofNat blk[k].2) 0 a →
      Spike.Lib.X64.Abs R
        (Spike.Lib.X64.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨pc, Abort.Disp.oD, σ⟩).so
        s'.st.1
        (Spike.Lib.X64.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨pc, Abort.Disp.oD, σ⟩).σ →
      ¬ ThreadsAb.RaW (_root_.Executable.labels exe).label s'
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfxM) := by
    intro blk pc S P B hb hS hP h
    subst hS hP
    exact hX_of (n := ⟨pc, Abort.Disp.oD, fun σ c => c = c0 ∧ σ.slot (-8) = 2#64 ∧ σ.slot 8 = ra⟩) h hoff8
      (fun _ _ _ _ _ h => by simp at h) (fun _ _ _ _ _ h => by simp at h)
      (fun σ _ _ k hk _ => (Spike.Lib.LowerX64.tj_keep _ hb pc σ (j := k + 1) (by omega)).1)
      (fun σ c hJ k hk => by rw [tj_ra _ hb pc σ (by omega), hJ.2.2]; exact hra)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hr := rChkW_sound hlab rH_d0
    rw [ofNat_zero'] at hr
    refine blkW_dispI hI hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR (by omega) (by omega) hoff pd0 (by decide)
      (dChkW_sound hlab chH_d0) (fun σ c hJ k hk hkE => ?_) (fun σ c hJ k hk hkT => ?_)
      (hX_of hr hoff8 (fun _ _ _ _ _ h => by simp at h) (fun σ _ _ k _ hk => ?_) (fun σ _ _ k _ hk => ?_)
        (fun σ c hJ k hk => ?_))
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      have hk3 : k + 1 < Abort.Disp.d0.length := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkE
        have : Abort.Disp.d0.length = 4 := by decide
        omega
      rw [Spike.Lib.X64.StubW.d0_rdi _ σ hk3, hJ.2.1]
      decide
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      obtain rfl : k = 3 := by simpa using hkT
      obtain ⟨hbp, hsl⟩ := Spike.Lib.LowerX64.d0_end (_root_.Executable.labels exe).label
        ((_root_.Executable.labels exe).label "scc_rt_abort") σ
      refine ⟨hbp, ?_⟩
      rw [hsl, hJ.2.1]
      decide
    · obtain rfl : k = 0 := by simpa using hk
      exact d0_sp1 _ _ σ
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      exact d0_bp _ _ σ (by omega) (by simp [Abort.Disp.d0]; omega)
    · dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
      rw [d0_ra _ _ σ (by omega), hJ.2.2]
      exact hra
  · refine blkW_dispI hI ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR (by omega) (by omega) hoff pt1 (by decide)
      (dChkW_sound hlab chH_t1) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (hXt (.inl rfl) rfl rfl (by have hr := rChkW_sound hlab rH_t1; rwa [ofNat_zero'] at hr))
    dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
    exact hTt (.inl rfl) _ σ hJ.2.1 k hk
  · refine blkW_dispI hI hj1 rfl Abort.Disp.j1_ok hR (by omega) (by omega) hoff pj1 (by decide)
      (dChkW_sound hlab chH_j1) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (hXt (.inr (.inr rfl)) rfl rfl (rChkW_sound hlab rH_j1))
    dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
    exact hTt (.inr (.inr rfl)) _ σ hJ.2.1 k hk
  · refine blkW_dispI hI ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR (by omega) (by omega) hoff pt2 (by decide)
      (dChkW_sound hlab chH_t2) (fun _ _ _ _ _ h => by simp at h) (fun σ c hJ k hk _ => ?_)
      (hXt (.inr (.inl rfl)) rfl rfl (by have hr := rChkW_sound hlab rH_t2; rwa [ofNat_zero'] at hr))
    dsimp only [Abort.Disp.DN.nd2R] at hJ ⊢
    exact hTt (.inr (.inl rfl)) _ σ hJ.2.1 k hk
  · exact blkW_phI hI hg2 (ofNat_zero' _) Abort.Disp.g2_ok hR (by omega) (by omega) pg2 (by decide)
      (phOffW_sound hlab chH_g2)
  · exact blkW_phI hI hx0 (ofNat_zero' _) Abort.x0_ok hR (by omega) (by omega) px0 (by decide)
      (phOffW_sound hlab chH_x0)
  · exact nodeW_siI hI hn1 (ofNat_zero' _) o1 (siOffW_sound hlab chH_n1)
  · exact blkW_phI hI hx1 rfl Abort.x1Heap_ok hR (by omega) (by omega) px1 (by decide)
      (phOffW_sound hlab chH_x1)
  · exact nodeW_sysI hI hsysIn rfl o34 (siOffW_sound hlab chH_sys)
  · exact blkW_phI hI hx2 rfl Abort.x2_ok hR (by omega) (by omega) px2 (by decide)
      (phOffW_sound hlab chH_x2)
  · exact nodeW_exitI hI hx (ofNat_zero' _) rfl htk fun _ _ h => h.2.1

/-- **`hpathW_ph`'s `hra` at wake's heap abort entry**: the return address
past the full branch of `scc_rt_alloc` is not the threads abort's. -/
theorem hra_alloc
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some a → lab l = Int64.ofNat a) :
    (lab ".Lscc_rt_alloc.full" + 12).toBitVec ≠ ThreadsAb.raT lab pfxM := by
  have h1 : lab ".Lscc_rt_alloc.full" = Int64.ofNat 4198751 := hlab _ _ (by decide +kernel)
  have h2 : lab (pfxM ++ ".spawnfail5") = Int64.ofNat 4203510 := hlab _ _ (by decide +kernel)
  simp only [ThreadsAb.raT, h1, h2]
  decide

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.chH_d0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.chH_d0

/-- info: 'Spike.Lib.X64.WakeWf.hpathW_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.hpathW_ph
