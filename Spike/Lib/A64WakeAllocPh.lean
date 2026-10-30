/-
**`scc_rt_alloc` keeps both abort phases in wake.w** (`Wf`'s `AbSt`/`AcSt`,
AArch64): `allocAbAcW`, every node of `AllocW` at `AbSt μ (WriteAb.Ab lab) ∧
AcSt μ Cl (ThreadsAb.Ac lab pfxM)`, none moved, for an executable with
`InstOk`, its program holding the allocator's code (`allocIn`) and passing
its phase check (`allocPhOk`), its labels wake's code labels where they
resolve (`hlab`), for a call returning to `wc_main`'s `.sp0` (`hra`).

Every block's and single instruction's targets are off both phases' pcs
(`blkW_phI`, `nodeW_siI`, `nodeW_phSt`; the `ret`'s is `.sp0`). The heap
abort's `bl scc_rt_abort` (`.4_full`) enters the dispatcher's prologue with
`x0 = 2` (out of the write abort) and `x30` past itself (not `raT`,
`hra_alloc`, out of the threads abort); its target is off both phases' other
pcs (`dChk`, `chA_full`). Each check is decided at wake's code labels.
-/
import Spike.Lib.A64WakeWfHPA
import Spike.Lib.A64WakeWfW
import Spike.Lib.A64AllocGS

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.LowerA64 (labC nvPcs arun_succ_eq)
open Spike.Lib.A64.Flow (ofNat4_zero)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.AllocG (allocPhOk allocPhOk_spec allocIn_spec phOne_spec blkPh_ret hdr_addrS)
open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)

/-! ## The checks at wake's code labels -/

local macro "ph_dec" : tactic => `(tactic| (simp only [phOffW, ← codeT_eq]; decide +kernel))
local macro "si_dec" : tactic => `(tactic| (simp only [siOffW, ← codeT_eq]; decide +kernel))

theorem chA_b0 : phOffW pfxM "scc_rt_alloc" 0 "scc_rt_alloc" b0 = true := by ph_dec
theorem chA_b1 : phOffW pfxM ".L2_scc_rt_alloc.0_entry" 0 ".L2_scc_rt_alloc.0_entry" b1 = true := by ph_dec
theorem chA_b2 : phOffW pfxM ".L2_scc_rt_alloc.0_entry" 4 ".L2_scc_rt_alloc.0_entry" b2 = true := by ph_dec
theorem chA_c0 : siOffW pfxM ".L2_scc_rt_alloc.1_cnt" 0 = true := by si_dec
theorem chA_c1 : siOffW pfxM ".L2_scc_rt_alloc.1_cnt" 1 = true := by si_dec
theorem chA_b3 : phOffW pfxM ".L2_scc_rt_alloc.1_cnt" 2 ".L2_scc_rt_alloc.1_cnt" b3 = true := by ph_dec
theorem chA_c5 : siOffW pfxM ".L2_scc_rt_alloc.1_cnt" 5 = true := by si_dec
theorem chA_b4 : phOffW pfxM ".L2_scc_rt_alloc.1_cnt" 6 ".L2_scc_rt_alloc.1_cnt" b4 = true := by ph_dec
theorem chA_b5 : phOffW pfxM ".L2_scc_rt_alloc.1_cnt" 15 ".L2_scc_rt_alloc.1_cnt" b5 = true := by ph_dec
theorem chA_b6 : phOffW pfxM ".L2_scc_rt_alloc.2_slow" 0 ".L2_scc_rt_alloc.2_slow" b6 = true := by ph_dec
theorem chA_b7 : phOffW pfxM ".L2_scc_rt_alloc.2_slow" 4 ".L2_scc_rt_alloc.2_slow" b7 = true := by ph_dec
theorem chA_f0 : siOffW pfxM ".L2_scc_rt_alloc.4_full" 0 = true := by si_dec
theorem chA_full : dChkW pfxM ".L2_scc_rt_alloc.4_full" 0 [1] [] b9 = true := by
  simp only [dChkW, labC, ← codeT_eq]; decide +kernel
theorem chA_b11 : phOffW pfxM ".L2_scc_rt_alloc.5_ok" 0 ".L2_scc_rt_alloc.5_ok" b11 = true := by ph_dec
theorem chA_o8 : siOffW pfxM ".L2_scc_rt_alloc.5_ok" 8 = true := by si_dec
theorem chA_o9 : siOffW pfxM ".L2_scc_rt_alloc.5_ok" 9 = true := by si_dec
theorem chA_b12 : phOffW pfxM ".L2_scc_rt_alloc.5_ok" 10 ".L2_scc_rt_alloc.5_ok" b12 = true := by ph_dec
theorem chA_o41 : siOffW pfxM ".L2_scc_rt_alloc.5_ok" 41 = true := by si_dec
theorem chA_b13 : phOffW pfxM ".L2_scc_rt_alloc.5_ok" 42 ".L2_scc_rt_alloc.5_ok" b13 = true := by ph_dec
theorem chA_ret : phOffW pfxM ".L2_scc_rt_alloc.5_ok" 54 ".L21_wc_main.sp0" [iRet.toDir] = true := by ph_dec

/-! ## The heap abort's call -/

section Full

variable {μ : Marks} {Cl : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

set_option maxHeartbeats 800000 in
/-- **`.4_full`'s `movz x0, #2; bl scc_rt_abort` keeps both phases**: its
pcs off the marks' sites (`hpc`), the `movz`'s next pc off both phases'
(`chA_f0`), the call's target off both phases' pcs but the dispatcher's
prologue (`chA_full`), entered at `x0 = 2` and `x30` past the call
(`hra_alloc`). -/
theorem blkW_fullPh {n : ND}
    (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l = some x →
      (_root_.Executable.labels exe).label l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc b9)
    (hnp : n.pc = (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.4_full")
    (hno : n.o = Spike.Lib.A64.Alloc.oI)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hpc : ∀ j < b9.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfxM) s)
      (fun _ _ => False) exe endPc R F n b9 := by
  have hok : Spike.Lib.A64.Flow.okBlk (-160) 0 n.o b9 = true := by rw [hno]; exact b9_ok
  have hsi := siOffW_sound (lab := (_root_.Executable.labels exe).label) hlab chA_f0
  simp only [siOff, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hsi
  have hd := dChkW_sound (lab := (_root_.Executable.labels exe).label) hlab chA_full
  rw [ofNat4_zero, ← hnp] at hd
  have hrun : ∀ σ, Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b9.take (1 + 1))
      ⟨n.pc, n.o, σ⟩ = Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label b9
      ⟨n.pc, Spike.Lib.A64.Alloc.oI, σ⟩ := fun σ => by rw [hno]; rfl
  have key : ∀ σ c, n.J σ c → ∀ k (hk : k < b9.length) a, Spike.Lib.A64.Flow.classify b9[k] = some a →
      ∀ s' : State, s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b9.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.A64.Flow.Abs R
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b9.take (k + 1)) ⟨n.pc, n.o, σ⟩).so s'.st.1
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b9.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label s' ∧
        ¬ Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfxM s' := by
    intro σ c hJ k hk a ha s' hpc' hA'
    have hc := List.all_eq_true.mp hd k (List.mem_range.mpr hk)
    simp only [List.getElem?_eq_getElem hk, ha] at hc
    have ht := List.all_eq_true.mp hc _ (aiTgt_mem (lab := (_root_.Executable.labels exe).label)
      (fall := n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) (ra := 0)
      (σ := (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b9.take k) ⟨n.pc, n.o, σ⟩).σ) a
      fun r hr => (noRet_false (by decide : noRetBlk b9 = true) k hk r (hr ▸ ha)).elim)
    rw [← hpc'] at ht
    simp only [tOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_true_eq, decide_eq_false_iff_not] at ht
    obtain ⟨⟨⟨hnv, hE'⟩, hT'⟩, hsp⟩ := ht
    refine ⟨?_, fun hac => ?_⟩
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | h1 | ⟨h1, h4⟩ | ⟨h1, h4⟩ | h1 | h1)
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
      · rcases hE' with hk' | hk'
        · obtain rfl : k = 1 := by simpa using hk'
          rw [hA'.regs, hrun, Spike.Lib.A64.Alloc.b9_run] at h4
          revert h4; dsimp only; decide
        · exact hk' h1
      · rcases hT' with hk' | hk'
        · simp at hk'
        · exact hk' h1
      · exact hnv (by simp [nvPcs, h1])
      · exact hnv (by simp [nvPcs, h1])
    · match k, hk with
      | 0, _ =>
        simp [b9, Spike.Lib.A64.Flow.classify] at ha
        obtain ⟨-, rfl⟩ := ha
        refine Spike.Lib.A64.ThreadsAb.not_ac_of_pc ?_ hac
        rw [hpc']
        dsimp only [Spike.Lib.A64.Flow.AI.tgt]
        rw [hnp]
        exact hsi.2
      | 1, _ =>
        have hx := Spike.Lib.A64.ThreadsAb.ac_x30 hac (by simpa [spPcs] using hsp)
        rw [hA'.regs, hrun, Spike.Lib.A64.Alloc.b9_run] at hx
        dsimp only at hx
        rw [Spike.Lib.A64.Alloc.b9_x30, hnp] at hx
        exact hra_alloc hlab hx
  refine BlkW.and (blkW_abSt hcode hok hR hal (by omega) (by omega) hpc ?_)
    (blkW_acStN hcode hok hR hal (by omega) (by omega) hpc ?_)
  · intro σ c hJ k hk a ha s' _ _ hpc' hA'
    obtain ⟨hso, hst⟩ := arun_succ_eq _ (am := ⟨n.pc, n.o, σ⟩) hok hk ha
    rw [hso, hst] at hA'
    exact (key σ c hJ k hk a ha s' hpc' hA').1
  · intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' hA'
    obtain ⟨hso, hst⟩ := arun_succ_eq _ (am := ⟨n.pc, n.o, σ⟩) hok hk ha
    rw [hso, hst] at hA'
    exact (key σ c hJ k hk a ha s' hpc' hA').2

end Full

/-! ## The allocator -/

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop}
  {ms : MemSide isaLSE2} {q : Call}

set_option hygiene false in
/-- A `ret`-free block of `scc_rt_alloc` off both phases' pcs. -/
local macro "pblk " hb:term:max ok:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact blkW_phI hI $hb (by pc_tac) $ok hR hal (by omega) (by omega) $hp (by decide)
    (phOffW_sound hlab $ch))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "psi " hb:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact nodeW_siI hI $hb (by pc_tac) (phOne_spec $hp).1 (siOffW_sound hlab $ch))

set_option maxHeartbeats 800000 in
/-- **`scc_rt_alloc`'s states keep both abort phases** in wake.w, none
moved: its code passing the phase check (`hph`), its labels wake's code
labels (`hlab`), for a call `q` at any allocation site (`hq`) returning to
`wc_main`'s `.sp0` (`hra`), in a region of the allocator's frame, the counter
and every header the code may store unmapped in private memory (`hmem`). -/
theorem allocAbAcW (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l = some x →
      lab l = Int64.ofNat x)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OKS ms lab) (hra : q.ra = (lab ".L21_wc_main.sp0").toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab lab) s ∧
      AcSt μ Cl (Spike.Lib.A64.ThreadsAb.Ac lab pfxM) s) (fun _ _ => False) exe endPc R F := by
  have hl := hI.labOk
  subst hl
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19⟩ :=
    allocPhOk_spec hph
  have htkOf : ∀ {n : ND} {p : Int64}, okPc p.toBitVec.toNat = true → p = n.pc → ∀ s c,
      At exe endPc R F n s c → ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a := by
    intro n p hok hp s c hA' a ha heq
    obtain ⟨-, -, -, hpc, -⟩ := hA'
    exact (hI.off s (by unfold pcOf; rw [hpc, ← hp]; exact hok)).1.noTake a ha (by unfold pcOf; rw [hpc]; exact heq)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · pblk h0 b0_ok p0 chA_b0
  · pblk h1 b1_ok p1 chA_b1
  · pblk h2 b2_ok p2 chA_b2
  · psi h3 p3 chA_c0
  · psi h4 p4 chA_c1
  · pblk h5 b3_ok p5 chA_b3
  · intro s c hA'
    have he : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5) =
        (N (_root_.Executable.labels exe).label ms q .rmw).pc := by pc_tac
    refine nodeW_phSt he (siOffW_sound hlab chA_c5) (htkOf (phOne_spec p6).1 he s c hA')
      (Spike.Lib.A64.WakeWf.ldop_step hI (op := .ADD) (kk := .acqRel) (rs := .X9) (rt := .X11) (b := .X10) h6 he
        fun σ c m hJ hF => ?_) s c hA'
    obtain ⟨-, h10, -⟩ := hJ
    have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
    rw [h10']
    exact hmem _ (.inl rfl) m hF
  · pblk h7 b4_ok p7 chA_b4
  · pblk h8 b5_ok p8 chA_b5
  · pblk h9 b6_ok p9 chA_b6
  · pblk h10 b7_ok p10 chA_b7
  · -- the heap abort's `movz x0, #2; bl scc_rt_abort`
    have he : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.4_full" + Int64.ofNat (4 * 0) =
        (N (_root_.Executable.labels exe).label ms q .full).pc := by pc_tac
    have hph11 := p11
    rw [he] at hph11
    exact blkW_fullPh hlab (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk h11 he) rfl rfl hR hal hlo hhi
      (hpcOf hI b9_ok hph11 (by decide))
  · pblk h12 b11_ok p12 chA_b11
  · psi h13 p13 chA_o8
  · psi h14 p14 chA_o9
  · pblk h15 b12_ok p15 chA_b12
  · intro s c hA'
    have he : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41) =
        (N (_root_.Executable.labels exe).label ms q .hdr).pc := by pc_tac
    refine nodeW_phSt he (siOffW_sound hlab chA_o41) (htkOf (phOne_spec p16).1 he s c hA')
      (Spike.Lib.A64.WakeWf.st_step hI (t := .X9) (b := .X10) (i := 0) h16 he fun σ c m hJ hF => ?_) s c hA'
    obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, h10⟩ := hJ
    exact hmem _ (.inr ⟨o.toNat, hle, hdr_addrS (hq m hF) hle hn28 h10⟩) m hF
  · pblk h17 b13_ok p17 chA_b13
  · have he : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 54) =
        (N (_root_.Executable.labels exe).label ms q .ret).pc := by pc_tac
    have hok : Spike.Lib.A64.Flow.okBlk (-160) 0 (N (_root_.Executable.labels exe).label ms q .ret).o
        [iRet.toDir] = true := by dsimp only [N]; decide
    refine Spike.Lib.LowerA64.BlkW.nodeW (blkW_phSt (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk h18 he) hok
      hR hal (by omega) (by omega) (fun j hj s h1 h2 h3 => ?_) he (phOffW_sound hlab chA_ret)
      (hret_of_run hok fun σ c hJ => ?_)) (List.cons_ne_nil _ _)
    · obtain rfl : j = 0 := by simpa using hj
      rw [Spike.Lib.A64.Flow.ofNat4_zero, ← he] at h3
      exact (hI.off s (by unfold pcOf; rw [h3]; exact p18)).1
    · obtain ⟨o, -, -, -, -, -, h30⟩ := hJ
      have hc : Spike.Lib.A64.Flow.classify iRet.toDir = some iRet := rfl
      simp only [Spike.Lib.A64.Flow.arun, List.foldl, Spike.Lib.A64.Flow.dstep, hc]
      simp [iRet, Spike.Lib.A64.Flow.AI.tgt, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base,
        Reg64s.getXReg, h30, hra]

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.blkW_fullPh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.blkW_fullPh

/-- info: 'Spike.Lib.A64.WakeWf.allocAbAcW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.allocAbAcW
