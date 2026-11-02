/-
**The write abort's phase kept on hello.w's threads abort path** (AArch64; part 3;
the hello twin of `A64WakeRefAb`'s `tpathW_ab`): every obligation of `TPathW` at
`AbSt μ (WriteAb.Ab lab)`, none moved, for an executable with `InstOk`, its program holding the runtime's abort
code (`abortIn`) and passing the path's phase check (`abortPhThreadsOk`), its labels hello's code labels where they
resolve (`hlab`), the exit call off the take site (`htk`).

Wake's checks (`WakeWf.tOkA`, `dChkA`, `dChkA_congr`), the block lemma (`blkW_dispAbI`) and the tests' data
(`tj_keep5`, `t4_fall`) are label generic; only their instantiation at the code labels reads wake's program, so it
is restated at `SccCode.helloProg`.

- `dChkAH`, `dChkAH_sound`, `siAbH`, `siAbH_sound`: the checks, decided at hello's code labels.
- `chAH2_*`: the checks.
- `tpathW_abH`: the path.
-/
import Spike.Lib.A64WakeRefAb
import Spike.Lib.A64HelloWfPh

namespace Spike.Lib.A64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.WakeRefTP (TPathW)
open Spike.Lib.A64.Abort (NT)
open Spike.Lib.A64.Abort.Disp (DN)
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.LowerA64 (labC blkLabs)
open Spike.Lib.A64.AllocG (abLabs abPcs_congr)
open Spike.Lib.A64.StubW (abortPhThreadsOk phOne)
open Spike.Lib.A64.WakeWf (dChkA dChkA_congr blkW_dispAbI tj_keep5 t4_fall)

/-! ## The checks at hello's code labels -/

/-- **`dChkA` at hello's code labels**, every label it reads resolving, the block at `lab l + 4 k`. -/
def dChkAH (l : Label) (k : Nat) (E T D : List Nat) (blk : List Directive) : Bool :=
  (l :: blkLabs blk ++ abLabs).all (fun x => (codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) &&
    dChkA (labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg)
      (labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg l + Int64.ofNat (4 * k)) E T D blk

/-- **A single instruction's next pc off the write abort's pcs** at hello's code labels, the instruction at
`lab l + 4 k`. -/
def siAbH (l : Label) (k : Nat) : Bool :=
  (l :: abLabs).all (fun x => (codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) &&
    !(Spike.Lib.A64.WriteAb.abPcs (labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg)).contains
      (labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg l + Int64.ofNat (4 * k) + 4)

section Sound

variable {lab : Label → Int64}
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → lab l = Int64.ofNat x)
include hlab

/-- **`dChkAH` at any labels agreeing with the code labels.** -/
theorem dChkAH_sound {l : Label} {k : Nat} {E T D : List Nat} {blk : List Directive}
    (h : dChkAH l k E T D blk = true) : dChkA lab (lab l + Int64.ofNat (4 * k)) E T D blk = true := by
  simp only [dChkAH, Bool.and_eq_true] at h
  have hl := lab_labCH hlab h.1
  rw [dChkA_congr (fun x hx => hl x (by simp [hx])) (fun x hx => hl x (by simp [hx])), hl l (by simp)]
  exact h.2

/-- **`siAbH` at any labels agreeing with the code labels.** -/
theorem siAbH_sound {l : Label} {k : Nat} (h : siAbH l k = true) :
    lab l + Int64.ofNat (4 * k) + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab := by
  simp only [siAbH, Bool.and_eq_true] at h
  have hl := lab_labCH hlab h.1
  rw [abPcs_congr (fun x hx => hl x (by simp [hx])), hl l (by simp)]
  simpa using h.2

end Sound

theorem chAH2_d0 : dChkAH "scc_rt_abort" 0 [0, 1, 2, 3] [4] [] Abort.Disp.d0 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_t1 : dChkAH ".L12_scc_rt_abort.0_entry" 0 [] [0, 1, 2, 3] [] Abort.Disp.t1 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_j1 : dChkAH ".L12_scc_rt_abort.0_entry" 4 [] [0] [] Abort.Disp.j1 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_t2 : dChkAH ".L12_scc_rt_abort.2_next1" 0 [] [0, 1, 2, 3] [] Abort.Disp.t2 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_j2 : dChkAH ".L12_scc_rt_abort.2_next1" 4 [] [0] [] Abort.Disp.j2 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_t3 : dChkAH ".L12_scc_rt_abort.4_next3" 0 [] [0, 1, 2, 3] [] Abort.Disp.t3 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_j3 : dChkAH ".L12_scc_rt_abort.4_next3" 4 [] [0] [] Abort.Disp.j3 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_t4 : dChkAH ".L12_scc_rt_abort.6_next5" 0 [] [0, 1, 2, 3] [3] Abort.Disp.t4 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_j4 : dChkAH ".L12_scc_rt_abort.6_next5" 4 [] [0] [] Abort.Disp.j4 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_t5 : dChkAH ".L12_scc_rt_abort.8_next7" 0 [] [0, 1, 2, 3] [] Abort.Disp.t5 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_g5 : dChkAH ".L12_scc_rt_abort.9_is8" 0 [] [] [] Abort.Disp.g5 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_b0T : dChkAH Abort.threads.fn 0 [] [] [] Abort.b0 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_b1T : dChkAH Abort.threads.entry 2 [] [] [] Abort.b1Threads = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_b2T : dChkAH Abort.threads.entry 8 [] [] [] Abort.b2 = true := by
  simp only [dChkAH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_n1 : siAbH Abort.threads.entry 0 = true := by
  simp only [siAbH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_n1b : siAbH Abort.threads.entry 1 = true := by
  simp only [siAbH, labC, ← codeT_eq]; decide +kernel
theorem chAH2_svc : siAbH Abort.threads.entry 7 = true := by
  simp only [siAbH, labC, ← codeT_eq]; decide +kernel

/-! ## The path -/

section Path

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl} {ra : BitVec 64}

set_option maxHeartbeats 800000 in
/-- **The threads abort path's nodes keep the write abort's phase** (`WakeWf.tpathW_ab` at hello's labels). -/
theorem tpathW_abH (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhThreadsOk okPc ph lab = true)
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → lab l = Int64.ofNat x)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a) :
    TPathW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F c0 ra := by
  have hl := hI.labOk
  subst hl
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, hj4, -, ht5, -, hg5, -⟩ := hdi
  simp only [abortPhThreadsOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pj2, pt3, pj3, pt4, pj4, pt5, pg5, pb0, o1, -, o1b, -, pb1, o7, -, pb2, -⟩ :=
    hphs
  have hoff : R.Off (-32) := ⟨by decide, by omega, by omega⟩
  -- the tests' data: the code `5` at `[sp]`
  have hTt : ∀ {blk : List Directive}, (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨
      blk = Abort.Disp.t4 ∨ blk = Abort.Disp.t5 ∨ blk = Abort.Disp.j1 ∨ blk = Abort.Disp.j2 ∨
      blk = Abort.Disp.j3 ∨ blk = Abort.Disp.j4) →
      ∀ (pc : Int64) (σ : Spike.Lib.A64.Flow.AS), (σ.slot (-32)).toNat = 5 → ∀ k, k < blk.length →
      (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).so.sp = -32 ∧
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1))
          ⟨pc, Abort.Disp.oD, σ⟩).σ.slot (-32) ≠ 4#64 := fun hb pc σ h5 k hk => by
    obtain ⟨h1, h3⟩ := tj_keep5 _ hb pc σ (j := k + 1) (by omega)
    refine ⟨h1, fun h => ?_⟩
    rw [h3] at h
    rw [h] at h5
    exact absurd h5 (by decide)
  have nE : ∀ {P : Prop} {k : Nat}, k ∈ ([] : List Nat) → P := fun h => by simp at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkW_dispAbI hI hd0 (add0 _) Abort.Disp.d0_ok hR hal (by omega) (by omega) hoff pd0 (by decide)
      (dChkAH_sound hlab chAH2_d0) (fun _ _ _ _ _ _ _ h => nE h) (fun σ c hJ k hk hkE => ?_)
      (fun σ c hJ k hk hkT => ?_)
    · dsimp only [DN.nd5] at hJ ⊢
      have hk4 : k + 1 < Abort.Disp.d0.length := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkE
        have : Abort.Disp.d0.length = 5 := by decide
        omega
      rw [Spike.Lib.A64.StubW.d0_x0 _ σ hk4]
      intro h
      have h2 := hJ.2.1
      rw [h] at h2
      exact absurd h2 (by decide)
    · dsimp only [DN.nd5] at hJ ⊢
      obtain rfl : k = 4 := by simpa using hkT
      obtain ⟨hsp, hsl⟩ := Spike.Lib.LowerA64.d0_end (_root_.Executable.labels exe).label
        ((_root_.Executable.labels exe).label "scc_rt_abort") σ
      refine ⟨hsp, fun h => ?_⟩
      have h' := congrArg BitVec.toNat (hsl.symm.trans h)
      rw [hJ.2.1] at h'
      exact absurd h' (by decide)
  · exact blkW_dispAbI hI ht1 (add0 _) Abort.Disp.t1_ok hR hal (by omega) (by omega) hoff pt1 (by decide)
      (dChkAH_sound hlab chAH2_t1) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj1 (by simp only [DN.nd5, add4, add0]) Abort.Disp.j1_ok hR hal (by omega)
      (by omega) hoff pj1 (by decide) (dChkAH_sound hlab chAH2_j1) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht2 (add0 _) Abort.Disp.t2_ok hR hal (by omega) (by omega) hoff pt2 (by decide)
      (dChkAH_sound hlab chAH2_t2) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj2 (by simp only [DN.nd5, add4, add0]) Abort.Disp.j2_ok hR hal (by omega)
      (by omega) hoff pj2 (by decide) (dChkAH_sound hlab chAH2_j2) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht3 (add0 _) Abort.Disp.t3_ok hR hal (by omega) (by omega) hoff pt3 (by decide)
      (dChkAH_sound hlab chAH2_t3) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj3 (by simp only [DN.nd5, add4, add0]) Abort.Disp.j3_ok hR hal (by omega)
      (by omega) hoff pj3 (by decide) (dChkAH_sound hlab chAH2_j3) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · refine blkW_dispAbI hI ht4 (add0 _) Abort.Disp.t4_ok hR hal (by omega) (by omega) hoff pt4 (by decide)
      (dChkAH_sound hlab chAH2_t4) (fun σ c hJ k hk a ha hkD => ?_) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
    obtain rfl : k = 3 := by simpa using hkD
    exact t4_fall _ _ _ σ hJ.2.1 ha
  · exact blkW_dispAbI hI hj4 (by simp only [DN.nd5, add4, add0]) Abort.Disp.j4_ok hR hal (by omega)
      (by omega) hoff pj4 (by decide) (dChkAH_sound hlab chAH2_j4) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht5 (add0 _) Abort.Disp.t5_ok hR hal (by omega) (by omega) hoff pt5 (by decide)
      (dChkAH_sound hlab chAH2_t5) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hg5 (add0 _) Abort.Disp.g5_ok hR hal (by omega) (by omega) hoff pg5 (by decide)
      (dChkAH_sound hlab chAH2_g5) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact blkW_dispAbI hI hb0 (add0 _) Abort.b0_ok hR hal (by omega) (by omega) hoff pb0 (by decide)
      (dChkAH_sound hlab chAH2_b0T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.A64.AllocG.nodeW_ab_si hI hn1 rfl (add0 _).symm o1 (siAbH_sound hlab chAH2_n1)
  · exact Spike.Lib.A64.AllocG.nodeW_ab_si hI hn1b rfl (by simp only [NT, add4, add0]) o1b
      (siAbH_sound hlab chAH2_n1b)
  · exact blkW_dispAbI hI hb1 (by simp only [NT, add4, add0]) Abort.b1Threads_ok hR hal (by omega) (by omega)
      hoff pb1 (by decide) (dChkAH_sound hlab chAH2_b1T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.LowerA64.nodeW_ab_svc hI hsvcIn rfl (by simp only [NT, Abort.pcSvc, add4, add0]) o7
      (siAbH_sound hlab chAH2_svc)
  · exact blkW_dispAbI hI hb2 (by simp only [NT, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal (by omega)
      (by omega) hoff pb2 (by decide) (dChkAH_sound hlab chAH2_b2T) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.LowerA64.nodeW_ab_exit hI hx (add0 _) rfl htk fun _ _ h => h.2.1

end Path

end Spike.Lib.A64.HelloWf

/-- info: 'Spike.Lib.A64.HelloWf.tpathW_abH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.tpathW_abH
