/-
**The write abort's phase kept on hello.w's threads abort path** (x86-64; the
twin of `Spike/Lib/A64HelloRefAbT.lean`, the hello restatement of
`Spike/Lib/X64WakeRefAb.lean`'s `tpathW_ab`): every obligation of `TPathW` at
`AbSt μ (WriteAb.Ab lab)`, none moved, for an executable with `InstOk`, its
cells holding the runtime's abort code (`abortIn`) and passing the path's
phase check (`abortPhThreadsOk`), its labels hello's code labels where they
resolve (`hlab`), the exit call off the take site (`htk`).

Wake's checks (`WakeWf.tOkA`, `dChkA`, `dChkA_congr`), the block lemma
(`blkW_dispAbI`) and the tests' data (`tj_keep5`, `t4_fall`) are label
generic; only their instantiation at the code labels reads wake's cells, so
it is restated at `SccCode.helloCells` (at `X64.HelloPh.lo`, the code base
`0x401000`).

- `dChkAH`, `dChkAH_sound`, `siAbH`, `siAbH_sound`: the checks, decided at
  hello's code labels.
- `chAH2_*`: the checks.
- `tpathW_abH`: the path.

**Deviation from the A64 file.** The x86-64 shapes of `X64WakeRefAb` (byte
offsets, the code `4` at `-8(%rbp)`, the stub's blocks `x0`/`x1Threads`/`x2`,
one `leaq`, the `syscall` of two bytes, the region `[-24, 16)` and no
alignment premise): so the checks are `chAH2_x0T`/`x1T`/`x2T`/`n1`/`sys`
(A64's `b0T`/`b1T`/`b2T`/`n1`/`n1b`/`svc`).
-/
import Spike.Lib.X64WakeRefAb
import Spike.Lib.X64HelloPh

namespace Spike.Lib.X64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At CodeAt cellOff arun classify AS SO Abs okBlk)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.Abort (NT)
open Spike.Lib.X64.Abort.Disp (DN)
open Scc.Cert.Rt.X64 (blockAtB)
open Spike.Lib.LowerX64 (blkLabs aiTgts_congr labC nvPcs arun_succ_eq bp_slot)
open Spike.Lib.X64.AllocG (abLabs abPcs_congr)
open Spike.Lib.X64.WriteAb (dispEPcs)
open Spike.Lib.X64.StubW (abortPhThreadsOk phOne)
open Spike.Lib.X64.Flow (ofNat_zero')
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.WakeWf

/-! ## The checks at hello's code labels -/

/-- **`dChkA` at hello's code labels**, every label it reads resolving, the
block at `lab l + k` (bytes). -/
def dChkAH (l : Label) (k : Nat) (E T D : List Nat) (blk : List (Directive × Nat)) : Bool :=
  (l :: blkLabs blk ++ abLabs).all (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) &&
    dChkA (labC Spike.Lib.X64.HelloPh.lo helloCells)
      (labC Spike.Lib.X64.HelloPh.lo helloCells l + Int64.ofNat k) E T D blk

/-- **A single instruction's next pc off the write abort's pcs** at hello's
code labels, the instruction of `z` bytes at `lab l + k`. -/
def siAbH (l : Label) (k z : Nat) : Bool :=
  (l :: abLabs).all (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) &&
    !(WriteAb.abPcs (labC Spike.Lib.X64.HelloPh.lo helloCells)).contains
      (labC Spike.Lib.X64.HelloPh.lo helloCells l + Int64.ofNat k + Int64.ofNat z)

section Sound

variable {lab : Label → Int64}
  (hlab : ∀ l a, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some a → lab l = Int64.ofNat a)
include hlab

/-- The labels a check reads, resolving, are the code labels (`X64WakeWfPh.lab_labC` at hello's cells). -/
private theorem lab_labCH {xs : List String}
    (h : xs.all (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) = true) :
    ∀ x ∈ xs, lab x = labC Spike.Lib.X64.HelloPh.lo helloCells x := fun x hx => by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp h x hx)
  rw [hlab x y hy]; simp [labC, hy]

/-- **`dChkAH` at any labels agreeing with the code labels.** -/
theorem dChkAH_sound {l : Label} {k : Nat} {E T D : List Nat} {blk : List (Directive × Nat)}
    (h : dChkAH l k E T D blk = true) : dChkA lab (lab l + Int64.ofNat k) E T D blk = true := by
  simp only [dChkAH, Bool.and_eq_true] at h
  have hl := lab_labCH hlab h.1
  rw [dChkA_congr (fun x hx => hl x (by simp [hx])) (fun x hx => hl x (by simp [hx])), hl l (by simp)]
  exact h.2

/-- **`siAbH` at any labels agreeing with the code labels.** -/
theorem siAbH_sound {l : Label} {k z : Nat} (h : siAbH l k z = true) :
    lab l + Int64.ofNat k + Int64.ofNat z ∉ WriteAb.abPcs lab := by
  simp only [siAbH, Bool.and_eq_true] at h
  have hl := lab_labCH hlab h.1
  rw [abPcs_congr (fun x hx => hl x (by simp [hx])), hl l (by simp)]
  simpa using h.2

end Sound

/-! ## The checks at hello's code labels -/

theorem chAH2_d0 : dChkAH "scc_rt_abort" 0 [0, 1, 2] [3] [] Abort.Disp.d0 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_t1 : dChkAH ".Lscc_rt_abort.entry" 0 [] [0, 1, 2, 3] [] Abort.Disp.t1 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_j1 : dChkAH ".Lscc_rt_abort.entry" 16 [] [0] [] Abort.Disp.j1 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_t2 : dChkAH ".Lscc_rt_abort.next1" 0 [] [0, 1, 2, 3] [] Abort.Disp.t2 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_j2 : dChkAH ".Lscc_rt_abort.next1" 16 [] [0] [] Abort.Disp.j2 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_t3 : dChkAH ".Lscc_rt_abort.next3" 0 [] [0, 1, 2, 3] [] Abort.Disp.t3 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_j3 : dChkAH ".Lscc_rt_abort.next3" 16 [] [0] [] Abort.Disp.j3 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_t4 : dChkAH ".Lscc_rt_abort.next5" 0 [] [0, 1, 2, 3] [3] Abort.Disp.t4 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_j4 : dChkAH ".Lscc_rt_abort.next5" 16 [] [0] [] Abort.Disp.j4 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_t5 : dChkAH ".Lscc_rt_abort.next7" 0 [] [0, 1, 2, 3] [] Abort.Disp.t5 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_g5 : dChkAH ".Lscc_rt_abort.is8" 0 [] [] [] Abort.Disp.g5 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_x0T : dChkAH Abort.threads.fn 0 [] [] [] Abort.x0 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_x1T : dChkAH Abort.threads.entry 7 [] [] [] Abort.x1Threads = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_x2T : dChkAH Abort.threads.entry 36 [] [] [] Abort.x2 = true := by
  unfold dChkAH; decide +kernel
theorem chAH2_n1 : siAbH Abort.threads.entry 0 7 = true := by
  unfold siAbH; decide +kernel
theorem chAH2_sys : siAbH Abort.threads.entry 34 2 = true := by
  unfold siAbH; decide +kernel

/-! ## The path -/

section Path

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

set_option maxHeartbeats 800000 in
/-- **The threads abort path's nodes keep the write abort's phase** (`WakeWf.tpathW_ab` at hello's labels). -/
theorem tpathW_abH (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hphs : abortPhThreadsOk okPc ph lab = true)
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some a → lab l = Int64.ofNat a)
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a) :
    TPathW (fun s _ => AbSt μ (WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F c0 ra := by
  have hl := hI.labOk
  subst hl
  have hsd := hab
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, hj4, -, ht5, -, hg5, -⟩ := hdi
  have hst := hsd.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hx0, hn1, hx1, hsysIn, hx2, hx, -, -⟩ := hst
  simp only [abortPhThreadsOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pj2, pt3, pj3, pt4, pj4, pt5, pg5, px0, o1, -, px1, o34, -, px2, -⟩ := hphs
  have hoff : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  -- the tests' data: the code `5` at `-8(%rbp)`
  have hTt : ∀ {blk : List (Directive × Nat)}, (blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨
      blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4 ∨ blk = Abort.Disp.t5 ∨ blk = Abort.Disp.j1 ∨
      blk = Abort.Disp.j2 ∨ blk = Abort.Disp.j3 ∨ blk = Abort.Disp.j4) →
      ∀ (pc : Int64) (σ : AS), σ.slot (-8) = 5#64 → ∀ k, k < blk.length →
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨pc, Abort.Disp.oD, σ⟩).so.get .rbp =
          some 0 ∧
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot (-8) ≠
          4#64 := fun hb pc σ h5 k hk => by
    obtain ⟨h1, h3⟩ := tj_keep5 _ hb pc σ (j := k + 1) (by omega)
    refine ⟨h1, fun h => ?_⟩
    rw [h3, h5] at h
    exact absurd h (by decide)
  have nE : ∀ {P : Prop} {k : Nat}, k ∈ ([] : List Nat) → P := fun h => by simp at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkW_dispAbI hI hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR (by omega) (by omega) hoff pd0 (by decide)
      (dChkAH_sound hlab chAH2_d0) (fun _ _ _ _ _ _ _ h => nE h) (fun σ c hJ k hk hkE => ?_)
      (fun σ c hJ k hk hkT => ?_)
    · dsimp only [DN.nd5] at hJ ⊢
      have hk3 : k + 1 < Abort.Disp.d0.length := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkE
        have : Abort.Disp.d0.length = 4 := by decide
        omega
      rw [Spike.Lib.X64.StubW.d0_rdi _ σ hk3, hJ.2.1]
      decide
    · dsimp only [DN.nd5] at hJ ⊢
      obtain rfl : k = 3 := by simpa using hkT
      obtain ⟨hbp, hsl⟩ := Spike.Lib.LowerX64.d0_end (_root_.Executable.labels exe).label
        ((_root_.Executable.labels exe).label "scc_rt_abort") σ
      refine ⟨hbp, ?_⟩
      rw [hsl, hJ.2.1]
      decide
  · exact blkW_dispAbI hI ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR (by omega) (by omega) hoff pt1 (by decide)
      (dChkAH_sound hlab chAH2_t1) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj1 rfl Abort.Disp.j1_ok hR (by omega) (by omega) hoff pj1 (by decide)
      (dChkAH_sound hlab chAH2_j1) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR (by omega) (by omega) hoff pt2 (by decide)
      (dChkAH_sound hlab chAH2_t2) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj2 rfl Abort.Disp.j2_ok hR (by omega) (by omega) hoff pj2 (by decide)
      (dChkAH_sound hlab chAH2_j2) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht3 (ofNat_zero' _) Abort.Disp.t3_ok hR (by omega) (by omega) hoff pt3 (by decide)
      (dChkAH_sound hlab chAH2_t3) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj3 rfl Abort.Disp.j3_ok hR (by omega) (by omega) hoff pj3 (by decide)
      (dChkAH_sound hlab chAH2_j3) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · refine blkW_dispAbI hI ht4 (ofNat_zero' _) Abort.Disp.t4_ok hR (by omega) (by omega) hoff pt4 (by decide)
      (dChkAH_sound hlab chAH2_t4) (fun σ c hJ k hk a ha hkD => ?_) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
    obtain rfl : k = 3 := by simpa using hkD
    exact t4_fall _ _ _ σ hJ.2.1 ha
  · exact blkW_dispAbI hI hj4 rfl Abort.Disp.j4_ok hR (by omega) (by omega) hoff pj4 (by decide)
      (dChkAH_sound hlab chAH2_j4) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht5 (ofNat_zero' _) Abort.Disp.t5_ok hR (by omega) (by omega) hoff pt5 (by decide)
      (dChkAH_sound hlab chAH2_t5) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hg5 (ofNat_zero' _) Abort.Disp.g5_ok hR (by omega) (by omega) hoff pg5 (by decide)
      (dChkAH_sound hlab chAH2_g5) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact blkW_dispAbI hI hx0 (ofNat_zero' _) Abort.x0_ok hR (by omega) (by omega) hoff px0 (by decide)
      (dChkAH_sound hlab chAH2_x0T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.X64.AllocG.nodeW_ab_si hI hn1 rfl (ofNat_zero' _).symm o1 (siAbH_sound hlab chAH2_n1)
  · exact blkW_dispAbI hI hx1 rfl Abort.x1Threads_ok hR (by omega) (by omega) hoff px1 (by decide)
      (dChkAH_sound hlab chAH2_x1T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.LowerX64.nodeW_ab_sys hI hsysIn rfl rfl o34 (siAbH_sound hlab chAH2_sys)
  · exact blkW_dispAbI hI hx2 rfl Abort.x2_ok hR (by omega) (by omega) hoff px2 (by decide)
      (dChkAH_sound hlab chAH2_x2T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.LowerX64.nodeW_ab_exit hI hx (ofNat_zero' _) rfl htk fun _ _ h => h.2.1

end Path

end Spike.Lib.X64.HelloWf

/-- info: 'Spike.Lib.X64.HelloWf.chAH2_t4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.chAH2_t4

/-- info: 'Spike.Lib.X64.HelloWf.tpathW_abH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.tpathW_abH
