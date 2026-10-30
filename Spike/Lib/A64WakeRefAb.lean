/-
**The write abort's phase kept on the threads abort path** (`Wf`'s `AbSt`,
AArch64): every obligation of `TPathW` at `AbSt μ (WriteAb.Ab lab)`, none
moved, for an executable with `InstOk`, its program holding the runtime's
abort code (`abortIn`) and passing the path's phase check
(`abortPhThreadsOk`), its labels wake's code labels where they resolve
(`hlab`), the exit call off the take site (`htk`).

The dispatcher's prologue and tests reach pcs of the write abort guarded by
data (`WriteAb.dispEPcs` at `x0 = 4`, `dispTPcs` at `[sp] = 4`): on this path
the code is `5` there. The test against `4` (`Disp.t4`) branches to the
write stub's jump (`g4Pcs`) only at the code `4`; at `5` it falls through
(`t4_fall`), so that edge is dead in the check (`D`). Every other target of
the path is off the write abort's pcs.

- `tOkA`, `dChkA`, `dChkA_congr`, `dChkAW`, `dChkAW_sound`, `siAbW`,
  `siAbW_sound`: the checks, decided at wake's code labels.
- `blkW_dispAb`, `blkW_dispAbI`: a checked block's states in `AbSt`.
- `tj_keep5`, `t4_fall`: the tests' data at the code `5`.
- `tpathW_ab`: the path.
-/
import Spike.Lib.A64WakeWfHP
import Spike.Lib.A64WakeRefTP

namespace Spike.Lib.A64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.WakeRefTP (TPathW)
open Spike.Lib.A64.Abort (NT)
open Spike.Lib.A64.Abort.Disp (DN)
open Scc.Cert.Rt.A64 (blockAt codeT codeT_eq)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.LowerA64 (labC blkLabs nvPcs aiTgts_congr arun_succ_eq sp_slot)
open Spike.Lib.A64.AllocG (abLabs abPcs_congr)
open Spike.Lib.A64.WriteAb (dispEPcs dispTPcs)
open Spike.Lib.A64.StubW (abortPhThreadsOk phOne)

/-! ## The checks -/

/-- **A target of instruction `k` off the write abort but by data**: off its
pcs without a data condition, at the prologue's only if `k ∈ E`, at the
tests' only if `k ∈ T`. -/
def tOkA (lab : Label → Int64) (E T : List Nat) (k : Nat) (t : Int64) : Bool :=
  !(nvPcs lab).contains t && (E.contains k || !(dispEPcs lab).contains t) &&
    (T.contains k || !(dispTPcs lab).contains t)

/-- **A block's targets off the write abort but by data** (`tOkA`), the
block at `pc`, without a `ret`; instruction `k ∈ D` checked at its
fall-through only (its other edge dead by the node's data). -/
def dChkA (lab : Label → Int64) (pc : Int64) (E T D : List Nat) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match Spike.Lib.A64.Flow.classify d with
      | some a => (if D.contains k then [pc + Int64.ofNat (4 * k) + Int64.ofNat 4]
          else aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) 0 a).all (tOkA lab E T k)
      | none => false
    | none => false

theorem tOkA_congr {lab lab' : Label → Int64} {E T : List Nat} (ha : ∀ l ∈ abLabs, lab l = lab' l) :
    tOkA lab E T = tOkA lab' E T := by
  unfold tOkA
  rw [nvPcs_congr' ha, dispEPcs_congr ha, dispTPcs_congr ha]

theorem dChkA_congr {lab lab' : Label → Int64} {pc : Int64} {E T D : List Nat} {blk : List Directive}
    (h : ∀ L ∈ blkLabs blk, lab L = lab' L) (ha : ∀ l ∈ abLabs, lab l = lab' l) :
    dChkA lab pc E T D blk = dChkA lab' pc E T D blk := by
  unfold dChkA
  rw [tOkA_congr ha]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some d =>
    simp only
    cases hc' : Spike.Lib.A64.Flow.classify d with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, by rw [hc']; exact hL⟩

/-- **`dChkA` at wake's code labels**, every label it reads resolving, the
block at `lab l + 4 k`. -/
def dChkAW (l : Label) (k : Nat) (E T D : List Nat) (blk : List Directive) : Bool :=
  (l :: blkLabs blk ++ abLabs).all
      (fun x => (codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg x).isSome) &&
    dChkA (labC Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg)
      (labC Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l + Int64.ofNat (4 * k)) E T D blk

/-- **A single instruction's next pc off the write abort's pcs** at wake's
code labels, the instruction at `lab l + 4 k`. -/
def siAbW (l : Label) (k : Nat) : Bool :=
  (l :: abLabs).all (fun x => (codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg x).isSome) &&
    !(Spike.Lib.A64.WriteAb.abPcs (labC Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg)).contains
      (labC Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l + Int64.ofNat (4 * k) + 4)

section Sound

variable {lab : Label → Int64}
  (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l = some x → lab l = Int64.ofNat x)
include hlab

/-- **`dChkAW` at any labels agreeing with the code labels.** -/
theorem dChkAW_sound {l : Label} {k : Nat} {E T D : List Nat} {blk : List Directive}
    (h : dChkAW l k E T D blk = true) : dChkA lab (lab l + Int64.ofNat (4 * k)) E T D blk = true := by
  simp only [dChkAW, Bool.and_eq_true] at h
  have hl := lab_labC hlab h.1
  rw [dChkA_congr (fun x hx => hl x (by simp [hx])) (fun x hx => hl x (by simp [hx])), hl l (by simp)]
  exact h.2

/-- **`siAbW` at any labels agreeing with the code labels.** -/
theorem siAbW_sound {l : Label} {k : Nat} (h : siAbW l k = true) :
    lab l + Int64.ofNat (4 * k) + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab := by
  simp only [siAbW, Bool.and_eq_true] at h
  have hl := lab_labC hlab h.1
  rw [abPcs_congr (fun x hx => hl x (by simp [hx])), hl l (by simp)]
  simpa using h.2

end Sound

/-! ## A checked block keeps the phase -/

section Blk

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

set_option hygiene false in
/-- The labels of the executable. -/
local notation "lb" => (_root_.Executable.labels exe).label

/-- **A checked block's states keep the write abort's phase**: a covered
block without a `ret` (`hnr`), its pcs off the marks' sites (`hpc`), its
targets off the phase but by data (`h`), instruction `k ∈ D` falling
through (`hD`), the code off `4` in `x0` past `k ∈ E` (`hE`) and at `[sp]`
past `k ∈ T` (`hT`). -/
theorem blkW_dispAb {n : ND} {blk : List Directive} {lo hi : Int} {E T D : List Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-32))
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s)
    (hnr : noRetBlk blk = true) (h : dChkA lb n.pc E T D blk = true)
    (hD : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, Spike.Lib.A64.Flow.classify blk[k] = some a → k ∈ D →
      a.tgt lb (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun lb (blk.take k) ⟨n.pc, n.o, σ⟩).σ = n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (Spike.Lib.A64.Flow.arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.X0 ≠ 4)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (Spike.Lib.A64.Flow.arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.sp = -32 ∧
      (Spike.Lib.A64.Flow.arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot (-32) ≠ 4#64) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab lb) s) (fun _ _ => False) exe endPc R F n blk := by
  refine blkW_abSt hcode hok hR hal hlo hhi hpc ?_
  intro σ c hJ k hk a ha s' _ _ hpc' hA'
  obtain ⟨hso, hst⟩ := arun_succ_eq _ (am := ⟨n.pc, n.o, σ⟩) hok hk ha
  rw [hso, hst] at hA'
  have hc := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at hc
  have ht : tOkA lb E T k s'.st.2 = true := by
    by_cases hkD : k ∈ D
    · simp only [show D.contains k = true by simp [hkD], ↓reduceIte] at hc
      rw [hpc', hD σ c hJ k hk a ha hkD]
      exact List.all_eq_true.mp hc _ (List.mem_singleton_self _)
    · simp only [show D.contains k = false by simp [hkD], Bool.false_eq_true, ↓reduceIte] at hc
      rw [hpc']
      exact List.all_eq_true.mp hc _ (aiTgt_mem (lab := lb) a
        fun r hr => (noRet_false hnr k hk r (hr ▸ ha)).elim)
  simp only [tOkA, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_true_eq, decide_eq_false_iff_not] at ht
  obtain ⟨⟨hnv, hE'⟩, hT'⟩ := ht
  rintro (⟨h1, -⟩ | ⟨h1, -⟩ | h1 | ⟨h1, h4⟩ | ⟨h1, h4⟩ | h1 | h1)
  · exact hnv (by simp [nvPcs, h1])
  · exact hnv (by simp [nvPcs, h1])
  · exact hnv (by simp [nvPcs, h1])
  · rcases hE' with hk' | hk'
    · exact hE σ c hJ k hk hk' (by rw [hA'.regs] at h4; exact h4)
    · exact hk' h1
  · rcases hT' with hk' | hk'
    · obtain ⟨hs, hsl⟩ := hT σ c hJ k hk hk'
      rw [sp_slot hA' hs hoff] at h4
      exact hsl (Option.some.inj h4)
    · exact hk' h1
  · exact hnv (by simp [nvPcs, h1])
  · exact hnv (by simp [nvPcs, h1])

variable [Kraken.Executable.ValidLayout exe] {prog : List Directive} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **`blkW_dispAb` at a block of the program.** -/
theorem blkW_dispAbI (hI : InstOk exe endPc prog lb μ own Tk K okPc ph kp)
    {n : ND} {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat} {E T D : List Nat}
    (hb : blockAt prog l k blk = true) (he : lb l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-32))
    (hph : blkPh okPc ph (fun _ => false) lb (lb l + Int64.ofNat (4 * k)) 0 blk = true)
    (hnr : noRetBlk blk = true) (h : dChkA lb (lb l + Int64.ofNat (4 * k)) E T D blk = true)
    (hD : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, Spike.Lib.A64.Flow.classify blk[k] = some a → k ∈ D →
      a.tgt lb (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun lb (blk.take k) ⟨n.pc, n.o, σ⟩).σ = n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (Spike.Lib.A64.Flow.arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.X0 ≠ 4)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (Spike.Lib.A64.Flow.arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.sp = -32 ∧
      (Spike.Lib.A64.Flow.arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot (-32) ≠ 4#64) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab lb) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph h
  exact blkW_dispAb (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb he) hok hR hal hlo hhi hoff
    (hpcOf hI hok hph hnr) hnr h hD hE hT

end Blk

/-! ## The tests' data at the code `5` -/

section Run

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over the dispatcher's blocks. -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.A64.Flow.arun, Spike.Lib.A64.Flow.dstep, Spike.Lib.A64.Flow.classify,
    Spike.Lib.A64.Flow.RegOnly, Spike.Lib.A64.Flow.AI.so, Spike.Lib.A64.Flow.AI.step,
    Spike.Lib.A64.Flow.AI.tgt, Spike.Lib.A64.Flow.soReg, Spike.Lib.A64.Flow.regDst, Spike.Lib.A64.Flow.zrB,
    Spike.Lib.A64.Flow.regRes, Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp,
    Reg64s.setRegOrZr, Reg64s.getRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64, Reg64s.setRegOrSp,
    Reg64s.getRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64, Reg64s.setXReg, Reg64s.getXReg,
    ShiftRegExpr.interp, ExtOrImmReg.interp, ConstExpr.interp, RegOrZr.base, RegOrSp.base,
    Spike.Lib.A64.Flow.SO.get, Spike.Lib.A64.Flow.SO.set, Spike.Lib.A64.Flow.SO.kill,
    Spike.Lib.A64.Flow.SO.write, Spike.Lib.A64.Flow.SO.killZ, Spike.Lib.lk, Spike.Lib.rm, Spike.Lib.upd_apply])

/-- **The dispatcher's five tests and four jumps keep `sp` at the frame's
`-32` and `[sp]`** through their end. -/
theorem tj_keep5 (lab : Label → Int64) {blk : List Directive}
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4 ∨
      blk = Abort.Disp.t5 ∨ blk = Abort.Disp.j1 ∨ blk = Abort.Disp.j2 ∨ blk = Abort.Disp.j3 ∨
      blk = Abort.Disp.j4)
    (pc : Int64) (σ : Spike.Lib.A64.Flow.AS) {j : Nat} (hj : j ≤ blk.length) :
    (Spike.Lib.A64.Flow.arun lab (blk.take j) ⟨pc, Abort.Disp.oD, σ⟩).so.sp = -32 ∧
      (Spike.Lib.A64.Flow.arun lab (blk.take j) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot (-32) = σ.slot (-32) := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4, Abort.Disp.t5, Abort.Disp.j1,
      Abort.Disp.j2, Abort.Disp.j3, Abort.Disp.j4] at hj ⊢ <;>
    simp only [List.length_cons, List.length_nil] at hj <;>
    rcases j with _|_|_|_|_|j <;> (try omega) <;> arun_simp

/-- **The test against `4` falls through at the code `5`.** -/
theorem t4_fall (lab : Label → Int64) (pc fall : Int64) (σ : Spike.Lib.A64.Flow.AS)
    (h5 : (σ.slot (-32)).toNat = 5) {a : Spike.Lib.A64.Flow.AI}
    (ha : Spike.Lib.A64.Flow.classify (Abort.Disp.t4[3]'(by decide)) = some a) :
    a.tgt lab fall (Spike.Lib.A64.Flow.arun lab (Abort.Disp.t4.take 3) ⟨pc, Abort.Disp.oD, σ⟩).σ = fall := by
  have e : σ.slot (-32) = 5#64 := BitVec.eq_of_toNat_eq (by simpa using h5)
  simp only [Abort.Disp.t4] at ha ⊢
  simp [Spike.Lib.A64.Flow.classify] at ha
  subst ha
  arun_simp
  simp [e]

end Run

/-! ## The checks at wake's code labels -/

theorem chA_d0 : dChkAW "scc_rt_abort" 0 [0, 1, 2, 3] [4] [] Abort.Disp.d0 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_t1 : dChkAW ".L12_scc_rt_abort.0_entry" 0 [] [0, 1, 2, 3] [] Abort.Disp.t1 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_j1 : dChkAW ".L12_scc_rt_abort.0_entry" 4 [] [0] [] Abort.Disp.j1 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_t2 : dChkAW ".L12_scc_rt_abort.2_next1" 0 [] [0, 1, 2, 3] [] Abort.Disp.t2 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_j2 : dChkAW ".L12_scc_rt_abort.2_next1" 4 [] [0] [] Abort.Disp.j2 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_t3 : dChkAW ".L12_scc_rt_abort.4_next3" 0 [] [0, 1, 2, 3] [] Abort.Disp.t3 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_j3 : dChkAW ".L12_scc_rt_abort.4_next3" 4 [] [0] [] Abort.Disp.j3 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_t4 : dChkAW ".L12_scc_rt_abort.6_next5" 0 [] [0, 1, 2, 3] [3] Abort.Disp.t4 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_j4 : dChkAW ".L12_scc_rt_abort.6_next5" 4 [] [0] [] Abort.Disp.j4 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_t5 : dChkAW ".L12_scc_rt_abort.8_next7" 0 [] [0, 1, 2, 3] [] Abort.Disp.t5 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_g5 : dChkAW ".L12_scc_rt_abort.9_is8" 0 [] [] [] Abort.Disp.g5 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_b0T : dChkAW Abort.threads.fn 0 [] [] [] Abort.b0 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_b1T : dChkAW Abort.threads.entry 2 [] [] [] Abort.b1Threads = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_b2T : dChkAW Abort.threads.entry 8 [] [] [] Abort.b2 = true := by
  simp only [dChkAW, labC, ← codeT_eq]; decide +kernel
theorem chA_n1 : siAbW Abort.threads.entry 0 = true := by
  simp only [siAbW, labC, ← codeT_eq]; decide +kernel
theorem chA_n1b : siAbW Abort.threads.entry 1 = true := by
  simp only [siAbW, labC, ← codeT_eq]; decide +kernel
theorem chA_svc : siAbW Abort.threads.entry 7 = true := by
  simp only [siAbW, labC, ← codeT_eq]; decide +kernel

/-! ## The path -/

section Path

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl} {ra : BitVec 64}

set_option maxHeartbeats 800000 in
/-- **The threads abort path's nodes keep the write abort's phase.** -/
theorem tpathW_ab (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhThreadsOk okPc ph lab = true)
    (hlab : ∀ l x, codeOf Spike.Lib.A64.WakePh.lo Spike.Lib.A64.WakeLabels.wakeProg l = some x →
      lab l = Int64.ofNat x)
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
      (dChkAW_sound hlab chA_d0) (fun _ _ _ _ _ _ _ h => nE h) (fun σ c hJ k hk hkE => ?_)
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
      (dChkAW_sound hlab chA_t1) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj1 (by simp only [DN.nd5, add4, add0]) Abort.Disp.j1_ok hR hal (by omega)
      (by omega) hoff pj1 (by decide) (dChkAW_sound hlab chA_j1) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht2 (add0 _) Abort.Disp.t2_ok hR hal (by omega) (by omega) hoff pt2 (by decide)
      (dChkAW_sound hlab chA_t2) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj2 (by simp only [DN.nd5, add4, add0]) Abort.Disp.j2_ok hR hal (by omega)
      (by omega) hoff pj2 (by decide) (dChkAW_sound hlab chA_j2) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht3 (add0 _) Abort.Disp.t3_ok hR hal (by omega) (by omega) hoff pt3 (by decide)
      (dChkAW_sound hlab chA_t3) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj3 (by simp only [DN.nd5, add4, add0]) Abort.Disp.j3_ok hR hal (by omega)
      (by omega) hoff pj3 (by decide) (dChkAW_sound hlab chA_j3) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · refine blkW_dispAbI hI ht4 (add0 _) Abort.Disp.t4_ok hR hal (by omega) (by omega) hoff pt4 (by decide)
      (dChkAW_sound hlab chA_t4) (fun σ c hJ k hk a ha hkD => ?_) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
    obtain rfl : k = 3 := by simpa using hkD
    exact t4_fall _ _ _ σ hJ.2.1 ha
  · exact blkW_dispAbI hI hj4 (by simp only [DN.nd5, add4, add0]) Abort.Disp.j4_ok hR hal (by omega)
      (by omega) hoff pj4 (by decide) (dChkAW_sound hlab chA_j4) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht5 (add0 _) Abort.Disp.t5_ok hR hal (by omega) (by omega) hoff pt5 (by decide)
      (dChkAW_sound hlab chA_t5) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hg5 (add0 _) Abort.Disp.g5_ok hR hal (by omega) (by omega) hoff pg5 (by decide)
      (dChkAW_sound hlab chA_g5) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact blkW_dispAbI hI hb0 (add0 _) Abort.b0_ok hR hal (by omega) (by omega) hoff pb0 (by decide)
      (dChkAW_sound hlab chA_b0T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.A64.AllocG.nodeW_ab_si hI hn1 rfl (add0 _).symm o1 (siAbW_sound hlab chA_n1)
  · exact Spike.Lib.A64.AllocG.nodeW_ab_si hI hn1b rfl (by simp only [NT, add4, add0]) o1b
      (siAbW_sound hlab chA_n1b)
  · exact blkW_dispAbI hI hb1 (by simp only [NT, add4, add0]) Abort.b1Threads_ok hR hal (by omega) (by omega)
      hoff pb1 (by decide) (dChkAW_sound hlab chA_b1T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.LowerA64.nodeW_ab_svc hI hsvcIn rfl (by simp only [NT, Abort.pcSvc, add4, add0]) o7
      (siAbW_sound hlab chA_svc)
  · exact blkW_dispAbI hI hb2 (by simp only [NT, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal (by omega)
      (by omega) hoff pb2 (by decide) (dChkAW_sound hlab chA_b2T) (fun _ _ _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.LowerA64.nodeW_ab_exit hI hx (add0 _) rfl htk fun _ _ h => h.2.1

end Path

end Spike.Lib.A64.WakeWf

/-- info: 'Spike.Lib.A64.WakeWf.blkW_dispAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.blkW_dispAb

/-- info: 'Spike.Lib.A64.WakeWf.tpathW_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeWf.tpathW_ab
