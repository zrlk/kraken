/-
**The write abort's phase kept on the threads abort path** (`Wf`'s `AbSt`,
x86-64; the twin of `Spike/Lib/A64WakeRefAb.lean`): every obligation of
`TPathW` at `AbSt μ (WriteAb.Ab lab)`, none moved, for an executable with
`InstOk`, its cells holding the runtime's abort code (`abortIn`) and passing
the path's phase check (`abortPhThreadsOk`), its labels wake's code labels
where they resolve (`hlab`), the exit call off the take site (`htk`).

The dispatcher's prologue and tests reach pcs of the write abort guarded by
data (`WriteAb.dispEPcs` at `%rdi = 4`, `dispTPcs` at `-8(%rbp) = 4`): on
this path the code is `5` there. The test against `4` (`Disp.t4`) branches
to the write stub's jump (`g4Pcs`) only at the code `4`; at `5` it falls
through (`t4_fall`), so that edge is dead in the check (`D`). Every other
target of the path is off the write abort's pcs.

- `tOkA`, `dChkA`, `tOkA_congr`, `dChkA_congr`, `dChkAW`, `dChkAW_sound`,
  `siAbW`, `siAbW_sound`: the checks, decided at wake's code labels.
- `blkW_dispAb`, `blkW_dispAbI`: a checked block's states in `AbSt`.
- `tj_keep5`, `t4_fall`: the tests' data at the code `5`.
- `chAb_*`: the checks at wake's code labels; `tpathW_ab`: the path.

**Where this differs from AArch64** (forced by the x86-64 shape):
- offsets are bytes: a block's `k`-th instruction is at `pc + cellOff blk k`,
  its fall-through `+ blk[k].2` (A64: `pc + 4k + 4`); `dChkAW` takes the
  block's byte offset from its label, `siAbW` the instruction's size;
- the code `4` is at `-8(%rbp)` past the prologue (`WriteAb.Ab`'s
  `bpLoad s (-8)`), so `hT` asks the abstract run's offsets to have `%rbp`
  at the frame base and its slot `-8` off `4` (`LowerX64.bp_slot`; A64:
  `sp` at `-32` and `[sp]`), with `hoff : R.Off (-8)`; the prologue stores
  the code at its fourth instruction (`E = [0, 1, 2]`, `T = [3]`; A64's
  `[0, 1, 2, 3]`, `[4]`);
- a target reads the offsets (`a.tgt lab so`), so `hD` and `t4_fall` are
  stated at the run's offsets too;
- the stub's `leaq` is one instruction (A64's `adrp`/`add`, `chAb_n1b`), and
  the `write` call is a `syscall` of two bytes (`LowerX64.nodeW_ab_sys`;
  A64's `svc`, `nodeW_ab_svc`); the stub's blocks are `x0`, `x1Threads`,
  `x2` (A64's `b0`, `b1Threads`, `b2`);
- the region is `[-24, 16)` (A64's `[-48, 0)`), no alignment premise
  (`hal`; x86-64's `blkW_abSt` has none).
-/
import Spike.Lib.X64WakeWfHP
import Spike.Lib.X64WakeRefTP

namespace Spike.Lib.X64.WakeWf

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
open SccCode (wakeCells)

/-! ## The checks -/

/-- **A target of instruction `k` off the write abort but by data**: off its
pcs without a data condition, at the prologue's only if `k ∈ E`, at the
tests' only if `k ∈ T`. -/
def tOkA (lab : Label → Int64) (E T : List Nat) (k : Nat) (t : Int64) : Bool :=
  !(nvPcs lab).contains t && (E.contains k || !(dispEPcs lab).contains t) &&
    (T.contains k || !(WriteAb.dispTPcs lab).contains t)

/-- **A block's targets off the write abort but by data** (`tOkA`), the
block at `pc`, without a `ret`; instruction `k ∈ D` checked at its
fall-through only (its other edge dead by the node's data). -/
def dChkA (lab : Label → Int64) (pc : Int64) (E T D : List Nat) (blk : List (Directive × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some dz => match classify dz.1 with
      | some a => (if D.contains k then [pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2]
          else aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) 0 a).all (tOkA lab E T k)
      | none => false
    | none => false

theorem tOkA_congr {lab lab' : Label → Int64} {E T : List Nat} (ha : ∀ l ∈ abLabs, lab l = lab' l) :
    tOkA lab E T = tOkA lab' E T := by
  unfold tOkA
  rw [nvPcs_congr' ha, dispEPcs_congr ha, dispTPcs_congr ha]

theorem dChkA_congr {lab lab' : Label → Int64} {pc : Int64} {E T D : List Nat} {blk : List (Directive × Nat)}
    (h : ∀ L ∈ blkLabs blk, lab L = lab' L) (ha : ∀ l ∈ abLabs, lab l = lab' l) :
    dChkA lab pc E T D blk = dChkA lab' pc E T D blk := by
  unfold dChkA
  rw [tOkA_congr ha]
  congr 1
  funext k
  cases hk : blk[k]? with
  | none => rfl
  | some dz =>
    simp only
    cases hc' : classify dz.1 with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨dz, List.mem_of_getElem? hk, by rw [hc']; exact hL⟩

/-- **`dChkA` at wake's code labels**, every label it reads resolving, the
block at `lab l + k` (bytes). -/
def dChkAW (l : Label) (k : Nat) (E T D : List Nat) (blk : List (Directive × Nat)) : Bool :=
  (l :: blkLabs blk ++ abLabs).all (fun x => (codeLabel Spike.Lib.X64.WakePh.lo wakeCells x).isSome) &&
    dChkA (labC Spike.Lib.X64.WakePh.lo wakeCells)
      (labC Spike.Lib.X64.WakePh.lo wakeCells l + Int64.ofNat k) E T D blk

/-- **A single instruction's next pc off the write abort's pcs** at wake's
code labels, the instruction of `z` bytes at `lab l + k`. -/
def siAbW (l : Label) (k z : Nat) : Bool :=
  (l :: abLabs).all (fun x => (codeLabel Spike.Lib.X64.WakePh.lo wakeCells x).isSome) &&
    !(WriteAb.abPcs (labC Spike.Lib.X64.WakePh.lo wakeCells)).contains
      (labC Spike.Lib.X64.WakePh.lo wakeCells l + Int64.ofNat k + Int64.ofNat z)

section Sound

variable {lab : Label → Int64}
  (hlab : ∀ l a, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some a → lab l = Int64.ofNat a)
include hlab

/-- **`dChkAW` at any labels agreeing with the code labels.** -/
theorem dChkAW_sound {l : Label} {k : Nat} {E T D : List Nat} {blk : List (Directive × Nat)}
    (h : dChkAW l k E T D blk = true) : dChkA lab (lab l + Int64.ofNat k) E T D blk = true := by
  simp only [dChkAW, Bool.and_eq_true] at h
  have hl := lab_labC hlab h.1
  rw [dChkA_congr (fun x hx => hl x (by simp [hx])) (fun x hx => hl x (by simp [hx])), hl l (by simp)]
  exact h.2

/-- **`siAbW` at any labels agreeing with the code labels.** -/
theorem siAbW_sound {l : Label} {k z : Nat} (h : siAbW l k z = true) :
    lab l + Int64.ofNat k + Int64.ofNat z ∉ WriteAb.abPcs lab := by
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
through (`hD`), the code off `4` in `%rdi` past `k ∈ E` (`hE`) and at
`-8(%rbp)` past `k ∈ T` (`hT`). -/
theorem blkW_dispAb {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {E T D : List Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-8))
    (hpc : ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk j) → PcOff μ s)
    (hnr : noRetBlk blk = true) (h : dChkA lb n.pc E T D blk = true)
    (hD : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a → k ∈ D →
      a.tgt lb (arun lb (blk.take k) ⟨n.pc, n.o, σ⟩).so (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun lb (blk.take k) ⟨n.pc, n.o, σ⟩).σ = n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.get .rbp = some 0 ∧
      (arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot (-8) ≠ 4#64) :
    BlkW (fun s _ => AbSt μ (WriteAb.Ab lb) s) (fun _ _ => False) exe endPc R F n blk := by
  refine blkW_abSt hcode hok hR hlo hhi hpc ?_
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
      exact List.all_eq_true.mp hc _ (aiTgt_mem (lab := lb) a fun r => (noRet_false hnr k hk (r ▸ ha)).elim)
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
      rw [bp_slot hA' hs hoff] at h4
      exact hsl (Option.some.inj h4)
    · exact hk' h1
  · exact hnv (by simp [nvPcs, h1])
  · exact hnv (by simp [nvPcs, h1])

variable [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **`blkW_dispAb` at a block of the program.** -/
theorem blkW_dispAbI (hI : InstOk exe endPc cells lb μ own Tk K okPc ph kp)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {l : Label} {k : Nat} {E T D : List Nat}
    (hb : blockAtB cells l k blk = true) (he : lb l + Int64.ofNat k = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-8))
    (hph : blkPh okPc ph (fun _ => false) lb (lb l + Int64.ofNat k) 0 blk = true)
    (hnr : noRetBlk blk = true) (h : dChkA lb (lb l + Int64.ofNat k) E T D blk = true)
    (hD : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a → k ∈ D →
      a.tgt lb (arun lb (blk.take k) ⟨n.pc, n.o, σ⟩).so (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun lb (blk.take k) ⟨n.pc, n.o, σ⟩).σ = n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.get .rbp = some 0 ∧
      (arun lb (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot (-8) ≠ 4#64) :
    BlkW (fun s _ => AbSt μ (WriteAb.Ab lb) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph h
  exact blkW_dispAb (fun s hs hn => he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn) hok hR hlo hhi hoff
    (hpcOf hI hok hph hnr) hnr h hD hE hT

end Blk

/-! ## The tests' data at the code `5` -/

section Run

set_option linter.unusedSimpArgs false

open Spike.Lib.X64 in
/-- The abstract run's simp set over the dispatcher's blocks. -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [arun, dstep, classify, RegOnly, AI.so, soReg, regDst, regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply, Reg64s.get_low64, BlockSpec.AI.step_ld', BlockSpec.AI.step_st',
    BlockSpec.AI.step_push', BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', BlockSpec.AI.step_jmp',
    BlockSpec.AI.step_jcc'])

/-- **The dispatcher's five tests and four jumps keep `%rbp` at the frame's
base and `-8(%rbp)`** through their end. -/
theorem tj_keep5 (lab : Label → Int64) {blk : List (Directive × Nat)}
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4 ∨
      blk = Abort.Disp.t5 ∨ blk = Abort.Disp.j1 ∨ blk = Abort.Disp.j2 ∨ blk = Abort.Disp.j3 ∨
      blk = Abort.Disp.j4)
    (pc : Int64) (σ : AS) {j : Nat} (hj : j ≤ blk.length) :
    (arun lab (blk.take j) ⟨pc, Abort.Disp.oD, σ⟩).so.get .rbp = some 0 ∧
      (arun lab (blk.take j) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot (-8) = σ.slot (-8) := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4, Abort.Disp.t5, Abort.Disp.j1,
      Abort.Disp.j2, Abort.Disp.j3, Abort.Disp.j4, List.length_zip, List.length_cons,
      List.length_nil] at hj ⊢ <;>
    rcases j with _|_|_|_|_|j <;> (try omega) <;> arun_simp

/-- **The test against `4` falls through at the code `5`.** -/
theorem t4_fall (lab : Label → Int64) (pc fall : Int64) (σ : AS) (h5 : σ.slot (-8) = 5#64) {a : Spike.Lib.X64.AI}
    (ha : classify (Abort.Disp.t4[3]'(by decide)).1 = some a) :
    a.tgt lab (arun lab (Abort.Disp.t4.take 3) ⟨pc, Abort.Disp.oD, σ⟩).so fall
      (arun lab (Abort.Disp.t4.take 3) ⟨pc, Abort.Disp.oD, σ⟩).σ = fall := by
  simp only [Abort.Disp.t4] at ha ⊢
  simp [classify] at ha
  subst ha
  arun_simp
  simp [h5, BlockSpec.AI.tgt_jcc']

end Run

/-! ## The checks at wake's code labels -/

theorem chAb_d0 : dChkAW "scc_rt_abort" 0 [0, 1, 2] [3] [] Abort.Disp.d0 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_t1 : dChkAW ".Lscc_rt_abort.entry" 0 [] [0, 1, 2, 3] [] Abort.Disp.t1 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_j1 : dChkAW ".Lscc_rt_abort.entry" 16 [] [0] [] Abort.Disp.j1 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_t2 : dChkAW ".Lscc_rt_abort.next1" 0 [] [0, 1, 2, 3] [] Abort.Disp.t2 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_j2 : dChkAW ".Lscc_rt_abort.next1" 16 [] [0] [] Abort.Disp.j2 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_t3 : dChkAW ".Lscc_rt_abort.next3" 0 [] [0, 1, 2, 3] [] Abort.Disp.t3 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_j3 : dChkAW ".Lscc_rt_abort.next3" 16 [] [0] [] Abort.Disp.j3 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_t4 : dChkAW ".Lscc_rt_abort.next5" 0 [] [0, 1, 2, 3] [3] Abort.Disp.t4 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_j4 : dChkAW ".Lscc_rt_abort.next5" 16 [] [0] [] Abort.Disp.j4 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_t5 : dChkAW ".Lscc_rt_abort.next7" 0 [] [0, 1, 2, 3] [] Abort.Disp.t5 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_g5 : dChkAW ".Lscc_rt_abort.is8" 0 [] [] [] Abort.Disp.g5 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_x0T : dChkAW Abort.threads.fn 0 [] [] [] Abort.x0 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_x1T : dChkAW Abort.threads.entry 7 [] [] [] Abort.x1Threads = true := by
  unfold dChkAW; decide +kernel
theorem chAb_x2T : dChkAW Abort.threads.entry 36 [] [] [] Abort.x2 = true := by
  unfold dChkAW; decide +kernel
theorem chAb_n1 : siAbW Abort.threads.entry 0 7 = true := by
  unfold siAbW; decide +kernel
theorem chAb_sys : siAbW Abort.threads.entry 34 2 = true := by
  unfold siAbW; decide +kernel

/-! ## The path -/

section Path

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}

set_option maxHeartbeats 800000 in
/-- **The threads abort path's nodes keep the write abort's phase.** -/
theorem tpathW_ab (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hphs : abortPhThreadsOk okPc ph lab = true)
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some a → lab l = Int64.ofNat a)
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
      (dChkAW_sound hlab chAb_d0) (fun _ _ _ _ _ _ _ h => nE h) (fun σ c hJ k hk hkE => ?_)
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
      (dChkAW_sound hlab chAb_t1) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj1 rfl Abort.Disp.j1_ok hR (by omega) (by omega) hoff pj1 (by decide)
      (dChkAW_sound hlab chAb_j1) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR (by omega) (by omega) hoff pt2 (by decide)
      (dChkAW_sound hlab chAb_t2) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj2 rfl Abort.Disp.j2_ok hR (by omega) (by omega) hoff pj2 (by decide)
      (dChkAW_sound hlab chAb_j2) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht3 (ofNat_zero' _) Abort.Disp.t3_ok hR (by omega) (by omega) hoff pt3 (by decide)
      (dChkAW_sound hlab chAb_t3) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hj3 rfl Abort.Disp.j3_ok hR (by omega) (by omega) hoff pj3 (by decide)
      (dChkAW_sound hlab chAb_j3) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · refine blkW_dispAbI hI ht4 (ofNat_zero' _) Abort.Disp.t4_ok hR (by omega) (by omega) hoff pt4 (by decide)
      (dChkAW_sound hlab chAb_t4) (fun σ c hJ k hk a ha hkD => ?_) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
    obtain rfl : k = 3 := by simpa using hkD
    exact t4_fall _ _ _ σ hJ.2.1 ha
  · exact blkW_dispAbI hI hj4 rfl Abort.Disp.j4_ok hR (by omega) (by omega) hoff pj4 (by decide)
      (dChkAW_sound hlab chAb_j4) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI ht5 (ofNat_zero' _) Abort.Disp.t5_ok hR (by omega) (by omega) hoff pt5 (by decide)
      (dChkAW_sound hlab chAb_t5) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun σ c hJ k hk _ => hTt (by simp) _ σ hJ.2.1 k hk)
  · exact blkW_dispAbI hI hg5 (ofNat_zero' _) Abort.Disp.g5_ok hR (by omega) (by omega) hoff pg5 (by decide)
      (dChkAW_sound hlab chAb_g5) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact blkW_dispAbI hI hx0 (ofNat_zero' _) Abort.x0_ok hR (by omega) (by omega) hoff px0 (by decide)
      (dChkAW_sound hlab chAb_x0T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.X64.AllocG.nodeW_ab_si hI hn1 rfl (ofNat_zero' _).symm o1 (siAbW_sound hlab chAb_n1)
  · exact blkW_dispAbI hI hx1 rfl Abort.x1Threads_ok hR (by omega) (by omega) hoff px1 (by decide)
      (dChkAW_sound hlab chAb_x1T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.LowerX64.nodeW_ab_sys hI hsysIn rfl rfl o34 (siAbW_sound hlab chAb_sys)
  · exact blkW_dispAbI hI hx2 rfl Abort.x2_ok hR (by omega) (by omega) hoff px2 (by decide)
      (dChkAW_sound hlab chAb_x2T) (fun _ _ _ _ _ _ _ h => nE h) (fun _ _ _ _ _ h => nE h)
      (fun _ _ _ _ _ h => nE h)
  · exact Spike.Lib.LowerX64.nodeW_ab_exit hI hx (ofNat_zero' _) rfl htk fun _ _ h => h.2.1

end Path

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.dChkAW_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.dChkAW_sound

/-- info: 'Spike.Lib.X64.WakeWf.siAbW_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.siAbW_sound

/-- info: 'Spike.Lib.X64.WakeWf.blkW_dispAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_dispAb

/-- info: 'Spike.Lib.X64.WakeWf.blkW_dispAbI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_dispAbI

/-- info: 'Spike.Lib.X64.WakeWf.tj_keep5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.tj_keep5

/-- info: 'Spike.Lib.X64.WakeWf.t4_fall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.t4_fall

/-- info: 'Spike.Lib.X64.WakeWf.chAb_t4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.chAb_t4

/-- info: 'Spike.Lib.X64.WakeWf.tpathW_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.tpathW_ab
