/-
**The threads abort phase kept off its pcs** (AArch64): the checks that
decide `blkW_acStN`'s `htgt` (`Spike/Lib/A64AcSt.lean`) at
`ThreadsAb.Ac lab pfx` (`Spike/Lib/A64ThreadsAb.lean`) for a block none of
whose targets is a pc of the phase, and the phase's introduction at the
dispatcher's classes with a data condition.

- `blkAc`, `blkAc_sound`: every target of every instruction (a `ret`'s the
  return address `ra`) is off `acPcs lab pfx`, so every next state is out of
  `Ac` (whatever the state at the instruction).
- `blkAcX`, `blkAcX_sound`: as `blkAc`, a `bl` into the dispatcher's
  prologue (`tgtAc`) admitted when its return address is not `raT` (the other
  `scc_rt_abort` callers: `ac_dispE_of`, a state in `Ac` off `acPcsNE` has
  `x30 = raT`; `bl_x30`).
- `ThreadsAcSt.ac_dispE`, `ac_dispT` (and `ac_dispEA`, `ac_dispTA` from the
  abstract state, `sp_five`): introduction at the dispatcher's prologue
  (`x0 = 5`) and its first five tests (`[sp] = 5`), with `x30 = raT`.
- `ThreadsAcSt.d0_x30`, `t_run5`, `g5_x30`, `b0_x30`, `b1T_x30`, `b2_x30`:
  the path's blocks keep (`g5`: reload) `x30`.
- `ThreadsAcSt.memE5`, `memT5`, `memJ5`, `memG5`, `memB0T`, `memN1T`,
  `memB1T`, `memB2T`, `memSvcT`, `memExT`: the path's pcs are `Ac`'s classes.
-/
import Spike.Lib.A64SegInst
import Spike.Lib.A64AcSt
import Spike.Lib.A64ThreadsAb
import Spike.Lib.A64Abort

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)

/-- **A block's targets off the threads abort phase's pcs**: every target of
every instruction (a `ret`'s the return address `ra`) is off
`acPcs lab pfx`. -/
def blkAc (lab : Label → Int64) (pfx : String) (pc ra : Int64) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a).all fun t =>
          !(Spike.Lib.A64.ThreadsAb.acPcs lab pfx).contains t
      | none => false
    | none => false

/-- **`blkW_acStN`'s `htgt` at the threads abort phase from the check**,
every `ret` of the block returning to `ra` (`hret`). -/
theorem blkAc_sound {exe : _root_.Executable} {endPc : Int64} {R : Region} {n : ND} {blk : List Directive}
    {pfx : String} {ra : Int64} (h : blkAc (_root_.Executable.labels exe).label pfx n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed
        = ra) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (4 * k) →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s' := by
  intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' _
  refine Spike.Lib.A64.ThreadsAb.not_ac_of_pc ?_
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at this
  have ht := List.all_eq_true.mp this _ (aiTgt_mem a fun r hr => hret σ c hJ k hk r (hr ▸ ha))
  rw [hpc']
  simpa only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] using ht

/-- `Ac`'s pcs but the dispatcher's prologue. -/
def acPcsNE (lab : Label → Int64) (pfx : String) : List Int64 :=
  Spike.Lib.A64.ThreadsAb.pcRet lab pfx :: Spike.Lib.A64.ThreadsAb.pcSt lab pfx ::
    Spike.Lib.A64.ThreadsAb.tailPcs lab pfx ++ Spike.Lib.A64.ThreadsAb.failPcs lab pfx ++
    Spike.Lib.A64.ThreadsAb.dispTPcs lab ++ Spike.Lib.A64.ThreadsAb.g5Pcs lab ++
    Spike.Lib.A64.ThreadsAb.stubPcs lab

/-- **A state in `Ac` off `acPcsNE`** is at the dispatcher's prologue with
the threads return address. -/
theorem ac_dispE_of {lab : Label → Int64} {pfx : String} {s : State} (h : Spike.Lib.A64.ThreadsAb.Ac lab pfx s)
    (hn : s.st.2 ∉ acPcsNE lab pfx) :
    s.st.1.regs.X30.toBitVec = Spike.Lib.A64.ThreadsAb.raT lab pfx := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨-, -, hr⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  all_goals first | exact hr | (exfalso; apply hn; simp_all [acPcsNE])

/-- One target's check: off `Ac`'s pcs, or a `bl` to off `acPcsNE` whose
return address `fall` is not the threads one (another caller of the
dispatcher). -/
def tgtAc (lab : Label → Int64) (pfx : String) (fall : Int64) (a : AI) (t : Int64) : Bool :=
  !(Spike.Lib.A64.ThreadsAb.acPcs lab pfx).contains t ||
    (match a with | .bl _ => true | _ => false) && !(acPcsNE lab pfx).contains t &&
      fall.toBitVec != Spike.Lib.A64.ThreadsAb.raT lab pfx

/-- **A block's targets out of the threads abort phase**: every target of
every instruction (a `ret`'s the return address `ra`) passes `tgtAc`. -/
def blkAcX (lab : Label → Int64) (pfx : String) (pc ra : Int64) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a).all fun t =>
          tgtAc lab pfx (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) a t
      | none => false
    | none => false

/-- A `bl`'s `x30` is its return address. -/
theorem bl_x30 (o : SO) (f : Int64) (σ : AS) (L : Label) :
    (AI.step o f (.bl L) σ).regs.X30.toBitVec = f.toBitVec := by
  rw [BlockSpec.AI.step_bl']
  simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]

/-- **`blkW_acStN`'s `htgt` at the threads abort phase from `blkAcX`**,
every `ret` of the block returning to `ra` (`hret`). -/
theorem blkAcX_sound {exe : _root_.Executable} {endPc : Int64} {R : Region} {n : ND} {blk : List Directive}
    {pfx : String} {ra : Int64} (h : blkAcX (_root_.Executable.labels exe).label pfx n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed
        = ra) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (4 * k) →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Spike.Lib.A64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s' := by
  intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' hA' hac
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at this
  have ht := List.all_eq_true.mp this _ (aiTgt_mem a fun r hr => hret σ c hJ k hk r (hr ▸ ha))
  rw [← hpc'] at ht
  simp only [tgtAc, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, bne_iff_ne, ne_eq] at ht
  rcases ht with ht | ⟨⟨hbl, hne⟩, hra⟩
  · exact Spike.Lib.A64.ThreadsAb.not_ac_of_pc ht hac
  · have hx := ac_dispE_of hac hne
    cases a <;> simp at hbl
    rw [hA'.regs, bl_x30] at hx
    exact hra hx

namespace ThreadsAcSt

open Spike.Lib.A64
open Spike.Lib.A64.ThreadsAb
open Spike.Lib.A64.WriteAb (spLoad dispEPcs)

variable {lab : Label → Int64} {pfx : String}

/-- The dispatcher's prologue with `x0 = 5` and the threads return address
is in `Ac`. -/
theorem ac_dispE {s : State} (h : s.st.2 ∈ dispEPcs lab) (h0 : s.st.1.regs.X0 = 5)
    (hr : s.st.1.regs.X30.toBitVec = raT lab pfx) : Ac lab pfx s :=
  .inr (.inr (.inr (.inr (.inl ⟨h, h0, hr⟩))))

/-- The dispatcher's first five tests with `[sp] = 5` and the threads return
address are in `Ac`. -/
theorem ac_dispT {s : State} (h : s.st.2 ∈ dispTPcs lab) (h0 : spLoad s 0 = some 5#64)
    (hr : s.st.1.regs.X30.toBitVec = raT lab pfx) : Ac lab pfx s :=
  .inr (.inr (.inr (.inr (.inr (.inl ⟨h, h0, hr⟩)))))

/-! ### The path's states in the phase, from the abstract state -/

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over the dispatcher's and the stub's blocks
(`Spike/Lib/A64StubWA.lean`'s). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Flow.arun, Flow.dstep, Flow.classify, Flow.RegOnly, Flow.AI.so, Flow.AI.step, Flow.AI.tgt,
    Flow.soReg, Flow.regDst, Flow.zrB, Flow.regRes, Operation.interp, MachineData.setRegOrZr,
    MachineData.setRegOrSp, Reg64s.setRegOrZr, Reg64s.getRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64,
    Reg64s.setRegOrSp, Reg64s.getRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64, Reg64s.setXReg,
    Reg64s.getXReg, ShiftRegExpr.interp, ExtOrImmReg.interp, ConstExpr.interp, RegOrZr.base, RegOrSp.base,
    Flow.SO.get, Flow.SO.set, Flow.SO.kill, Flow.SO.write, Flow.SO.killZ, Spike.Lib.lk, Spike.Lib.rm])

/-- The dispatcher's prologue keeps `x30` before each instruction. -/
theorem d0_x30 (pc : Int64) (σ : Flow.AS) {k : Nat} (hk : k < Abort.Disp.d0.length) :
    (Flow.arun lab (Abort.Disp.d0.take k) ⟨pc, Abort.oE, σ⟩).σ.regs.X30 = σ.regs.X30 := by
  simp only [Abort.Disp.d0] at hk ⊢
  simp only [List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- A test of the dispatcher (the fifth included) keeps the frame's offset,
its slots and `x30` before each instruction. -/
theorem t_run5 {blk : List Directive}
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4 ∨
      blk = Abort.Disp.t5)
    (pc : Int64) (σ : Flow.AS) {k : Nat} (hk : k < blk.length) :
    (Flow.arun lab (blk.take k) ⟨pc, Abort.Disp.oD, σ⟩).so.sp = -32 ∧
      (Flow.arun lab (blk.take k) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot = σ.slot ∧
      (Flow.arun lab (blk.take k) ⟨pc, Abort.Disp.oD, σ⟩).σ.regs.X30 = σ.regs.X30 := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4, Abort.Disp.t5] at hk ⊢ <;>
    simp only [List.length_cons, List.length_nil] at hk <;>
    rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- The jump to the threads stub has `x30 = ra` before each instruction:
kept, then reloaded from `slot (-8)`. -/
theorem g5_x30 (pc : Int64) (σ : Flow.AS) {ra : BitVec 64} (h8 : σ.slot (-8) = ra)
    (hr : σ.regs.X30.toBitVec = ra) {k : Nat} (hk : k < Abort.Disp.g5.length) :
    (Flow.arun lab (Abort.Disp.g5.take k) ⟨pc, Abort.Disp.oD, σ⟩).σ.regs.X30.toBitVec = ra := by
  simp only [Abort.Disp.g5] at hk ⊢
  simp only [List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> arun_simp <;> simp_all

/-- The stub's prologue keeps `x30` before each instruction. -/
theorem b0_x30 (pc : Int64) (σ : Flow.AS) {k : Nat} (hk : k < Abort.b0.length) :
    (Flow.arun lab (Abort.b0.take k) ⟨pc, Abort.oE, σ⟩).σ.regs.X30 = σ.regs.X30 := by
  simp only [Abort.b0] at hk ⊢
  simp only [List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> arun_simp

/-- The threads stub's argument block keeps `x30` before each instruction. -/
theorem b1T_x30 (pc : Int64) (σ : Flow.AS) {k : Nat} (hk : k < Abort.b1Threads.length) :
    (Flow.arun lab (Abort.b1Threads.take k) ⟨pc, Abort.oI, σ⟩).σ.regs.X30 = σ.regs.X30 := by
  simp only [Abort.b1Threads] at hk ⊢
  simp only [List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- The stub's block after the call keeps `x30` before each instruction. -/
theorem b2_x30 (pc : Int64) (σ : Flow.AS) {k : Nat} (hk : k < Abort.b2.length) :
    (Flow.arun lab (Abort.b2.take k) ⟨pc, Abort.oI, σ⟩).σ.regs.X30 = σ.regs.X30 := by
  simp only [Abort.b2] at hk ⊢
  simp only [List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|k <;> (try omega) <;> arun_simp

/-- The word at `[sp]` from the abstract state, `sp` at the frame's `-32`. -/
theorem sp_five {R : Spike.Lib.Region} {o : Flow.SO} {s : State} {σ : Flow.AS} (hA : Flow.Abs R o s.st.1 σ)
    (ho : o.sp = -32) (hoff : R.Off (-32)) (h5 : (σ.slot (-32)).toNat = 5) : spLoad s 0 = some 5#64 := by
  obtain ⟨j, hj, hjv⟩ := hA.slot (-32) hoff
  have hsp := hA.so .SP o.sp rfl
  rw [← hA.regs, ho] at hsp
  simp only [Reg64s.getRegOrSp64] at hsp
  simp only [spLoad, Scc.Sem.A64.privLoad, hsp]
  rw [show R.addr (-32) + 0 = R.addr (-32) from BitVec.add_zero _, hj, Option.map_some, hjv]
  exact congrArg some (BitVec.eq_of_toNat_eq (by simpa using h5))

/-- A state of the dispatcher's prologue with `x0 = 5` and the threads
return address, from the abstract state. -/
theorem ac_dispEA {R : Spike.Lib.Region} {o : Flow.SO} {s : State} {σ : Flow.AS} (hmem : s.st.2 ∈ dispEPcs lab)
    (hA : Flow.Abs R o s.st.1 σ) (h5 : σ.regs.X0.toBitVec.toNat = 5) (hr : σ.regs.X30.toBitVec = raT lab pfx) :
    Ac lab pfx s :=
  ac_dispE hmem (by rw [hA.regs]; exact UInt64.toNat_inj.mp (by simpa using h5)) (by rw [hA.regs]; exact hr)

/-- A state of the dispatcher's tests with `5` at `[sp]` and the threads
return address, from the abstract state. -/
theorem ac_dispTA {R : Spike.Lib.Region} {o : Flow.SO} {s : State} {σ : Flow.AS} (hmem : s.st.2 ∈ dispTPcs lab)
    (hA : Flow.Abs R o s.st.1 σ) (ho : o.sp = -32) (hoff : R.Off (-32)) (h5 : (σ.slot (-32)).toNat = 5)
    (hr : σ.regs.X30.toBitVec = raT lab pfx) : Ac lab pfx s :=
  ac_dispT hmem (sp_five hA ho hoff h5) (by rw [hA.regs]; exact hr)

/-- The prologue's pcs are `dispEPcs`. -/
theorem memE5 {k : Nat} (hk : k < Abort.Disp.d0.length) :
    lab "scc_rt_abort" + Int64.ofNat (4 * k) ∈ dispEPcs lab := by
  simp only [Abort.Disp.d0, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> simp [dispEPcs]

/-- The five tests' pcs are `dispTPcs`. -/
theorem memT5 {l : Label} {blk : List Directive}
    (hl : l = ".L12_scc_rt_abort.0_entry" ∨ l = ".L12_scc_rt_abort.2_next1" ∨ l = ".L12_scc_rt_abort.4_next3" ∨
      l = ".L12_scc_rt_abort.6_next5" ∨ l = ".L12_scc_rt_abort.8_next7")
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4 ∨
      blk = Abort.Disp.t5)
    {k : Nat} (hk : k < blk.length) : lab l + Int64.ofNat (4 * k) ∈ dispTPcs lab := by
  have hk4 : k < 4 := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      simpa only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4, Abort.Disp.t5, List.length_cons,
        List.length_nil] using hk
  rcases hl with rfl | rfl | rfl | rfl | rfl <;> rcases k with _|_|_|_|k <;> (try omega) <;>
    simp [dispTPcs]

/-- The four jumps to the next test are `dispTPcs`. -/
theorem memJ5 {l : Label}
    (hl : l = ".L12_scc_rt_abort.0_entry" ∨ l = ".L12_scc_rt_abort.2_next1" ∨ l = ".L12_scc_rt_abort.4_next3" ∨
      l = ".L12_scc_rt_abort.6_next5")
    {k : Nat} (hk : k < 1) : lab l + 4 + 4 + 4 + 4 + Int64.ofNat (4 * k) ∈ dispTPcs lab := by
  rcases hl with rfl | rfl | rfl | rfl <;> rcases k with _|k <;> (try omega) <;>
    simp [dispTPcs, Int64.add_assoc]

/-- The jump to the threads stub's pcs are `g5Pcs`. -/
theorem memG5 {k : Nat} (hk : k < Abort.Disp.g5.length) :
    lab ".L12_scc_rt_abort.9_is8" + Int64.ofNat (4 * k) ∈ g5Pcs lab := by
  simp only [Abort.Disp.g5, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> simp [g5Pcs]

/-- The threads stub's prologue is in `stubPcs`. -/
theorem memB0T {k : Nat} (hk : k < Abort.b0.length) :
    lab Abort.threads.fn + Int64.ofNat (4 * k) ∈ stubPcs lab := by
  simp only [Abort.b0, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> simp [stubPcs]

/-- The threads stub's message address is in `stubPcs`. -/
theorem memN1T : lab Abort.threads.entry ∈ stubPcs lab ∧ lab Abort.threads.entry + 4 ∈ stubPcs lab := by
  simp [stubPcs]

/-- The threads stub's argument block is in `stubPcs`. -/
theorem memB1T {k : Nat} (hk : k < Abort.b1Threads.length) :
    lab Abort.threads.entry + 4 + 4 + Int64.ofNat (4 * k) ∈ stubPcs lab := by
  simp only [Abort.b1Threads, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> simp [stubPcs, Int64.add_assoc]

/-- The threads stub's block after the call is in `stubPcs`. -/
theorem memB2T {k : Nat} (hk : k < Abort.b2.length) :
    Abort.pcSvc lab Abort.threads + 4 + Int64.ofNat (4 * k) ∈ stubPcs lab := by
  simp only [Abort.b2, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|k <;> (try omega) <;> simp [stubPcs, Int64.add_assoc]

/-- The threads stub's system call is in `stubPcs`. -/
theorem memSvcT : Abort.pcSvc lab Abort.threads ∈ stubPcs lab := by
  simp [stubPcs, Int64.add_assoc]

/-- The threads stub's exit call is in `stubPcs`. -/
theorem memExT : lab Abort.threads.exit ∈ stubPcs lab := by
  simp [stubPcs]

end ThreadsAcSt

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64ConsumerA.blkAc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkAc_sound

/-- info: 'Spike.Lib.A64ConsumerA.blkAcX_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkAcX_sound

/-- info: 'Spike.Lib.A64ConsumerA.ThreadsAcSt.g5_x30' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ThreadsAcSt.g5_x30

/-- info: 'Spike.Lib.A64ConsumerA.ThreadsAcSt.t_run5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ThreadsAcSt.t_run5

end Spike.Lib.A64ConsumerA
