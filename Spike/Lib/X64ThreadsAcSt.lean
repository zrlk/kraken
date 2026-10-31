/-
**The threads abort phase kept off its pcs** (x86-64): the checks that
decide `blkW_acStN`'s `htgt` (`Spike/Lib/X64AcSt.lean`) at
`ThreadsAb.Ac lab pfx` (`Spike/Lib/X64ThreadsAb.lean`) for a block none of
whose targets is a pc of the phase, and the phase's introduction at the
dispatcher's classes with a data condition. The x86-64 twin of
`Spike/Lib/A64ThreadsAcSt.lean`.

- `blkAc`, `blkAc_sound`: every target of every instruction (a `ret`'s the
  return address `ra`) is off `acPcs lab pfx`, so every next state is out of
  `Ac` (whatever the state at the instruction).
- `ThreadsAcSt.ac_dispE`, `ac_dispT` (and `ac_dispEA`, `ac_dispTA` from the
  abstract state, `bp_five`): introduction at the dispatcher's prologue
  (`%rdi = 5`) and its first five tests (`-8(%rbp) = 5`), with the return
  address `raT`.
- `ThreadsAcSt.RaPos`, `raW_of_abs`: the return address from the abstract
  state's `slot 8` (`Abort.Disp.DN.nd5 … ra`, `Abort.NT … ra`), the static
  offsets placing `%rsp` or `%rbp` as `RaW` reads it at the pc.
- `ThreadsAcSt.d0_run5`, `t_run5`, `g5_run`, `x0_run5`: the path's blocks
  keep `slot 8` (and the prologue `%rdi`), each pc's offsets at `RaPos`.
- `ThreadsAcSt.memE5`, `memT5`, `memJ5`, `memG5`, `memX0T`, `memN1T`,
  `memX1T`, `memX2T`, `memSysT`, `memExT`: the path's pcs are `Ac`'s classes.

**Deviations from the A64 file.** The return address is the pushed word, not
`x30` (`Spike/Lib/X64ThreadsAb.lean`'s `RaW`): the A64 `d0_x30`, `t_run5`'s
`x30` conjunct, `g5_x30`, `b0_x30`, `b1T_x30`, `b2_x30` become `slot 8` kept
plus the offsets' position (`RaPos`), and `ac_dispEA`/`ac_dispTA` take
`σ.slot 8 = raT`, `R.Off 8` and `RaPos` for the A64 `x30 = raT`. The x86-64
dispatcher stores its code at `-8(%rbp)` (A64 `[sp]`, `sp_five` → `bp_five`).
`blkAcX`, `blkAcX_sound`, `tgtAc`, `acPcsNE`, `ac_dispE_of`, `bl_x30` are not
twinned: they have no users outside the A64 file. The stub's `n1b`
(A64's second `adrp`/`add` half) has no x86-64 node: `n1` is one `leaq`.
-/
import Spike.Lib.X64SegInst
import Spike.Lib.X64AcSt
import Spike.Lib.X64ThreadsAb
import Spike.Lib.X64Abort

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64

/-- **A block's targets off the threads abort phase's pcs**: every target of
every instruction (a `ret`'s the return address `ra`) is off
`acPcs lab pfx`. -/
def blkAc (lab : Label → Int64) (pfx : String) (pc ra : Int64) (blk : List (Directive × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some dz => match classify dz.1 with
      | some a => (aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) ra a).all fun t =>
          !(Spike.Lib.X64.ThreadsAb.acPcs lab pfx).contains t
      | none => false
    | none => false

/-- **`blkW_acStN`'s `htgt` at the threads abort phase from the check**,
every `ret` of the block returning to `ra` (`hret`). -/
theorem blkAc_sound {exe : _root_.Executable} {endPc : Int64} {R : Region} {n : ND}
    {blk : List (Directive × Nat)} {pfx : String} {ra : Int64}
    (h : blkAc (_root_.Executable.labels exe).label pfx n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp) = ra) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k].1 = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (cellOff blk k) →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Spike.Lib.X64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Spike.Lib.X64.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s' := by
  intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' _
  refine Spike.Lib.X64.ThreadsAb.not_ac_of_pc ?_
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at this
  have ht := List.all_eq_true.mp this _ (aiTgt_mem a fun hr => hret σ c hJ k hk (hr ▸ ha))
  rw [hpc']
  simpa only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] using ht

namespace ThreadsAcSt

open Spike.Lib.X64.ThreadsAb
open Spike.Lib.X64.WriteAb (bpLoad dispEPcs)

variable {lab : Label → Int64} {pfx : String}

/-- The dispatcher's prologue with `%rdi = 5` and the threads return address
is in `Ac`. -/
theorem ac_dispE {s : State} (h : s.st.2 ∈ dispEPcs lab) (h0 : s.st.1.regs.get64 .rdi = 5#64)
    (hr : RaW lab s (raT lab pfx)) : Ac lab pfx s :=
  .inr (.inr (.inr (.inr (.inl ⟨h, h0, hr⟩))))

/-- The dispatcher's first five tests with `-8(%rbp) = 5` and the threads
return address are in `Ac`. -/
theorem ac_dispT {s : State} (h : s.st.2 ∈ dispTPcs lab) (h0 : bpLoad s (-8) = some 5#64)
    (hr : RaW lab s (raT lab pfx)) : Ac lab pfx s :=
  .inr (.inr (.inr (.inr (.inr (.inl ⟨h, h0, hr⟩)))))

/-! ### The return address from the abstract state -/

/-- **The offsets at a pc place the return address where `RaW` reads it**:
`%rsp` at the frame's `8` at `raSPcs`, at `0` at `raPPcs`, `%rbp` at the
frame's base at `raBPcs`. -/
def RaPos (lab : Label → Int64) (pc : Int64) (o : SO) : Prop :=
  (pc ∈ raSPcs lab ∧ o.sp = 8) ∨ (pc ∈ raPPcs lab ∧ o.sp = 0) ∨ (pc ∈ raBPcs lab ∧ o.get .rbp = some 0)

/-- The word at the frame's offset `k` of the region from the abstract
state, a register at the region's address of `k - d`. -/
theorem load_of_abs {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ)
    {r : Reg64} {k d : Int} (hr : o.get r = some (k - d)) (hoff : R.Off k) :
    privLoad s ((s.st.1.regs.get64 r) + BitVec.ofInt 64 d) = some (σ.slot k) := by
  obtain ⟨j, hj, hjv⟩ := hA.slot k hoff
  have hreg := hA.so r (k - d) hr
  rw [← hA.regs] at hreg
  simp only [Scc.Sem.X64.privLoad, hreg]
  rw [← Spike.Lib.Region.addr_add, Int.sub_add_cancel, hj, Option.map_some, hjv]

/-- **The return address from the abstract state**: `slot 8 = ra` at
offsets in `RaPos`. -/
theorem raW_of_abs {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} {ra : BitVec 64}
    (hA : Abs R o s.st.1 σ) (hoff : R.Off 8) (hpos : RaPos lab s.st.2 o) (h8 : σ.slot 8 = ra) :
    RaW lab s ra := by
  rcases hpos with ⟨hp, ho⟩ | ⟨hp, ho⟩ | ⟨hp, ho⟩
  · refine .inl ⟨hp, ?_⟩
    have := load_of_abs hA (r := .rsp) (d := 0) (by simp [SO.get, ho]) hoff
    rw [← h8, ← this]; rfl
  · refine .inr (.inl ⟨hp, ?_⟩)
    have := load_of_abs hA (r := .rsp) (d := 8) (by simp [SO.get, ho]) hoff
    rw [← h8, ← this]; rfl
  · refine .inr (.inr ⟨hp, ?_⟩)
    have := load_of_abs hA (r := .rbp) (d := 8) (by simpa using ho) hoff
    rw [← h8, ← this]; rfl

/-- The word at `-8(%rbp)` from the abstract state, `%rbp` at the frame's
base. -/
theorem bp_five {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ)
    (ho : o.get .rbp = some 0) (hoff : R.Off (-8)) (h5 : σ.slot (-8) = 5#64) :
    bpLoad s (-8) = some 5#64 := by
  have := load_of_abs hA (r := .rbp) (k := -8) (d := -8) (by simpa using ho) hoff
  rw [← h5, ← this]; rfl

/-- A state of the dispatcher's prologue with `%rdi = 5` and the threads
return address, from the abstract state. -/
theorem ac_dispEA {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hmem : s.st.2 ∈ dispEPcs lab)
    (hA : Abs R o s.st.1 σ) (h5 : σ.regs.get64 .rdi = 5#64) (hoff : R.Off 8) (hpos : RaPos lab s.st.2 o)
    (hr : σ.slot 8 = raT lab pfx) : Ac lab pfx s :=
  ac_dispE hmem (by rw [hA.regs]; exact h5) (raW_of_abs hA hoff hpos hr)

/-- A state of the dispatcher's tests with `5` at `-8(%rbp)` and the threads
return address, from the abstract state. -/
theorem ac_dispTA {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hmem : s.st.2 ∈ dispTPcs lab)
    (hA : Abs R o s.st.1 σ) (ho : o.get .rbp = some 0) (hoff : R.Off (-8)) (h5 : σ.slot (-8) = 5#64)
    (hoff8 : R.Off 8) (hr : σ.slot 8 = raT lab pfx) : Ac lab pfx s :=
  ac_dispT hmem (bp_five hA ho hoff h5) (raW_of_abs hA hoff8 (.inr (.inr ⟨dispT_ra hmem, ho⟩)) hr)

/-! ### The path's blocks keep the return address -/

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over the dispatcher's and the stub's blocks
(`Spike/Lib/X64StubWA.lean`'s). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [arun, dstep, Spike.Lib.X64.classify, RegOnly, AI.so, soReg, regDst, regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply, Reg64s.get_low64, BlockSpec.AI.step_ld', BlockSpec.AI.step_st',
    BlockSpec.AI.step_push', BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', BlockSpec.AI.step_jmp',
    BlockSpec.AI.step_jcc'])

/-- The dispatcher's prologue keeps `%rdi` and `slot 8` before each
instruction, its offsets at `RaPos`. -/
theorem d0_run5 (pc : Int64) (σ : AS) {k : Nat} (hk : k < Abort.Disp.d0.length) :
    (arun lab (Abort.Disp.d0.take k) ⟨pc, Abort.oE, σ⟩).σ.regs.get64 .rdi = σ.regs.get64 .rdi ∧
      (arun lab (Abort.Disp.d0.take k) ⟨pc, Abort.oE, σ⟩).σ.slot 8 = σ.slot 8 ∧
      RaPos lab (lab "scc_rt_abort" + Int64.ofNat (cellOff Abort.Disp.d0 k))
        (arun lab (Abort.Disp.d0.take k) ⟨pc, Abort.oE, σ⟩).so := by
  simp only [Abort.Disp.d0] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> arun_simp <;>
    simp [RaPos, raSPcs, raPPcs, raBPcs, SO.get, Spike.Lib.lk, Abort.Disp.oD, cellOff]

/-- A test of the dispatcher (the fifth included) keeps `%rbp` at the
frame's base and the slots before each instruction. -/
theorem t_run5 {blk : List (Directive × Nat)}
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4 ∨
      blk = Abort.Disp.t5)
    (pc : Int64) (σ : AS) {k : Nat} (hk : k < blk.length) :
    (arun lab (blk.take k) ⟨pc, Abort.Disp.oD, σ⟩).so.get .rbp = some 0 ∧
      (arun lab (blk.take k) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot = σ.slot := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4, Abort.Disp.t5] at hk ⊢ <;>
    simp only [List.length_zip, List.length_cons, List.length_nil] at hk <;>
    rcases k with _|_|_|_|k <;> (try omega) <;> arun_simp

/-- The jump to the threads stub keeps `slot 8` before each instruction, its
offsets at `RaPos`. -/
theorem g5_run (pc : Int64) (σ : AS) {k : Nat} (hk : k < Abort.Disp.g5.length) :
    (arun lab (Abort.Disp.g5.take k) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot 8 = σ.slot 8 ∧
      RaPos lab (lab ".Lscc_rt_abort.is8" + Int64.ofNat (cellOff Abort.Disp.g5 k))
        (arun lab (Abort.Disp.g5.take k) ⟨pc, Abort.Disp.oD, σ⟩).so := by
  simp only [Abort.Disp.g5] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|k <;> (try omega) <;> arun_simp <;>
    simp [RaPos, raSPcs, raPPcs, raBPcs, SO.get, Spike.Lib.lk, Abort.Disp.oD, dispTPcs, cellOff]

/-- The threads stub's prologue keeps `slot 8` before each instruction, its
offsets at `RaPos`. -/
theorem x0_run5 (pc : Int64) (σ : AS) {k : Nat} (hk : k < Abort.x0.length) :
    (arun lab (Abort.x0.take k) ⟨pc, Abort.oE, σ⟩).σ.slot 8 = σ.slot 8 ∧
      RaPos lab (lab Abort.threads.fn + Int64.ofNat (cellOff Abort.x0 k))
        (arun lab (Abort.x0.take k) ⟨pc, Abort.oE, σ⟩).so := by
  simp only [Abort.x0] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|k <;> (try omega) <;> arun_simp <;>
    simp [RaPos, raSPcs, raPPcs, raBPcs, SO.get, Spike.Lib.lk, Abort.Disp.oD, stubPcs, cellOff]

/-- The threads stub's argument block keeps `%rbp` at the frame's base and
`slot 8` before each instruction. -/
theorem x1T_run (pc : Int64) (σ : AS) {k : Nat} (hk : k < Abort.x1Threads.length) :
    (arun lab (Abort.x1Threads.take k) ⟨pc, Abort.oI, σ⟩).so.get .rbp = some 0 ∧
      (arun lab (Abort.x1Threads.take k) ⟨pc, Abort.oI, σ⟩).σ.slot 8 = σ.slot 8 := by
  simp only [Abort.x1Threads] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- The stub's block after the call keeps `%rbp` at the frame's base and
`slot 8` before each instruction. -/
theorem x2_run5 (pc : Int64) (σ : AS) {k : Nat} (hk : k < Abort.x2.length) :
    (arun lab (Abort.x2.take k) ⟨pc, Abort.oI, σ⟩).so.get .rbp = some 0 ∧
      (arun lab (Abort.x2.take k) ⟨pc, Abort.oI, σ⟩).σ.slot 8 = σ.slot 8 := by
  simp only [Abort.x2] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|k <;> (try omega) <;> arun_simp

/-! ### The path's pcs are `Ac`'s classes -/

/-- The prologue's pcs are `dispEPcs`. -/
theorem memE5 {k : Nat} (hk : k < Abort.Disp.d0.length) :
    lab "scc_rt_abort" + Int64.ofNat (cellOff Abort.Disp.d0 k) ∈ dispEPcs lab := by
  simp only [Abort.Disp.d0, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|_|k <;> (try omega) <;> simp [dispEPcs, cellOff] <;> decide

/-- The five tests' pcs are `dispTPcs`. -/
theorem memT5 {l : Label} {blk : List (Directive × Nat)}
    (hl : l = ".Lscc_rt_abort.entry" ∨ l = ".Lscc_rt_abort.next1" ∨ l = ".Lscc_rt_abort.next3" ∨
      l = ".Lscc_rt_abort.next5" ∨ l = ".Lscc_rt_abort.next7")
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4 ∨
      blk = Abort.Disp.t5)
    {k : Nat} (hk : k < blk.length) : lab l + Int64.ofNat (cellOff blk k) ∈ dispTPcs lab := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4, Abort.Disp.t5, List.length_zip,
      List.length_cons, List.length_nil] at hk ⊢ <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl <;> rcases k with _|_|_|_|k <;> (try omega) <;>
    simp [dispTPcs, cellOff] <;> decide

/-- The four jumps to the next test are `dispTPcs`. -/
theorem memJ5 {l : Label} {blk : List (Directive × Nat)}
    (hl : l = ".Lscc_rt_abort.entry" ∨ l = ".Lscc_rt_abort.next1" ∨ l = ".Lscc_rt_abort.next3" ∨
      l = ".Lscc_rt_abort.next5")
    (hb : blk = Abort.Disp.j1 ∨ blk = Abort.Disp.j2 ∨ blk = Abort.Disp.j3 ∨ blk = Abort.Disp.j4)
    {k : Nat} (hk : k < blk.length) : lab l + 16 + Int64.ofNat (cellOff blk k) ∈ dispTPcs lab := by
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [Abort.Disp.j1, Abort.Disp.j2, Abort.Disp.j3, Abort.Disp.j4, List.length_zip, List.length_cons,
      List.length_nil] at hk ⊢ <;>
    rcases hl with rfl | rfl | rfl | rfl <;> rcases k with _|k <;> (try omega) <;>
    simp [dispTPcs, cellOff] <;> decide

/-- The jump to the threads stub's pcs are `g5Pcs`. -/
theorem memG5 {k : Nat} (hk : k < Abort.Disp.g5.length) :
    lab ".Lscc_rt_abort.is8" + Int64.ofNat (cellOff Abort.Disp.g5 k) ∈ g5Pcs lab := by
  simp only [Abort.Disp.g5, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|k <;> (try omega) <;> simp [g5Pcs, cellOff] <;> decide

/-- The threads stub's prologue is in `stubPcs`. -/
theorem memX0T {k : Nat} (hk : k < Abort.x0.length) :
    lab Abort.threads.fn + Int64.ofNat (cellOff Abort.x0 k) ∈ stubPcs lab := by
  simp only [Abort.x0, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|k <;> (try omega) <;> simp [stubPcs, cellOff] <;> decide

/-- The threads stub's message address is in `stubPcs` and `raBPcs`. -/
theorem memN1T : lab Abort.threads.entry ∈ stubPcs lab ∧ lab Abort.threads.entry ∈ raBPcs lab := by
  simp [stubPcs, raBPcs]

/-- The threads stub's argument block is in `stubPcs` and `raBPcs`. -/
theorem memX1T {k : Nat} (hk : k < Abort.x1Threads.length) :
    lab Abort.threads.entry + 7 + Int64.ofNat (cellOff Abort.x1Threads k) ∈ stubPcs lab ∧
      lab Abort.threads.entry + 7 + Int64.ofNat (cellOff Abort.x1Threads k) ∈ raBPcs lab := by
  simp only [Abort.x1Threads, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|_|_|k <;> (try omega) <;> simp [stubPcs, raBPcs, cellOff, Int64.add_assoc] <;> decide

/-- The threads stub's block after the call is in `stubPcs` and `raBPcs`. -/
theorem memX2T {k : Nat} (hk : k < Abort.x2.length) :
    lab Abort.threads.entry + 36 + Int64.ofNat (cellOff Abort.x2 k) ∈ stubPcs lab ∧
      lab Abort.threads.entry + 36 + Int64.ofNat (cellOff Abort.x2 k) ∈ raBPcs lab := by
  simp only [Abort.x2, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|k <;> (try omega) <;> simp [stubPcs, raBPcs, cellOff, Int64.add_assoc] <;> decide

/-- The threads stub's system call is in `stubPcs` and `raBPcs`. -/
theorem memSysT : Abort.pcSys lab Abort.threads ∈ stubPcs lab ∧ Abort.pcSys lab Abort.threads ∈ raBPcs lab := by
  simp [stubPcs, raBPcs, Abort.pcSys]

/-- The threads stub's exit call is in `stubPcs` and `raBPcs`. -/
theorem memExT : lab Abort.threads.exit ∈ stubPcs lab ∧ lab Abort.threads.exit ∈ raBPcs lab := by
  simp [stubPcs, raBPcs]

end ThreadsAcSt

end Spike.Lib.X64ConsumerA

/-- info: 'Spike.Lib.X64ConsumerA.blkAc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.blkAc_sound

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.ac_dispE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.ac_dispE

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.ac_dispT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.ac_dispT

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.load_of_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.load_of_abs

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.raW_of_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.raW_of_abs

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.bp_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.bp_five

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.ac_dispEA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.ac_dispEA

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.ac_dispTA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.ac_dispTA

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.d0_run5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.d0_run5

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.t_run5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.t_run5

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.g5_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.g5_run

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.x0_run5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.x0_run5

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.x1T_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.x1T_run

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.x2_run5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.x2_run5

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memE5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memE5

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memT5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memT5

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memJ5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memJ5

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memG5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memG5

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memX0T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memX0T

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memN1T' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memN1T

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memX1T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memX1T

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memX2T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memX2T

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memSysT' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memSysT

/-- info: 'Spike.Lib.X64ConsumerA.ThreadsAcSt.memExT' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ThreadsAcSt.memExT
