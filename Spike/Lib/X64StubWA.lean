/-
**The write abort path's obligations inside `SFactsA`** (x86-64): the
`Abort.Disp.StubWW` of a jump to `scc_rt_abort` with `%rdi = 4`
(`Spike/Lib/X64AbortWriteW.lean`) at `W := SFactsA … frs Dt (WriteAb.Ab lab)`
with the write abort phase (`Spike/Lib/X64WriteAb.lean`), for any program
with the abort code (`Scc.Cert.Rt.X64.Abort.abortIn`), an instance's facts at
the frames `frs` (`InstOk` at `own · frs`, `Spike/Lib/Rt/X64RtW.lean`) and the
path's phase check (`abortPhWriteOk`, `Spike/Lib/X64AbortPhW.lean`). The twin
of `Spike/Lib/A64StubWA.lean`.

The source control `c0` is `print`'s jump to the abort after its refused
`write`: unlike the heap path's allocation it is not stuck, so the facts the
path needs at every frame run from it are given (`RefCtl`).

* `RefCtl`: the facts of `c0` the path needs (not a `ret` at the outermost
  frame, its loads and stores one cell, placed at every memory of the frame
  condition, frame runs from and into it keeping the owned words, its
  allocations passing the zero check);
* `sfactsA_doneW`, `sfactsA_sysW`: `SFactsA` in the phase `Ab` at an
  instruction without an event off the sites, and at a `syscall` with the
  abort facts and the write tail given;
* `ab_dispE`, `ab_dispT`, `d0_rdi`, `t_run` and the `mem*` lemmas: the
  path's states in `WriteAb.Ab`;
* `blkW_writeA`, `nodeW_si_writeA`: a block and a single instruction of the
  path (as `blkW_heapA`, `nodeW_si_heapA`, `Spike/Lib/X64StubHA.lean`), each
  state in the phase (`hAb`);
* `stubWW_sfactsA`: `StubWW` inside `SFactsA … frs Dt (WriteAb.Ab lab)`, the
  write tail `Dt` holding at the stub's `write` (`hwr`), the exit call the
  write abort site.

**Unlike AArch64**: instructions have sizes (a block's pcs are its label's
plus `cellOff`); `ownSys` also covers `arch_prctl`'s resumed state; the
dispatcher's code is at `-8(%rbp)`; the stub's region is `[-24, 16)` from its
frame base.
-/
import Spike.Lib.X64AbortPhW
import Spike.Lib.X64AbortStubCode
import Spike.Lib.X64SegInstA
import Spike.Lib.X64WriteAb

namespace Spike.Lib.X64.StubW

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
open Scc.Cert.Rt.X64 (blockAtB code_field)
open Kraken.Promising.Lower.X64 (op64)

/-! ## The control at the jump to the abort -/

/-- **The facts of the source control of the write abort path** at the
frames `frs`: not a `ret` at the outermost frame, every load and store of a
frame run from it one cell, placed at every memory of the frame condition
`F` (`PlacedSE`: a model term of an extern needs only its frames placed),
every frame run from or into it keeping the owned words, every allocation
of a frame run from it passing the zero check. -/
structure RefCtl (Λ : Scc.Sem.Layout) (p : Prog) (own : OwnS) (lbl : Lbl) (F : MachineData → Prop) (c0 : Ctl)
    (frs : List TermRun.Frame) : Prop where
  noRet : frs = [] → ∀ a, c0.term ≠ .ret a
  cell : ∀ c' fs', FrameRun p (c0, frs) (c', fs') → ∀ x a e ty w,
    (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty
  place : ∀ s : State, F s.st.1 → Spike.Lib.X64ConsumerS.PlacedSE Λ lbl s c0 frs
  runOut : ∀ (s : State) c' fs', FrameRun p (c0, frs) (c', fs') → own s fs' = own s frs
  runIn : ∀ (s : State) c₁ fs₁, FrameRun p (c₁, fs₁) (c0, frs) → own s frs = own s fs₁
  zero : ∀ c' fs', FrameRun p (c0, frs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
    ZeroOkTy τ = true

/-! ## `SFactsA` at one state in the phase -/

section State

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS} {lbl : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} {Dt : State → Prop} {F : MachineData → Prop}
  {Ab : State → Prop}

open Kraken.Promising.Lower.X64 (CellAt after)

/-- **`SFactsA` in the phase at an instruction without an event** (not a
`syscall`, its step `.done s'`), off the marks' sites, at a control with
`RefCtl`'s facts: the leaf owns what `s` owns and is in the take phase iff
`s` is; in that phase the range is owned. -/
theorem sfactsA_doneW {s' : State} {d : Directive} {sz : Nat} (hc : RefCtl Λ p own lbl F c fs)
    (hpl : Spike.Lib.X64ConsumerS.PlacedSE Λ lbl s c fs) (hP : PcOff μ s)
    (hcl : CellAt s d sz) (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) (hex : isa.exec s = some (.done s'))
    (hown : own s' fs = own s fs) (htk : Tk s' ↔ Tk s) (hO : Tk s → Owned Λ rS s) (hAb : Ab s) :
    SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt Ab := by
  have hs : abi.atSys s = false := atSyscall_false_of_cellAt hcl hd
  refine
    { noRet := hc.noRet
      cell := hc.cell
      noSite := hP.noSite
      mapped := fun _ e he => by rw [hex] at he; cases he; nofun
      place := hpl
      svc := fun h => by rw [hs] at h; cases h
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.runOut s c₂ fs₂ hr
        · exact hc.runIn s c₁ fs₁ hr
      ownInstr := fun c' fs' hr _ tree he => by
        rw [hex] at he; cases he
        refine .inl ⟨?_, trivial⟩
        show own s' fs' = own s fs'
        rw [hc.runOut s' c' fs' hr, hc.runOut s c' fs' hr]
        exact hown
      ownSys := fun _ _ _ h => by rw [hs] at h; cases h
      ownTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      site := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkInstr := fun _ _ tree he => by rw [hex] at he; cases he; exact htk
      tkSys := fun h => by rw [hs] at h; cases h
      owned := hO
      wrTail := fun h => by rw [hs] at h; cases h
      wr := fun _ _ _ _ => wrOkA_of_noWr (noWr_done hex)
      zero := hc.zero
      abortOk := fun k a ha hpc => (hP.noAbort k a ha hpc).elim
      abInstr := fun hn => (hn hAb).elim
      abSys := fun hn => (hn hAb).elim
      abTake := fun hn => (hn hAb).elim }

/-- **`SFactsA` in the phase at a `syscall`** of `z` bytes off the release
and take sites, at a control with `RefCtl`'s facts, with the write abort
facts (`hab`) and the write tail (`hwr`) given: every state the kernel
resumes in is past it, owning what `s` owns and in the take phase iff `s`
is. -/
theorem sfactsA_sysW {z : Nat} (hc : RefCtl Λ p own lbl F c fs)
    (hpl : Spike.Lib.X64ConsumerS.PlacedSE Λ lbl s c fs)
    (hrel : ∀ a, μ.site .release = some a → pcOf s ≠ a) (htake : ∀ a, μ.site .take = some a → pcOf s ≠ a)
    (hcl : CellAt s (op64 .syscall) z)
    (hnext : ∀ m, own (after s z m) fs = own s fs ∧ (Tk (after s z m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hab : ∀ k a, μ.abortAt k = some a → pcOf s = a → (k = .writeErr ∧ Ab s) ∧
      ∀ v, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) →
        v % 256 = Scc.Sem.Kernel.abortStatus)
    (hwr : ∀ fd buf n, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s)
    (hAb : Ab s) :
    SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt Ab := by
  have hs : abi.atSys s = true := atSyscall_of_cellAt hcl
  have hsucc : ∀ call, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Scc.Sem.Kernel.certSuccs abi s call, own s' fs = own s fs ∧ (Tk s' ↔ Tk s) := by
    intro call _ s' hs'
    by_cases ha : ∃ a, call = .archSetFs a
    · obtain ⟨a, rfl⟩ := ha
      rw [certSuccs_archSetFs hcl a] at hs'
      cases hs' with
      | head => exact hnext _
      | tail _ h => cases h
    · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hcl fun a he => ha ⟨a, he⟩).1 hs'
      exact hnext _
  refine
    { noRet := hc.noRet
      cell := hc.cell
      noSite := hrel
      mapped := fun h => by rw [hs] at h; cases h
      place := hpl
      svc := fun _ => ⟨z, hcl⟩
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.runOut s c₂ fs₂ hr
        · exact hc.runIn s c₁ fs₁ hr
      ownInstr := fun _ _ _ h => by rw [hs] at h; cases h
      ownSys := fun c' fs' hr _ call hd s' hs' => by
        rw [hc.runOut s' c' fs' hr, hc.runOut s c' fs' hr]
        exact (hsucc call hd s' hs').1
      ownTake := fun a ha hpc => (htake a ha hpc).elim
      site := fun a ha hpc => (htake a ha hpc).elim
      tkTake := fun a ha hpc => (htake a ha hpc).elim
      tkInstr := fun _ h => by rw [hs] at h; cases h
      tkSys := fun _ call hd s' hs' => (hsucc call hd s' hs').2
      owned := hO
      wrTail := fun _ => hwr
      wr := fun _ _ _ h => by rw [hs] at h; cases h
      zero := hc.zero
      abortOk := fun k a ha hpc => let ⟨h1, h2⟩ := hab k a ha hpc; ⟨.inl h1, h2⟩
      abInstr := fun hn => (hn hAb).elim
      abSys := fun hn => (hn hAb).elim
      abTake := fun hn => (hn hAb).elim }

end State

/-! ## The path's states in the phase -/

section Phase

variable {lab : Label → Int64}

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over the dispatcher's prologue and tests
(`BlockSpec.unfolds` with `AI.step` through its non-`rfl` equations). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [arun, dstep, classify, RegOnly, AI.so, soReg, regDst, regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply, Reg64s.get_low64, BlockSpec.AI.step_ld', BlockSpec.AI.step_st',
    BlockSpec.AI.step_push', BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', BlockSpec.AI.step_jmp',
    BlockSpec.AI.step_jcc'])

/-- The dispatcher's prologue keeps `%rdi` before each instruction. -/
theorem d0_rdi (pc : Int64) (σ : AS) {k : Nat} (hk : k < Abort.Disp.d0.length) :
    (arun lab (Abort.Disp.d0.take k) ⟨pc, Abort.oE, σ⟩).σ.regs.get64 .rdi = σ.regs.get64 .rdi := by
  simp only [Abort.Disp.d0] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- A test of the dispatcher keeps `%rbp` at the frame's base and the slots
before each instruction. -/
theorem t_run {blk : List (Directive × Nat)}
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4)
    (pc : Int64) (σ : AS) {k : Nat} (hk : k < blk.length) :
    (arun lab (blk.take k) ⟨pc, Abort.Disp.oD, σ⟩).so.get .rbp = some 0 ∧
      (arun lab (blk.take k) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot = σ.slot := by
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4] at hk ⊢ <;>
    simp only [List.length_zip, List.length_cons, List.length_nil] at hk <;>
    rcases k with _|_|_|_|k <;> (try omega) <;> arun_simp

/-- The word at `-8(%rbp)` from the abstract state, `%rbp` at the frame's
base. -/
theorem bp_four {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ)
    (ho : o.get .rbp = some 0) (hoff : R.Off (-8)) (h4 : σ.slot (-8) = 4#64) :
    WriteAb.bpLoad s (-8) = some 4#64 := by
  obtain ⟨j, hj, hjv⟩ := hA.slot (-8) hoff
  have hbp := hA.so .rbp 0 ho
  rw [← hA.regs] at hbp
  simp only [Reg64s.get64] at hbp
  simp only [WriteAb.bpLoad, Scc.Sem.X64.privLoad, hbp]
  rw [show R.addr 0 + (-8) = R.addr (-8) by simp only [Spike.Lib.Region.addr]; rw [BitVec.add_assoc]; rfl,
    hj, Option.map_some, hjv, h4]

/-- A state of the dispatcher's prologue with `%rdi = 4` is in the phase. -/
theorem ab_dispE {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hmem : s.st.2 ∈ WriteAb.dispEPcs lab)
    (hA : Abs R o s.st.1 σ) (h4 : σ.regs.get64 .rdi = 4#64) : WriteAb.Ab lab s :=
  .inr (.inr (.inr (.inl ⟨hmem, by rw [hA.regs]; exact h4⟩)))

/-- A state of the dispatcher's tests with `4` at `-8(%rbp)` is in the
phase. -/
theorem ab_dispT {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hmem : s.st.2 ∈ WriteAb.dispTPcs lab)
    (hA : Abs R o s.st.1 σ) (ho : o.get .rbp = some 0) (hoff : R.Off (-8)) (h4 : σ.slot (-8) = 4#64) :
    WriteAb.Ab lab s :=
  .inr (.inr (.inr (.inr (.inl ⟨hmem, bp_four hA ho hoff h4⟩))))

/-- The prologue's pcs are `dispEPcs`. -/
theorem memE {k : Nat} (hk : k < Abort.Disp.d0.length) :
    lab "scc_rt_abort" + Int64.ofNat (cellOff Abort.Disp.d0 k) ∈ WriteAb.dispEPcs lab := by
  simp only [Abort.Disp.d0, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|_|k <;> (try omega) <;> simp [WriteAb.dispEPcs, cellOff] <;> decide

/-- The four tests' pcs are `dispTPcs`. -/
theorem memT {l : Label} {blk : List (Directive × Nat)}
    (hl : l = ".Lscc_rt_abort.entry" ∨ l = ".Lscc_rt_abort.next1" ∨ l = ".Lscc_rt_abort.next3" ∨
      l = ".Lscc_rt_abort.next5")
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4)
    {k : Nat} (hk : k < blk.length) : lab l + Int64.ofNat (cellOff blk k) ∈ WriteAb.dispTPcs lab := by
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4, List.length_zip, List.length_cons,
      List.length_nil] at hk ⊢ <;>
    rcases hl with rfl | rfl | rfl | rfl <;> rcases k with _|_|_|_|k <;> (try omega) <;>
    simp [WriteAb.dispTPcs, cellOff] <;> decide

/-- The jumps to the next test are `dispTPcs`. -/
theorem memJ {l : Label} {blk : List (Directive × Nat)}
    (hl : l = ".Lscc_rt_abort.entry" ∨ l = ".Lscc_rt_abort.next1" ∨ l = ".Lscc_rt_abort.next3")
    (hb : blk = Abort.Disp.j1 ∨ blk = Abort.Disp.j2 ∨ blk = Abort.Disp.j3)
    {k : Nat} (hk : k < blk.length) : lab l + 16 + Int64.ofNat (cellOff blk k) ∈ WriteAb.dispTPcs lab := by
  rcases hb with rfl | rfl | rfl <;>
    simp only [Abort.Disp.j1, Abort.Disp.j2, Abort.Disp.j3, List.length_zip, List.length_cons,
      List.length_nil] at hk ⊢ <;>
    rcases hl with rfl | rfl | rfl <;> rcases k with _|k <;> (try omega) <;>
    simp [WriteAb.dispTPcs, cellOff] <;> decide

/-- The jump to the write stub's pcs are `g4Pcs`. -/
theorem memG {k : Nat} (hk : k < Abort.Disp.g4.length) :
    lab ".Lscc_rt_abort.is6" + Int64.ofNat (cellOff Abort.Disp.g4 k) ∈ WriteAb.g4Pcs lab := by
  simp only [Abort.Disp.g4, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|k <;> (try omega) <;> simp [WriteAb.g4Pcs, cellOff] <;> decide

/-- The write stub's prologue is in `stubPcs`. -/
theorem memX0 {k : Nat} (hk : k < Abort.x0.length) :
    lab Abort.write.fn + Int64.ofNat (cellOff Abort.x0 k) ∈ WriteAb.stubPcs lab := by
  simp only [Abort.x0, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|k <;> (try omega) <;> simp [WriteAb.stubPcs, cellOff] <;> decide

/-- The write stub's argument block is in `stubPcs`. -/
theorem memX1 {k : Nat} (hk : k < Abort.x1Write.length) :
    lab Abort.write.entry + 7 + Int64.ofNat (cellOff Abort.x1Write k) ∈ WriteAb.stubPcs lab := by
  simp only [Abort.x1Write, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|_|_|k <;> (try omega) <;> simp [WriteAb.stubPcs, cellOff, Int64.add_assoc] <;> decide

/-- The write stub's block after the call is in `stubPcs`. -/
theorem memX2 {k : Nat} (hk : k < Abort.x2.length) :
    lab Abort.write.entry + 36 + Int64.ofNat (cellOff Abort.x2 k) ∈ WriteAb.stubPcs lab := by
  simp only [Abort.x2, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|k <;> (try omega) <;> simp [WriteAb.stubPcs, cellOff, Int64.add_assoc] <;> decide

/-- The write stub's system call is in `stubPcs`. -/
theorem memSys : Abort.pcSys lab Abort.write ∈ WriteAb.stubPcs lab := by
  simp [WriteAb.stubPcs, Abort.pcSys]

end Phase

/-! ## The path's blocks and single instructions -/

section Nodes

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame} {R : Region} {F : MachineData → Prop} {Ab : State → Prop}

/-- **A block of the write abort path inside `SFactsA`** at the frames
`frs`: as `blkW_heapA` with the source control's facts `RefCtl` (`hc`), each
state before an instruction in the phase (`hAb`). -/
theorem blkW_writeA {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {lo hi : Int} {l : Label} {off : Nat} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hph : blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat off) 0 blk = true)
    (hnr : noRetBlk blk = true) (hJ : ∀ σ c, n.J σ c → c = c0) (hc : RefCtl Λ p own lbl F c0 frs)
    (hAb : ∀ (s : State) σ c j m, n.J σ c → j < blk.length →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).σ →
      Ab { s with st := (m, n.pc + Int64.ofNat (cellOff blk j)) }) :
    BlkW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt Ab) K exe endPc R F n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn
  rw [he, ← hI.labOk] at hph
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph
    (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
  intro s σ c hs hn _ _ hA hD hJc k hk m hA' hDm
  have hab := hAb s σ c k m hJc hk hA'
  obtain rfl := hJ σ c hJc
  obtain ⟨hP, hK⟩ := hpc k hk { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } hs hn rfl
  refine ⟨?_, hK⟩
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some (a.toDir, blk[k].2) := by rw [List.getElem?_eq_getElem hk, ← hdir]
  have hcell : Kraken.Promising.Lower.X64.CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }
      a.toDir blk[k].2 :=
    (hcode s hs hn).cell hd rfl rfl rfl
  have hlA : Kraken.Promising.Lower.X64.labelAddr { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } =
      (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [hs]
  obtain ⟨m', hex, -, -⟩ := exec_ai haok hR hlo hhi hcell hreg hA'
  rw [hlA] at hex
  obtain ⟨hown, htk⟩ := hph' σ c hJc k hk a hca { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }
    { s with st := (m', a.tgt (_root_.Executable.labels exe).label
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
      (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) } hs hn hs hn rfl rfl
  exact sfactsA_doneW hc (hc.place _ (hF _ _ hD hDm)) hP hcell (AI.not_syscall hreg) hex
    hown htk (fun _ => owned_off hR hR8 hl hh hsub (stackOff_stable hfit _ _ (hFO _ hD) hDm)
      fun k' hk' => Option.isSome_iff_exists.mpr (by obtain ⟨j, hj, -⟩ := hA'.slot k' hk'; exact ⟨j, hj⟩)) hab

/-- **A single instruction without an event (`SI`) of the write abort path
inside `SFactsA`**: as `nodeW_si_heapA` with `RefCtl` (`hc`), every state at
its pc in the phase (`hAb`). -/
theorem nodeW_si_writeA {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {n : ND} {si : SI} {l : Label} {off z : Nat} {q : Int64} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAtB cells l off [(si.toDir, z)] = true) (he : lab l + Int64.ofNat off = q) (hp : n.pc = q)
    (hok : okPc q.toBitVec.toNat = true) (hph : ph (q + Int64.ofNat z).toBitVec.toNat = ph q.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hJ : ∀ σ c, n.J σ c → c = c0) (hc : RefCtl Λ p own lbl F c0 frs) (hAb : ∀ s : State, s.st.2 = q → Ab s) :
    NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt Ab) K exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJc⟩
  obtain rfl := hJ σ c hJc
  rw [hp] at hpc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact hok)
  have hcell := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have hnx := Spike.Lib.X64.Rt.next_same hI hpc hph
  refine ⟨sfactsA_doneW hc (hc.place s hD) hP.1 hcell
    (by cases si <;> intro w w' h <;> cases h) (exec_si hcell) (hnx _).1 (hnx _).2
    (fun _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => ?_) (hAb s hpc), hP.2⟩
  obtain ⟨j, hj, -⟩ := hA.slot k hk
  rw [hj]; rfl

end Nodes

/-! ## `StubWW` (the phase check `abortPhWriteOk` in `Spike/Lib/X64AbortPhW.lean`) -/

section Stub

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame}
  {al : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {R : Region} {F : MachineData → Prop}

set_option maxHeartbeats 800000 in
/-- **The write abort path's obligations inside `SFactsA … frs Dt
(WriteAb.Ab lab)`** (`Abort.Disp.StubWW`), for a program with the abort code
(`hprog`), an instance's facts at the frames `frs` (`hI`) and the path's
phase check (`hphs`). The callee's region holds the stub's frame (`hlo`,
`hhi`); the words of `rS` lie off it in the frame condition (`hFO`); the
source control `c0` has `RefCtl`'s facts (`hc`). The exit call is the write
abort site: off the release and take sites (`hrel`, `htk`), no other kind's
(`hk`), no outside move (`hKex`), the memory side's abort (`hms`). The write
tail `Dt` holds at the `write` (`hwr`). -/
theorem stubWW_sfactsA {kp : Nat} (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {c0 : Ctl} {Dt : State → Prop}
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hphs : abortPhWriteOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p own lbl F c0 frs)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.write.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.write.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.write.exit).toBitVec.toNat = a → k = .writeErr)
    (hKex : ∀ s s', pcOf s = (lab Abort.write.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.write.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.N lab Abort.write c0 .sys) s c → Dt s) :
    Abort.Disp.StubWW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (WriteAb.Ab lab))
      K p al ms exe endPc R F c0 := by
  have hlab := hI.labOk
  subst hlab
  have hoff : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hb1, hsysIn, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, -, hg4, -⟩ := hdi
  simp only [abortPhWriteOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pj2, pt3, pj3, pt4, pg4, pb0, o1, q1, pb1, o5, q5, pb2, qx⟩ := hphs
  have hown : ∀ (s : State) (o : SO) σ, Abs R o s.st.1 σ → F s.st.1 → Tk s → Owned Λ rS s :=
    fun s _ σ hA hD _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have he34 : (_root_.Executable.labels exe).label Abort.write.entry + Int64.ofNat 34 =
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .sys).pc := rfl
  have hsysW : NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt
      (WriteAb.Ab (_root_.Executable.labels exe).label)) K exe endPc R F
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .sys) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
    have hc0 : c = c0 := hJ
    subst hc0
    have hAb : WriteAb.Ab (_root_.Executable.labels exe).label s := WriteAb.ab_stub (by rw [hpc]; exact memSys)
    rw [← he34] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o5)
    exact ⟨sfactsA_sysW hc (hc.place s hD) hP.1.noSite hP.1.noTake
      (Spike.Lib.X64.Rt.cellOf hI hsysIn rfl hs hn hpc) (Spike.Lib.X64.Rt.next_same hI hpc q5) (hown s _ σ hA hD)
      (fun k a ha e => (hP.1.noAbort k a ha e).elim) (fun _ _ _ _ => hwr s c hAt) hAb, hP.2⟩
  have hsex : NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt
      (WriteAb.Ab (_root_.Executable.labels exe).label)) K exe endPc R F
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) := by
    rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJ, hax, hdi⟩
    have hc0 : c = c0 := hJ
    subst hc0
    have hpcN : pcOf s = ((_root_.Executable.labels exe).label Abort.write.exit).toBitVec.toNat := by
      unfold pcOf; rw [hpc]; rfl
    have hAb : WriteAb.Ab (_root_.Executable.labels exe).label s :=
      WriteAb.ab_stub (by rw [hpc]; simp [Abort.N, WriteAb.stubPcs])
    have hx231 : σ.regs.rax.toNat = 231 := by
      simp only [Reg64s.get64] at hax
      rw [← UInt64.toNat_toBitVec, hax]; rfl
    have hd : Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
        some (.exitGroup σ.regs.rdi.toNat) := by
      rw [← syscallCall_exitGroup hx231, syscallCall, ← hA.regs]; rfl
    refine ⟨sfactsA_sysW hc (hc.place s hD) (fun a ha => hpcN ▸ hrel a ha)
      (fun a ha => hpcN ▸ htk a ha) (Spike.Lib.X64.Rt.cellOf hI hx (ofNat_zero' _) hs hn hpc)
      (Spike.Lib.X64.Rt.next_same hI hpc qx) (hown s _ σ hA hD)
      (fun k a ha e => ⟨⟨hk k a ha (hpcN ▸ e), hAb⟩, fun v hv => ?_⟩)
      (fun _ _ _ h => by rw [hd] at h; cases h) hAb, fun s' => hKex s s' hpcN⟩
    rw [hd] at hv
    cases hv
    simp only [Reg64s.get64] at hdi
    rw [← UInt64.toNat_toBitVec, hdi]; rfl
  have hT1 : Abort.Disp.t1 = Abort.Disp.t1 ∨ Abort.Disp.t1 = Abort.Disp.t2 ∨ Abort.Disp.t1 = Abort.Disp.t3 ∨
    Abort.Disp.t1 = Abort.Disp.t4 := .inl rfl
  have hT2 : Abort.Disp.t2 = Abort.Disp.t1 ∨ Abort.Disp.t2 = Abort.Disp.t2 ∨ Abort.Disp.t2 = Abort.Disp.t3 ∨
    Abort.Disp.t2 = Abort.Disp.t4 := .inr (.inl rfl)
  have hT3 : Abort.Disp.t3 = Abort.Disp.t1 ∨ Abort.Disp.t3 = Abort.Disp.t2 ∨ Abort.Disp.t3 = Abort.Disp.t3 ∨
    Abort.Disp.t3 = Abort.Disp.t4 := .inr (.inr (.inl rfl))
  have hT4 : Abort.Disp.t4 = Abort.Disp.t1 ∨ Abort.Disp.t4 = Abort.Disp.t2 ∨ Abort.Disp.t4 = Abort.Disp.t3 ∨
    Abort.Disp.t4 = Abort.Disp.t4 := .inr (.inr (.inr rfl))
  have hj : ∀ {blk : List (Directive × Nat)} {j : Nat},
      (blk = Abort.Disp.j1 ∨ blk = Abort.Disp.j2 ∨ blk = Abort.Disp.j3) → j < blk.length → j = 0 := by
    intro blk j hb hk
    rcases hb with rfl | rfl | rfl <;>
      simp only [Abort.Disp.j1, Abort.Disp.j2, Abort.Disp.j3, List.length_zip, List.length_cons,
        List.length_nil] at hk <;> omega
  exact stubWW_of_code hI.lays hI.endOk hprog hK hF
    (blkW_writeA hI hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pd0 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA => ab_dispE (memE hk) hA ((d0_rdi _ _ hk).trans hJ.2))
    (blkW_writeA hI ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt1 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inl rfl) hT1 hk) hA (t_run hT1 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run hT1 _ _ hk).2).trans hJ.2))
    (blkW_writeA hI hj1 rfl Abort.Disp.j1_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj1 rfl (fun _ _ h => h.1) hc
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inl rfl) hk
        exact ab_dispT (memJ (.inl rfl) (.inl rfl) hk) hA
          (by first | rfl | simp [arun, SO.get, Spike.Lib.lk, Abort.Disp.oD]) hoff hJ.2)
    (blkW_writeA hI ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt2 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inr (.inl rfl)) hT2 hk) hA (t_run hT2 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run hT2 _ _ hk).2).trans hJ.2))
    (blkW_writeA hI hj2 rfl Abort.Disp.j2_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj2 rfl (fun _ _ h => h.1) hc
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inr (.inl rfl)) hk
        exact ab_dispT (memJ (.inr (.inl rfl)) (.inr (.inl rfl)) hk) hA
          (by first | rfl | simp [arun, SO.get, Spike.Lib.lk, Abort.Disp.oD]) hoff hJ.2)
    (blkW_writeA hI ht3 (ofNat_zero' _) Abort.Disp.t3_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt3 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inr (.inr (.inl rfl))) hT3 hk) hA (t_run hT3 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run hT3 _ _ hk).2).trans hJ.2))
    (blkW_writeA hI hj3 rfl Abort.Disp.j3_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pj3 rfl (fun _ _ h => h.1) hc
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl := hj (.inr (.inr rfl)) hk
        exact ab_dispT (memJ (.inr (.inr rfl)) (.inr (.inr rfl)) hk) hA
          (by first | rfl | simp [arun, SO.get, Spike.Lib.lk, Abort.Disp.oD]) hoff hJ.2)
    (blkW_writeA hI ht4 (ofNat_zero' _) Abort.Disp.t4_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pt4 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inr (.inr (.inr rfl))) hT4 hk) hA (t_run hT4 _ _ hk).1 hoff
        ((congrArg (fun f => f (-8)) (t_run hT4 _ _ hk).2).trans hJ.2))
    (blkW_writeA hI hg4 (ofNat_zero' _) Abort.Disp.g4_ok hR hR8 (by omega) hhi hl hh
      hF hsub hfit hFO pg4 rfl (fun _ _ h => h) hc
      fun _ _ _ _ _ _ hk _ => WriteAb.ab_g4 (memG hk))
    (blkW_writeA hI hb0 (ofNat_zero' _) Abort.x0_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb0 rfl (fun _ _ h => h) hc
      fun _ _ _ _ _ _ hk _ => WriteAb.ab_stub (memX0 hk))
    (nodeW_si_writeA (si := Abort.siMsg Abort.write) hI hn1 rfl (ofNat_zero' _).symm o1 q1
      hR hR8 hl hh hsub hFO (fun _ _ h => h) hc
      fun _ h => WriteAb.ab_stub (by rw [h, ofNat_zero']; simp [WriteAb.stubPcs]))
    (blkW_writeA hI hb1 rfl Abort.x1Write_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb1 rfl (fun _ _ h => h) hc
      fun _ _ _ _ _ _ hk _ => WriteAb.ab_stub (memX1 hk))
    hsysW
    (blkW_writeA hI hb2 rfl Abort.x2_ok hR hR8 hlo hhi hl hh
      hF hsub hfit hFO pb2 rfl (fun _ _ h => h) hc
      fun _ _ _ _ _ _ hk _ => WriteAb.ab_stub (memX2 hk))
    hsex
    (fun s c ⟨hs, _, _, hpc, _⟩ => hms s hs hpc)

end Stub

end Spike.Lib.X64.StubW
