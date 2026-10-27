/-
**An abort stub's write tail** (x86-64), for every stub (`Abort.Stub`,
`Spike/Lib/X64Abort.lean`): after the stub's `write` system call (to the
error output) only the shared block `Abort.x2` (`movq %rax, -16(%rbp)`,
`movq $101, %rdi`, `movl $231, %eax`) and the `exit_group` call follow, so
the states from the `write` on form a predicate `StubDt` closed under the
certification steps, keeping the promise set. `Spike/Lib/LowerX64/OvfDt.lean`
is this at the overflow stub; here the stub and its argument block are
parameters, so one proof covers the write-abort and heap-abort stubs' tails
(pieces of a program's write tail `Dt`, combined with `ClosedC.union`,
`Spike/Lib/TailDt.lean`). The twin of `Spike/Lib/Rt/A64StubDt.lean`.

- `StubDt exe endPc lab st`: the five tail positions: at the `write`
  (`%rax = 1`, `%rdi = 2`, the spill `-16(%rbp)` mapped, `Spilled`), at the
  store (the spill mapped), at the two moves, at the exit call
  (`%rax = 231`);
- `stubDt_closed`: `StubDt` is closed under certification (`ClosedC`),
  given the stub's code and the tail off the transfer sites (`hns`);
- `stubDt_of_at`: the stub's `write` node (`At … .sys`) is in `StubDt`, for
  a region holding the stub's frame `[-24, 16)`.
-/
import Spike.Lib.LowerX64.OvfDt
import Spike.Lib.TailDt

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt after exec_store_mapped op64)
open Kraken.Promising.Lower (silentTree_done)
open Scc.Sem
open Scc.Sem.X64 (abi pcOf atSyscall_of_cellAt atSyscall_false_of_cellAt mem_certSuccs_syscall)
open Spike.Bridge.CertC (stepC_silent stepC_dead)
open Spike.Lib.X64
open Spike.Lib.X64.StubW (syscallCall_write)
open Spike.Lib.LowerX64 (spill Spilled)
open Spike.Lib (ClosedC)

/-! ## The tail states -/

/-- **An abort stub's write tail**: the executable and its end, and one of
the tail's positions: the `write` call (`%rax = 1`, `%rdi = 2`, the spill
mapped), the spill (mapped), the two moves, the exit call (`%rax = 231`). -/
def StubDt (exe : _root_.Executable) (endPc : Int64) (lab : Label → Int64) (st : Abort.Stub) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧
    (s.st.2 = Abort.pcSys lab st ∧ s.st.1.regs.get64 .rax = 1 ∧ s.st.1.regs.get64 .rdi = 2 ∧ Spilled s ∨
      s.st.2 = lab st.entry + 36 ∧ Spilled s ∨
      s.st.2 = lab st.entry + 40 ∨
      s.st.2 = lab st.entry + 47 ∨
      s.st.2 = lab st.exit ∧ s.st.1.regs.get64 .rax = 231)

/-! ## Closure under certification -/

section Step

variable {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {μ : Marks} {st : Abort.Stub}

/-- **The stub's write tail is closed under certification**, keeping the
promises, given the stub's code (`hcode`, any argument block `x1` and
source control) and the tail off the transfer sites (`hns`): the `write`
resumes past its cell with `%rbp` and the private memory unchanged; the
spill (mapped) and the two moves are silent; the `exit_group` call has no
step. -/
theorem stubDt_closed {c0 : Ctl} {x1 : List (Directive × Nat)} (hcode : Abort.Code st c0 x1 exe endPc)
    (hlab : (_root_.Executable.labels exe).label = lab)
    (hns : ∀ s, StubDt exe endPc lab st s → Kernel.siteAt abi μ s = none) (x : Kernel.KState) :
    ClosedC Arch.tso (Kernel.certSem abi Arch.tso μ x 0) 0 (StubDt exe endPc lab st) := by
  subst hlab
  rintro ⟨t, mem⟩ q hD h
  have hsi := hns _ hD
  obtain ⟨he, hn, hc⟩ := hD
  -- a silent instruction at `t.st` steps to the state `exec` gives
  have hsil : ∀ {d : Directive} {z : Nat} {s' : State}, CellAt t.st d z →
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) →
      isa.exec t.st = some (.done s') → q.1.st = s' ∧ q.1.prom = t.prom := by
    intro d z s' hc hd hex
    have hce : (Kernel.certSem abi Arch.tso μ x 0).exec t.st = some (.done s') := by
      show Kernel.soloExec abi Arch.tso μ x 0 t.st = _
      rw [Kernel.soloExec_of_not_atSys abi hsi (atSyscall_false_of_cellAt hc hd)]
      exact hex
    obtain ⟨-, hpr, hP⟩ := stepC_silent hce (silentTree_done _) h
    exact ⟨hP, hpr⟩
  rcases hc with ⟨hpc, ha, h0, hsp⟩ | ⟨hpc, j, hj⟩ | hpc | hpc | ⟨hpc, h231⟩
  · -- the `write`: resumed past the cell, `%rbp` and the private memory unchanged
    have hc : CellAt t.st (op64 .syscall) 2 := (hcode.sys t.st he hn).cell0 rfl rfl hpc
    have hat : abi.atSys t.st = true := atSyscall_of_cellAt hc
    obtain ⟨buf, n, hd⟩ := syscallCall_write ha h0
    have hd' : Kernel.decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some (.write 2 buf n) := hd
    obtain ⟨outs, o, hso, ho, rfl⟩ := h
    obtain ⟨-, hpr, hmem⟩ := Kernel.certSem_step_sys hsi hat hd' (by intro _ _ h; cases h) hso ho
    obtain ⟨r, -, hr⟩ := (mem_certSuccs_syscall hc (by intro _ h; cases h)).mp hmem
    refine ⟨?_, hpr⟩
    show StubDt _ _ _ _ o.thread.st
    rw [← hr]
    refine ⟨he, hn, .inr (.inl ⟨?_, hsp⟩)⟩
    show t.st.st.2 + Int64.ofNat 2 = _
    rw [hpc, Int64.add_assoc]
    rfl
  · -- `movq %rax, -16(%rbp)`: mapped, silent
    have hc := (hcode.n5 t.st he hn).cell (j := 0) rfl rfl rfl
      (by rw [show Int64.ofNat (cellOff Abort.x2 0) = 0 by decide, Int64.add_zero]; exact hpc)
    obtain ⟨hq, hpr⟩ := hsil hc (by intro _ _ h; cases h)
      (exec_store_mapped hc (eaddr_rbp t.st 4 (-16)) hj)
    refine ⟨?_, hpr⟩
    rw [hq]
    exact ⟨he, hn, .inr (.inr (.inl (by show t.st.st.2 + Int64.ofNat 4 = _; rw [hpc, Int64.add_assoc]; rfl)))⟩
  · -- `movq $101, %rdi`
    have hc := (hcode.n5 t.st he hn).cell (j := 1) rfl rfl rfl
      (by rw [hpc]; show _ = _ + 36 + _; rw [Int64.add_assoc]; rfl)
    obtain ⟨hq, hpr⟩ := hsil hc (by intro _ _ h; cases h) (exec_reg rfl hc)
    refine ⟨?_, hpr⟩
    rw [hq]
    exact ⟨he, hn, .inr (.inr (.inr (.inl (by show t.st.st.2 + Int64.ofNat 7 = _; rw [hpc, Int64.add_assoc]; rfl))))⟩
  · -- `movl $231, %eax`: at the exit call
    have hc := (hcode.n5 t.st he hn).cell (j := 2) rfl rfl rfl
      (by rw [hpc]; show _ = _ + 36 + _; rw [Int64.add_assoc]; rfl)
    obtain ⟨hq, hpr⟩ := hsil hc (by intro _ _ h; cases h) (exec_reg rfl hc)
    refine ⟨?_, hpr⟩
    rw [hq]
    refine ⟨he, hn, .inr (.inr (.inr (.inr ⟨?_, rfl⟩)))⟩
    show t.st.st.2 + Int64.ofNat 5 = _
    rw [hpc, hcode.hexit, Int64.add_assoc]
    rfl
  · -- the `exit_group` call: no step
    exfalso
    have hc : CellAt t.st (op64 .syscall) 2 := (hcode.ex t.st he hn).cell0 rfl rfl hpc
    have hat : abi.atSys t.st = true := atSyscall_of_cellAt hc
    have hx : t.st.st.1.regs.rax.toNat = 231 := by
      simp only [Reg64s.get64] at h231
      rw [← UInt64.toNat_toBitVec, h231]; rfl
    have hd : Kernel.decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some (.exitGroup t.st.st.1.regs.rdi.toNat) :=
      syscallCall_exitGroup hx
    refine stepC_dead (n := 0) (f := fun i => .done ([] : List isa.State)[i]) ?_ rfl h
    simp only [Kernel.certSem, Kernel.soloExec, hsi, hat, ite_true, hd, Kernel.results, List.filterMap_nil]
    rfl

end Step

/-! ## Entry -/

/-- **The stub's `write` node is in the tail**, for a region holding the
stub's frame `[-24, 16)`: `%rbp` is the region's base (`Abort.oI`) and the
spill is the region's cell at `-16`. -/
theorem stubDt_of_at {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {st : Abort.Stub}
    {R : Region}
    {F : MachineData → Prop} {c0 c : Ctl} {s : State} (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hAt : At exe endPc R F (Abort.N lab st c0 .sys) s c) :
    StubDt exe endPc lab st s := by
  obtain ⟨hs, hn, -, hpc, σ, hA, -, -, h0, ha⟩ := hAt
  have hbp : s.st.1.regs.get64 .rbp = R.addr 0 := by rw [hA.regs]; exact hA.so .rbp 0 rfl
  obtain ⟨j, hj, -⟩ := hA.slot (-16) ⟨by decide, by omega, by omega⟩
  refine ⟨hs, hn, .inl ⟨hpc, by rw [hA.regs]; exact ha, by rw [hA.regs]; exact h0, j, ?_⟩⟩
  unfold spill slotA
  rw [hbp, BitVec.ofInt_add, BitVec.ofInt_toInt, ← Region.addr_add,
    show (0 : Int) + (-16 : Int64).toInt = -16 by decide]
  exact hj

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.stubDt_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stubDt_closed

end Spike.Lib.X64.Rt
