/-
**An abort stub's write tail** (AArch64), for every stub (`Abort.Stub`,
`Spike/Lib/A64Abort.lean`): after the stub's `write` system call (to the
error output) only the shared block `Abort.b2` (`str x0, [sp, #8]`,
`movz x0, #101`, `movz x8, #94`) and the `exit_group` call follow, so the
states from the `write` on form a predicate `StubDt` closed under the
certification steps, keeping the promise set. `Spike/Lib/LowerA64/OvfDt.lean`
is this at the overflow stub; here the stub is a parameter, so one proof
covers the write-abort and heap-abort stubs' tails (pieces of a program's
write tail `Dt`, combined with `ClosedC.union`, `Spike/Lib/TailDt.lean`).

- `StubDt exe endPc lab st`: the five tail positions: at the `write`
  (`x0 = 2`, `x8 = 64`, the spill's facts `Sp16`, `Spilled`), at the store
  (its facts), at the two `movz`, at the exit call (`x8 = 94`);
- `stubDt_closed`: `StubDt` is closed under certification (`ClosedC`),
  given the stub's code and the tail off the transfer sites (`hns`);
- `stubDt_of_at`: the stub's `write` node (`At … .svc`) is in `StubDt`, for
  a 16-aligned region holding the stub's frame.
-/
import Spike.Lib.LowerA64.OvfDt
import Spike.Lib.TailDt

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower.A64 (CellAt after exec_str_sp exec_movz)
open Kraken.Promising.Lower (silentTree_done)
open Scc.Sem
open Scc.Sem.A64 (abi pcOf atSvc_of_cellAt atSvc_false_of_cellAt mem_certSuccs_svc)
open Spike.Bridge.CertC (stepC_silent stepC_dead)
open Spike.Lib.A64.Flow
open Spike.Lib.A64
open Spike.Lib.LowerA64 (spill Sp16 Spilled)
open Spike.Lib (ClosedC)
open Scc.Cert.Rt.A64.Print (add4 add0)

/-! ## The tail states -/

/-- **An abort stub's write tail**: the executable and its end, and one of
the tail's positions: the `write` call (`x0 = 2`, `x8 = 64`, `sp`
16-aligned, the spill mapped), the spill (`sp` 16-aligned, the spill
mapped), the two `movz`, the exit call (`x8 = 94`). -/
def StubDt (exe : _root_.Executable) (endPc : Int64) (lab : Label → Int64) (st : Abort.Stub) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧
    (s.st.2 = Abort.pcSvc lab st ∧ s.st.1.regs.X0 = 2 ∧ s.st.1.regs.X8 = 64 ∧ Sp16 s ∧ Spilled s ∨
      s.st.2 = Abort.pcSvc lab st + 4 ∧ Sp16 s ∧ Spilled s ∨
      s.st.2 = Abort.pcSvc lab st + 4 + 4 ∨
      s.st.2 = Abort.pcSvc lab st + 4 + 4 + 4 ∨
      s.st.2 = lab st.exit ∧ s.st.1.regs.X8 = 94)

/-! ## Closure under certification -/

section Step

variable {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {μ : Marks} {st : Abort.Stub}

/-- **The stub's write tail is closed under certification**, keeping the
promises, given the stub's code (`hcode`, any argument block `b1` and
source control) and the tail off the transfer sites (`hns`): the `write`
resumes past its cell with `sp` and the private memory unchanged; the spill
(mapped, aligned) and the two `movz` are silent; the `exit_group` call has
no step. -/
theorem stubDt_closed {c0 : Ctl} {b1 : List Directive} (hcode : Abort.Code st c0 b1 exe endPc)
    (hlab : (_root_.Executable.labels exe).label = lab)
    (hns : ∀ s, StubDt exe endPc lab st s → Kernel.siteAt abi μ s = none) (x : Kernel.KState) :
    ClosedC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x 0) 0 (StubDt exe endPc lab st) := by
  subst hlab
  rintro ⟨t, mem⟩ q hD h
  have hsi := hns _ hD
  obtain ⟨he, hn, hc⟩ := hD
  -- a silent instruction at `t.st` steps to the state `exec` gives
  have hsil : ∀ {d : Directive} {s' : State}, CellAt t.st d 4 → (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) →
      isaLSE2.exec t.st = some (.done s') → q.1.st = s' ∧ q.1.prom = t.prom := by
    intro d s' hc hd hex
    have hce : (Kernel.certSem abi Arch.armv8 μ x 0).exec t.st = some (.done s') := by
      show Kernel.soloExec abi Arch.armv8 μ x 0 t.st = _
      rw [Kernel.soloExec_of_not_atSys abi hsi (atSvc_false_of_cellAt hc hd)]
      exact hex
    obtain ⟨-, hpr, hP⟩ := stepC_silent hce (silentTree_done _) h
    exact ⟨hP, hpr⟩
  rcases hc with ⟨hpc, h0, h8, hal, j, hj⟩ | ⟨hpc, hal, j, hj⟩ | hpc | hpc | ⟨hpc, h8⟩
  · -- the `write`: resumed past the cell, `sp` and the private memory unchanged
    have hc : CellAt t.st svcDir 4 := (hcode.svc t.st he hn).cell (j := 0) rfl rfl rfl (by rw [add0]; exact hpc)
    have hat : abi.atSys t.st = true := atSvc_of_cellAt hc
    obtain ⟨buf, n, hd⟩ := Spike.Lib.A64.StubW.svcCall_write h0 h8
    have hd' : Kernel.decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some (.write 2 buf n) := hd
    obtain ⟨outs, o, hso, ho, rfl⟩ := h
    obtain ⟨-, hpr, hmem⟩ := Kernel.certSem_step_sys hsi hat hd' (by intro _ _ h; cases h) hso ho
    obtain ⟨r, -, hr⟩ := (mem_certSuccs_svc hc hd').mp hmem
    refine ⟨?_, hpr⟩
    show StubDt _ _ _ _ o.thread.st
    rw [← hr]
    exact ⟨he, hn, .inr (.inl ⟨by show t.st.st.2 + Int64.ofNat 4 = _; rw [hpc]; rfl, hal, j, hj⟩)⟩
  · -- `str x0, [sp, #8]`: mapped and aligned, silent
    have hc := (hcode.n5 t.st he hn).cell (j := 0) rfl rfl rfl (by rw [add0]; exact hpc)
    obtain ⟨hq, hpr⟩ := hsil hc (by intro _ h; cases h) (exec_str_sp hc hal rfl hj)
    refine ⟨?_, hpr⟩
    rw [hq]
    exact ⟨he, hn, .inr (.inr (.inl (by show t.st.st.2 + Int64.ofNat 4 = _; rw [hpc]; rfl)))⟩
  · -- `movz x0, #101`
    have hc := (hcode.n5 t.st he hn).cell (j := 1) rfl rfl rfl (by rw [hpc]; simp only [Abort.N, add4, add0])
    obtain ⟨hq, hpr⟩ := hsil hc (by intro _ h; cases h) (exec_movz hc)
    refine ⟨?_, hpr⟩
    rw [hq]
    exact ⟨he, hn, .inr (.inr (.inr (.inl (by show t.st.st.2 + Int64.ofNat 4 = _; rw [hpc]; rfl))))⟩
  · -- `movz x8, #94`: at the exit call
    have hc := (hcode.n5 t.st he hn).cell (j := 2) rfl rfl rfl (by rw [hpc]; simp only [Abort.N, add4, add0])
    obtain ⟨hq, hpr⟩ := hsil hc (by intro _ h; cases h) (exec_movz hc)
    refine ⟨?_, hpr⟩
    rw [hq]
    refine ⟨he, hn, .inr (.inr (.inr (.inr ⟨?_, ?_⟩)))⟩
    show t.st.st.2 + Int64.ofNat 4 = _
    rw [hpc, hcode.hexit]
    rfl
    simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  · -- the `exit_group` call: no step
    exfalso
    have hc : CellAt t.st svcDir 4 := (hcode.ex t.st he hn).cell (j := 0) rfl rfl rfl (by rw [add0]; exact hpc)
    have hat : abi.atSys t.st = true := atSvc_of_cellAt hc
    have hd : Kernel.decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some (.exitGroup t.st.st.1.regs.X0.toNat) :=
      svcCall_exitGroup (by rw [h8]; rfl)
    refine stepC_dead (n := 0) (f := fun i => .done ([] : List isaLSE2.State)[i]) ?_ rfl h
    simp only [Kernel.certSem, Kernel.soloExec, hsi, hat, ite_true, hd, Kernel.results, List.filterMap_nil]
    rfl

end Step

/-! ## Entry -/

/-- **The stub's `write` node is in the tail**, for a 16-aligned region
holding the stub's 48-byte frame: `sp` is the frame's base (16-aligned)
and the spill is the frame's cell at `-40`. -/
theorem stubDt_of_at {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {st : Abort.Stub}
    {R : Region} {F : MachineData → Prop} {c0 c : Ctl} {s : State} (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hAt : At exe endPc R F (Abort.N lab st c0 .svc) s c) :
    StubDt exe endPc lab st s := by
  obtain ⟨hs, hn, -, hpc, σ, hA, -, -, h0, h8⟩ := hAt
  have hsp : s.st.1.regs.SP.toBitVec = R.addr (-48) := by rw [hA.regs]; exact hA.so.sp
  obtain ⟨j, hj, -⟩ := hA.slot (-40) ⟨by decide, by omega, by omega⟩
  refine ⟨hs, hn, .inl ⟨hpc, by rw [hA.regs]; exact h0, by rw [hA.regs]; exact h8, ?_, j, ?_⟩⟩
  · show _ = _
    rw [hsp]
    exact R.addr_align16 hal (by decide)
  · unfold spill
    rw [hsp, addr_spn, show (-48 : Int) + (8 : Int64).toInt = -40 by decide]
    exact hj

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Rt.stubDt_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stubDt_closed

end Spike.Lib.A64.Rt
