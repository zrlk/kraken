/-
**The overflow stub's write tail** (x86-64): after the stub's `write`
system call only `movq %rax, -16(%rbp)`, `movq $101, %rdi`,
`movl $231, %eax` and the `exit_group` call follow (`Abort.x2`,
`Spike/Lib/X64Abort.lean`), so the states from the `write` on form a
predicate `OvfDt` closed under the certification steps, keeping the promise
set. This discharges the write tail `Dt` of `stubW_sfacts` (`hwr`) and,
through `tailNoFul_of_wrIn`, the consumer's `TailNoFul`
(`Spike/Lib/X64TailNoFul.lean`). The twin of `Spike/Lib/LowerA64/OvfDt.lean`.

- `spill`, `Spilled`: the store's address `-16(%rbp)`, mapped in the private
  memory (so the store is silent; unlike AArch64 the store has no alignment
  check);
- `OvfDt exe endPc lab`: the five tail positions: at the `write`
  (`%rax = 1`, `%rdi = 2`, the spill mapped), at the store (the spill
  mapped), at the two moves, at the exit call (`%rax = 231`);
- `ovfDt_step`: every certification step from `OvfDt` lands in `OvfDt`
  keeping the promises (the `write` resumes past its cell with `%rbp` and
  the private memory unchanged, `syscallRet` writing `%rax`, `%rcx`, `%r11`
  only; the instructions are silent; `exit_group` has no step), off the
  transfer sites (`hns`);
- `ovfDt_of_at`: the stub's `write` node (`At … .sys`) is in `OvfDt`, for a
  region holding the stub's frame `[-24, 16)` (`%rbp` the region's base,
  the spill its cell at `-16`);
- `ovfDt_noSite`: `OvfDt` is off the transfer sites, from the instance's
  facts and the path's phase check (`abortPhOk`);
- `tailNoFul_ovf`: `TailNoFul … (OvfDt …)` from `WrIn`.
-/
import Spike.Lib.X64StubW
import Spike.Lib.X64TailNoFul
import Spike.Bridge.CertC

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt after exec_store_mapped op64)
open Kraken.Promising.Lower (silentTree_done)
open Scc.Sem
open Scc.Sem.X64 (abi pcOf atSyscall_of_cellAt atSyscall_false_of_cellAt mem_certSuccs_syscall)
open Spike.Bridge.CertC (stepC_silent stepC_dead)
open Spike.Lib.X64
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.StubW (abortPhOk phOne syscallCall_write)
open Spike.Lib.X64Consumer (TailNoFul WrIn Inv tailNoFul_of_wrIn)

/-! ## The tail states -/

/-- The address of `-16(%rbp)` (the stub's spill of the `write`'s result). -/
def spill (s : State) : BitVec 64 := slotA (s.st.1.regs.get64 .rbp) (-16)

/-- The spill address is mapped in the private memory. -/
def Spilled (s : State) : Prop := ∃ j, Mem.loadInt s.st.1.dmem (spill s) 8 = some j

/-- **The overflow stub's write tail**: the executable and its end, and one
of the tail's positions: the `write` call (`%rax = 1`, `%rdi = 2`, the
spill mapped), the spill (mapped), the two moves, the exit call
(`%rax = 231`). -/
def OvfDt (exe : _root_.Executable) (endPc : Int64) (lab : Label → Int64) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧
    (s.st.2 = Abort.pcSys lab Abort.overflow ∧ s.st.1.regs.get64 .rax = 1 ∧ s.st.1.regs.get64 .rdi = 2 ∧
        Spilled s ∨
      s.st.2 = lab Abort.overflow.entry + 36 ∧ Spilled s ∨
      s.st.2 = lab Abort.overflow.entry + 40 ∨
      s.st.2 = lab Abort.overflow.entry + 47 ∨
      s.st.2 = lab Abort.overflow.exit ∧ s.st.1.regs.get64 .rax = 231)

/-! ## Closure under certification -/

section Step

variable {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {μ : Marks}

/-- **A certification step from the write tail** stays in it and keeps the
promises, given the stub's code (`hcode`, any source control) and the tail
off the transfer sites (`hns`): the `write` resumes past its cell with
`%rbp` and the private memory unchanged; the spill (mapped) and the two
moves are silent; the `exit_group` call has no step. -/
theorem ovfDt_step {c0 : Ctl} (hcode : Abort.Code Abort.overflow c0 Abort.x1Overflow exe endPc)
    (hlab : (_root_.Executable.labels exe).label = lab)
    (hns : ∀ s, OvfDt exe endPc lab s → Kernel.siteAt abi μ s = none) :
    ∀ x (p q : Thread isa × Memory), OvfDt exe endPc lab p.1.st →
      ThreadStepC Arch.tso (Kernel.certSem abi Arch.tso μ x 0) 0 p q →
        OvfDt exe endPc lab q.1.st ∧ q.1.prom = p.1.prom := by
  subst hlab
  rintro x ⟨t, mem⟩ q hD h
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
    show OvfDt _ _ _ o.thread.st
    rw [← hr]
    refine ⟨he, hn, .inr (.inl ⟨?_, hsp⟩)⟩
    show t.st.st.2 + Int64.ofNat 2 = _
    rw [hpc, Int64.add_assoc]
    rfl
  · -- `movq %rax, -16(%rbp)`: mapped, silent
    have hc := (hcode.n5 t.st he hn).cell (j := 0) rfl rfl rfl (by rw [show Int64.ofNat (cellOff Abort.x2 0) = 0 by decide, Int64.add_zero]; exact hpc)
    obtain ⟨hq, hpr⟩ := hsil hc (by intro _ _ h; cases h)
      (exec_store_mapped hc (eaddr_rbp t.st 4 (-16)) hj)
    refine ⟨?_, hpr⟩
    rw [hq]
    exact ⟨he, hn, .inr (.inr (.inl (by show t.st.st.2 + Int64.ofNat 4 = _; rw [hpc, Int64.add_assoc]; rfl)))⟩
  · -- `movq $101, %rdi`
    have hc := (hcode.n5 t.st he hn).cell (j := 1) rfl rfl rfl (by rw [hpc]; show _ = _ + 36 + _; rw [Int64.add_assoc]; rfl)
    obtain ⟨hq, hpr⟩ := hsil hc (by intro _ _ h; cases h) (exec_reg rfl hc)
    refine ⟨?_, hpr⟩
    rw [hq]
    exact ⟨he, hn, .inr (.inr (.inr (.inl (by show t.st.st.2 + Int64.ofNat 7 = _; rw [hpc, Int64.add_assoc]; rfl))))⟩
  · -- `movl $231, %eax`: at the exit call
    have hc := (hcode.n5 t.st he hn).cell (j := 2) rfl rfl rfl (by rw [hpc]; show _ = _ + 36 + _; rw [Int64.add_assoc]; rfl)
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

/-! ## Entry and sites -/

/-- **The stub's `write` node is in the tail**, for a region holding the
stub's frame `[-24, 16)`: `%rbp` is the region's base (`Abort.oI`) and the
spill is the region's cell at `-16`. -/
theorem ovfDt_of_at {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {R : Region}
    {F : MachineData → Prop} {c0 c : Ctl} {s : State} (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hAt : At exe endPc R F (Abort.N lab Abort.overflow c0 .sys) s c) :
    OvfDt exe endPc lab s := by
  obtain ⟨hs, hn, -, hpc, σ, hA, -, -, h0, ha⟩ := hAt
  have hbp : s.st.1.regs.get64 .rbp = R.addr 0 := by rw [hA.regs]; exact hA.so .rbp 0 rfl
  obtain ⟨j, hj, -⟩ := hA.slot (-16) ⟨by decide, by omega, by omega⟩
  refine ⟨hs, hn, .inl ⟨hpc, by rw [hA.regs]; exact ha, by rw [hA.regs]; exact h0, j, ?_⟩⟩
  unfold spill slotA
  rw [hbp, BitVec.ofInt_add, BitVec.ofInt_toInt, ← Region.addr_add,
    show (0 : Int) + (-16 : Int64).toInt = -16 by decide]
  exact hj

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Spike.Lib.X64Consumer.Own}
  {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The write tail is off the transfer sites**: its instructions are
off-site pcs of the path's phase check (`abortPhOk`: the `write` call's
`phOne`, `Abort.x2`'s `blkPh`), whose `PcOff` the instance gives; the exit
call is off the release and take sites (`hrel`, `htk`). -/
theorem ovfDt_noSite {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hphs : abortPhOk okPc ph lab = true)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a) :
    ∀ s, OvfDt exe endPc lab s → Kernel.siteAt abi μ s = none := by
  simp only [abortPhOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨-, -, -, -, -, -, -, o5, -, pb2, -⟩ := hphs
  have hb : ∀ k, k < 3 →
      okPc (lab Abort.overflow.entry + Int64.ofNat 36 + Int64.ofNat (cellOff Abort.x2 k)).toBitVec.toNat = true := by
    intro k hk
    have := List.all_eq_true.mp pb2 k (List.mem_range.mpr (by simpa [Abort.x2] using hk))
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  rw [show Int64.ofNat (cellOff Abort.x2 0) = 0 by decide, Int64.add_zero, show Int64.ofNat 36 = 36 from rfl] at h0
  rw [Int64.add_assoc, show Int64.ofNat 36 + Int64.ofNat (cellOff Abort.x2 1) = 40 by decide] at h1
  rw [Int64.add_assoc, show Int64.ofNat 36 + Int64.ofNat (cellOff Abort.x2 2) = 47 by decide] at h2
  have hoff : ∀ s : State, okPc (pcOf s) = true → Kernel.siteAt abi μ s = none := fun s h =>
    have hP := (hI.off s h).1
    Kernel.siteAt_eq_none_iff.mpr ⟨fun e => hP.noTake _ e rfl, fun e => hP.noSite _ e rfl⟩
  rintro s ⟨-, -, ⟨hpc, -⟩ | ⟨hpc, -⟩ | hpc | hpc | ⟨hpc, -⟩⟩
  · exact hoff s (by unfold pcOf; rw [hpc]; exact o5)
  · exact hoff s (by unfold pcOf; rw [hpc]; exact h0)
  · exact hoff s (by unfold pcOf; rw [hpc]; exact h1)
  · exact hoff s (by unfold pcOf; rw [hpc]; exact h2)
  · have he : (lab Abort.overflow.exit).toBitVec.toNat = abi.pc s := by
      show _ = s.st.2.toBitVec.toNat
      rw [hpc]
    exact Kernel.siteAt_eq_none_iff.mpr ⟨fun e => htk _ e he, fun e => hrel _ e he⟩

/-- **The consumer's closed tail at the overflow stub**: `WrIn` at `OvfDt`
(`hW`), and `OvfDt` closed under certification (`ovfDt_step`, the stub's
code from `abortIn`, off the sites by `ovfDt_noSite`). -/
theorem tailNoFul_ovf {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hphs : abortPhOk okPc ph lab = true)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    {I : Inv} {Λ : Scc.Sem.Layout} {rS : Range} {Tk' : State → Prop} (hW : WrIn I (OvfDt exe endPc lab)) :
    TailNoFul I Λ rS Tk' μ (OvfDt exe endPc lab) := by
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hcode := Scc.Cert.Rt.X64.Abort.code_stub (c0 := Spike.Lib.X64Consumer.c0) hI.lays hI.endOk hsd.1.1.1.1.1
  exact tailNoFul_of_wrIn hW (ovfDt_step hcode hI.labOk (ovfDt_noSite hI hphs hrel htk))

end Inst

end Spike.Lib.LowerX64
