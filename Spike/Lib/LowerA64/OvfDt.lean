/-
**The overflow stub's write tail** (AArch64): after the stub's `write`
system call only `str x0, [sp, #8]`, `movz x0, #101`, `movz x8, #94` and the
`exit_group` call follow (`Abort.b2`, `Spike/Lib/A64Abort.lean`), so the
states from the `write` on form a predicate `OvfDt` closed under the
certification steps, keeping the promise set. This discharges the write
tail `Dt` of `stubW_sfacts` (`hwr`) and, through `tailNoFul_of_wrIn`, the
consumer's `TailNoFul` (`Spike/Lib/A64TailNoFul.lean`).

- `spill`, `Sp16`, `Spilled`: the store's address `sp + 8`, `sp` 16-aligned
  (the store's alignment check), the address mapped in the private memory
  (so the store is silent);
- `OvfDt exe endPc lab`: the five tail positions: at the `write` (`x0 = 2`,
  `x8 = 64`, the store's facts), at the store (its facts), at the two
  `movz`, at the exit call (`x8 = 94`);
- `ovfDt_step`: every certification step from `OvfDt` lands in `OvfDt`
  keeping the promises (the `write` resumes past its cell with `sp` and the
  private memory unchanged; the instructions are silent; `exit_group` has
  no step), off the transfer sites (`hns`);
- `ovfDt_of_at`: the stub's `write` node (`At … .svc`) is in `OvfDt`, for a
  16-aligned region holding the stub's frame;
- `ovfDt_noSite`: `OvfDt` is off the transfer sites, from the instance's
  facts and the path's phase check (`abortPhOk`);
- `tailNoFul_ovf`: `TailNoFul … (OvfDt …)` from `WrIn`.
-/
import Spike.Lib.A64StubW
import Spike.Lib.A64TailNoFul
import Spike.Bridge.CertC

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower.A64 (CellAt after exec_str_sp exec_movz)
open Kraken.Promising.Lower (silentTree_done)
open Scc.Sem
open Scc.Sem.A64 (abi pcOf atSvc_of_cellAt atSvc_false_of_cellAt mem_certSuccs_svc)
open Spike.Bridge.CertC (stepC_silent stepC_dead)
open Spike.Lib.A64.Flow
open Spike.Lib.A64
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.StubW (abortPhOk phOne)
open Spike.Lib.A64Consumer (TailNoFul WrIn Inv Own tailNoFul_of_wrIn PcOff)
open Scc.Cert.Rt.A64.Print (add4 add0)

/-! ## The tail states -/

/-- The address of `[sp, #8]` (the stub's spill of the `write`'s result). -/
def spill (s : State) : BitVec 64 := BitVec.ofInt 64 (s.st.1.regs.SP.toBitVec.toInt + (8 : Int64).toInt)

/-- `sp` is 16-aligned. -/
def Sp16 (s : State) : Prop := s.st.1.regs.SP.toBitVec % 16#64 = 0#64

/-- The spill address is mapped in the private memory. -/
def Spilled (s : State) : Prop := ∃ j, Mem.loadInt s.st.1.dmem (spill s) 8 = some j

/-- **The overflow stub's write tail**: the executable and its end, and one
of the tail's positions: the `write` call (`x0 = 2`, `x8 = 64`, `sp`
16-aligned, the spill mapped), the spill (`sp` 16-aligned, the spill
mapped), the two `movz`, the exit call (`x8 = 94`). -/
def OvfDt (exe : _root_.Executable) (endPc : Int64) (lab : Label → Int64) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧
    (s.st.2 = Abort.pcSvc lab Abort.overflow ∧ s.st.1.regs.X0 = 2 ∧ s.st.1.regs.X8 = 64 ∧ Sp16 s ∧ Spilled s ∨
      s.st.2 = Abort.pcSvc lab Abort.overflow + 4 ∧ Sp16 s ∧ Spilled s ∨
      s.st.2 = Abort.pcSvc lab Abort.overflow + 4 + 4 ∨
      s.st.2 = Abort.pcSvc lab Abort.overflow + 4 + 4 + 4 ∨
      s.st.2 = lab Abort.overflow.exit ∧ s.st.1.regs.X8 = 94)

/-! ## Closure under certification -/

section Step

variable {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {μ : Marks}

/-- **A certification step from the write tail** stays in it and keeps the
promises, given the stub's code (`hcode`, any source control) and the tail
off the transfer sites (`hns`): the `write` resumes past its cell with `sp`
and the private memory unchanged; the spill (mapped, aligned) and the two
`movz` are silent; the `exit_group` call has no step. -/
theorem ovfDt_step {c0 : Ctl} (hcode : Abort.Code Abort.overflow c0 Abort.b1Overflow exe endPc)
    (hlab : (_root_.Executable.labels exe).label = lab)
    (hns : ∀ s, OvfDt exe endPc lab s → Kernel.siteAt abi μ s = none) :
    ∀ x (p q : Thread isaLSE2 × Memory), OvfDt exe endPc lab p.1.st →
      ThreadStepC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x 0) 0 p q →
        OvfDt exe endPc lab q.1.st ∧ q.1.prom = p.1.prom := by
  subst hlab
  rintro x ⟨t, mem⟩ q hD h
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
    show OvfDt _ _ _ o.thread.st
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

/-! ## Entry and sites -/

/-- **The stub's `write` node is in the tail**, for a 16-aligned region
holding the stub's 48-byte frame: `sp` is the frame's base (16-aligned)
and the spill is the frame's cell at `-40`. -/
theorem ovfDt_of_at {exe : _root_.Executable} {endPc : Int64} {lab : Label → Int64} {R : Region}
    {F : MachineData → Prop} {c0 c : Ctl} {s : State} (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (hAt : At exe endPc R F (Abort.N lab Abort.overflow c0 .svc) s c) :
    OvfDt exe endPc lab s := by
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

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The write tail is off the transfer sites**: its instructions are
off-site pcs of the path's phase check (`abortPhOk`: the `write` call's
`phOne`, `Abort.b2`'s `blkPh`), whose `PcOff` the instance gives; the exit
call is off the release and take sites (`hrel`, `htk`). -/
theorem ovfDt_noSite {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hphs : abortPhOk okPc ph lab = true)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a) :
    ∀ s, OvfDt exe endPc lab s → Kernel.siteAt abi μ s = none := by
  simp only [abortPhOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨-, -, -, -, -, -, -, -, -, o7, -, pb2, -⟩ := hphs
  have hb : ∀ k, k < 3 → okPc (lab Abort.overflow.entry + Int64.ofNat (4 * 8) + Int64.ofNat (4 * k)).toBitVec.toNat
      = true := by
    intro k hk
    have := List.all_eq_true.mp pb2 k (List.mem_range.mpr (by simpa [Abort.b2] using hk))
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  simp only [add4, add0] at o7 h0 h1 h2
  have hoff : ∀ s : State, okPc (pcOf s) = true → Kernel.siteAt abi μ s = none := fun s h =>
    have hP := (hI.off s h).1
    Kernel.siteAt_eq_none_iff.mpr ⟨fun e => hP.noTake _ e rfl, fun e => hP.noSite _ e rfl⟩
  rintro s ⟨-, -, ⟨hpc, -⟩ | ⟨hpc, -⟩ | hpc | hpc | ⟨hpc, -⟩⟩
  · exact hoff s (by unfold pcOf; rw [hpc]; exact o7)
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
theorem tailNoFul_ovf {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhOk okPc ph lab = true)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    {I : Inv} {Λ : Scc.Sem.Layout} {rS : Range} {Tk' : State → Prop} (hW : WrIn I (OvfDt exe endPc lab)) :
    TailNoFul I Λ rS Tk' μ (OvfDt exe endPc lab) := by
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hcode := Scc.Cert.Rt.A64.Abort.code_stub (c0 := Spike.Lib.A64Consumer.c0) hI.lays hI.endOk hsd.1.1.1.1.1
  exact tailNoFul_of_wrIn hW (ovfDt_step hcode hI.labOk (ovfDt_noSite hI hphs hrel htk))

end Inst

end Spike.Lib.LowerA64
