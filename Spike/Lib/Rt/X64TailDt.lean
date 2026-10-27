/-
**Pieces of a write tail** (x86-64): predicates of states, each closed or
stepping into the next piece under the certification steps
(`ClosedC`, `StepsTo`, `Spike/Lib/TailDt.lean`), from which a program's
write tail `Dt` is assembled back to front (`ClosedC.rel`). A piece carries
only the state: its executable, a pc, and the machine data related (`Abs`)
to an abstract state, with a frame condition `C` on the machine data that
no write inside the piece's region breaks (`FStable`).

- `BlkSt exe endPc R pc o blk J C`: inside the covered block `blk` at `pc`
  (static offsets `o`), at some instruction `k`, the machine data related
  to the abstract run of the first `k` instructions from an abstract state
  of `J`, and `C`; `blkSt_steps`: a step stays in the block or lands at the
  run's exit (`hland`), given the block's code, its `okBlk` and the piece
  off the transfer sites (`hns`);
- `SysSt exe endPc pc z P`: at a `syscall` cell of `z` bytes at `pc`, in
  `P`; `sysSt_steps`: the call (decoded from `P`, not a `clone` or an
  `arch_prctl`) resumes in the target (`hland`, for every result);
- `ExitSt exe endPc pc z`: at an `exit_group` call (`%rax = 231`);
  `exitSt_closed`: no step;
- `abs_enter`, `abs_leave`: the relation across a call's region change
  (`at_enter`, `at_leave` of `Spike/Lib/X64Call.lean` over `Abs` and the
  caller's kept cells `CKept` instead of `At`).
-/
import Spike.Lib.Rt.X64BlkDt
import Spike.Lib.X64Call

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem
open Scc.Sem.X64 (abi)
open Spike.Lib.X64
open Spike.Lib (ClosedC StepsTo)

/-! ## Inside a covered block -/

/-- **Inside the covered block `blk` at `pc`** (static offsets `o` at its
entry, region `R`): at the `k`-th instruction, the machine data related to
the abstract run of the first `k` instructions from an abstract state of
`J`, and the frame condition `C`. -/
def BlkSt (exe : _root_.Executable) (endPc : Int64) (R : Region) (pc : Int64) (o : SO)
    (blk : List (Directive × Nat)) (J : AS → Prop) (C : MachineData → Prop) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ ∃ k < blk.length, s.st.2 = pc + Int64.ofNat (cellOff blk k) ∧
    ∃ σ0, J σ0 ∧
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, o, σ0⟩).so s.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, o, σ0⟩).σ ∧ C s.st.1

/-- **The block's entry is in the piece.** -/
theorem blkSt_entry {exe : _root_.Executable} {endPc : Int64} {R : Region} {pc : Int64} {o : SO}
    {blk : List (Directive × Nat)} {J : AS → Prop} {C : MachineData → Prop} {s : State} {σ0 : AS}
    (hne : 0 < blk.length) (he : s.exe = exe) (hn : s.endPc = endPc) (hpc : s.st.2 = pc) (hJ : J σ0)
    (hA : Abs R o s.st.1 σ0) (hC : C s.st.1) : BlkSt exe endPc R pc o blk J C s :=
  ⟨he, hn, 0, hne, by rw [hpc, cellOff_zero, show Int64.ofNat 0 = 0 from rfl, Int64.add_zero], σ0, hJ,
    by simpa [arun] using hA, hC⟩

section Steps

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}

/-- **A step inside a covered block** stays in the block or lands at the
abstract run's exit: in `Tgt` for every machine data related to the whole
run and in `C` (`hland`), given the block's code (`hcode`), its `okBlk`,
the region's facts, `C` kept by writes inside the region (`hC`) and the
piece off the transfer sites (`hns`). -/
theorem blkSt_steps {exe : _root_.Executable} {endPc : Int64} {R : Region} {pc : Int64} {o : SO}
    {blk : List (Directive × Nat)} {J : AS → Prop} {C : MachineData → Prop} {Tgt : State → Prop} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc blk) (hok : okBlk lo hi o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hC : FStable R C)
    (hns : ∀ s, BlkSt exe endPc R pc o blk J C s → Kernel.siteAt abi μ s = none)
    (hland : ∀ σ0, J σ0 → ∀ (s : State) m, s.exe = exe → s.endPc = endPc →
      Abs R (arun (_root_.Executable.labels exe).label blk ⟨pc, o, σ0⟩).so m
        (arun (_root_.Executable.labels exe).label blk ⟨pc, o, σ0⟩).σ → C m →
      Tgt { s with st := (m, (arun (_root_.Executable.labels exe).label blk ⟨pc, o, σ0⟩).pc) }) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid (BlkSt exe endPc R pc o blk J C) Tgt := by
  rintro ⟨t, mem⟩ q hD h
  have hsi := hns _ hD
  obtain ⟨he, hn, k, hk, hpc, σ0, hJ, hA, hCm⟩ := hD
  have hlab : labelAddr t.st = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels t.st.exe).label L = _; rw [he]
  have hc := hcode t.st he hn
  by_cases hk1 : k + 1 < blk.length
  · obtain ⟨hpr, m', hq, hA', hD'⟩ :=
      blk_stepC_mid (am := ⟨pc, o, σ0⟩) hsi hlab hc hok hR hlo hhi hk1 hpc hA h
    refine ⟨.inl ?_, hpr⟩
    rw [hq]
    exact ⟨he, hn, k + 1, hk1, rfl, σ0, hJ, hA', hC _ _ hCm hD'⟩
  · obtain ⟨hpr, m', hq, hA', hD'⟩ :=
      blk_stepC_last (am := ⟨pc, o, σ0⟩) hsi hlab hc hok hR hlo hhi (by omega) hpc hA h
    refine ⟨.inr ?_, hpr⟩
    rw [hq]
    exact hland σ0 hJ t.st m' he hn hA' (hC _ _ hCm hD')

end Steps

/-! ## A system call, and the exit -/

/-- **At a `syscall` cell** of `z` bytes at `pc`, in `P`. -/
def SysSt (exe : _root_.Executable) (endPc : Int64) (pc : Int64) (P : State → Prop) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ s.st.2 = pc ∧ P s

/-- **At the `exit_group` call** at `pc` (`%rax = 231`). -/
def ExitSt (exe : _root_.Executable) (endPc : Int64) (pc : Int64) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ s.st.2 = pc ∧ s.st.1.regs.get64 .rax = 231

section Sys

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}

/-- **A system call resumes in the target**: from `P` the call decodes to
`call s` (not a `clone`, not an `arch_prctl`), and for every result `v`
the state past the cell (`syscallRegs`) is in `Tgt` (`hland`), given the
cell (`hcode`) and the piece off the transfer sites (`hns`). -/
theorem sysSt_steps {exe : _root_.Executable} {endPc : Int64} {pc : Int64} {z : Nat} {P Tgt : State → Prop}
    {call : State → Kernel.Call}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc [(op64 .syscall, z)])
    (hns : ∀ s, SysSt exe endPc pc P s → Kernel.siteAt abi μ s = none)
    (hd : ∀ s, P s → syscallCall s.st.1.regs = some (call s))
    (hna : ∀ s, P s → ∀ a, call s ≠ .archSetFs a) (hcl : ∀ s, P s → ∀ st tl, call s ≠ .clone st tl)
    (hland : ∀ s, s.exe = exe → s.endPc = endPc → s.st.2 = pc → P s → ∀ v ∈ Kernel.results (call s),
      Tgt { s with st := ({ s.st.1 with
        regs := syscallRegs (pc + Int64.ofNat z) (Scc.Sem.X64.rflags s.st.1.status) v s.st.1.regs },
        pc + Int64.ofNat z) }) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid (SysSt exe endPc pc P) Tgt := by
  refine StepsTo.of_into fun ⟨t, mem⟩ q hD h => ?_
  have hsi := hns _ hD
  obtain ⟨he, hn, hpc, hP⟩ := hD
  have hc : CellAt t.st (op64 .syscall) z := (hcode t.st he hn).cell0 rfl rfl hpc
  obtain ⟨hpr, v, hv, hq⟩ := syscall_stepC hsi hc (hd _ hP) (hna _ hP) (hcl _ hP) h
  refine ⟨?_, hpr⟩
  rw [hq, hpc]
  exact hland t.st he hn hpc hP v hv

/-- **The exit call has no step**, given its cell and the piece off the
transfer sites. -/
theorem exitSt_closed {exe : _root_.Executable} {endPc : Int64} {pc : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc [(op64 .syscall, z)])
    (hns : ∀ s, ExitSt exe endPc pc s → Kernel.siteAt abi μ s = none) :
    ClosedC A (Kernel.certSem abi A μ x tid) tid (ExitSt exe endPc pc) := by
  rintro ⟨t, mem⟩ q hD h
  have hsi := hns _ hD
  obtain ⟨he, hn, hpc, h231⟩ := hD
  have hc : CellAt t.st (op64 .syscall) z := (hcode t.st he hn).cell0 rfl rfl hpc
  have hx : t.st.st.1.regs.rax.toNat = 231 := by
    simp only [Reg64s.get64] at h231
    rw [← UInt64.toNat_toBitVec, h231]; rfl
  exact (exit_stepC hsi hc hx h).elim

end Sys

/-! ## Across a call -/

/-- **Entering the callee's region** at `kb`, over `Abs`: machine data
related to `σC` at offsets `o` in the caller's region (`%rsp` at `o.sp`, so
`kb = o.sp - e0`) is related to the entered state at `⟨e0, []⟩` in the
callee's region. -/
theorem abs_enter {R : Region} {o : SO} {m : MachineData} {σC : AS} {e0 lo' hi' : Int}
    (hlo : R.lo ≤ o.sp - e0 + lo') (hhi : o.sp - e0 + hi' ≤ R.hi) (hk8 : (o.sp - e0) % 8 = 0)
    (ho : o.regs = []) (hA : Abs R o m σC) :
    Abs (R.callee (o.sp - e0) lo' hi') ⟨e0, []⟩ m (enter (o.sp - e0) σC) := by
  refine ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩
  · intro r k' hr
    obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
    have := hA.so .rsp o.sp (by obtain ⟨sp, rs⟩ := o; cases ho; simp [SO.get])
    simp only [enter] at this ⊢
    rw [this, Region.callee_addr]; congr 1; omega
  · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo hhi hk8 hk)
    exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

/-- **Leaving the callee's region** at `kb`, over `Abs`: machine data
related to `σx` at `⟨e, []⟩` in the callee's region, the caller's cells
outside it as in `m0` (`CKept`) related to `σC`, is related to the state
the caller's left (`leave`) at `⟨kb + e, []⟩` in the caller's region. -/
theorem abs_leave {R : Region} {kb lo' hi' e : Int} {o : SO} {m m0 : MachineData} {σx σC : AS}
    (hAx : Abs (R.callee kb lo' hi') ⟨e, []⟩ m σx) (hK : CKept R kb lo' hi' m0 m) (hAC : Abs R o m0 σC) :
    Abs R ⟨kb + e, []⟩ m (leave (R.callee kb lo' hi') kb σC σx) := by
  refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
  · intro r k' hr
    obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
    have := hAx.so .rsp e (by simp [SO.get])
    simp only [leave] at this ⊢
    rw [this, Region.callee_addr]
  · by_cases hin : (R.callee kb lo' hi').Off (k - kb)
    · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
      refine ⟨j, ?_, ?_⟩
      · rw [Region.callee_addr, show kb + (k - kb) = k by omega] at hj; exact hj
      · simp only [leave]; rw [ite_eq_left hin]; exact hv
    · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
      refine ⟨j, ?_, ?_⟩
      · rw [hK k hk hin]; exact hj
      · simp only [leave]; rw [ite_eq_right hin]; exact hv

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.blkSt_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkSt_steps

end Spike.Lib.X64.Rt
