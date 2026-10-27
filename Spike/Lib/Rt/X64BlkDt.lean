/-
**Certification steps inside covered code** (x86-64): the one-instruction
steps a write tail's closure proof (`ClosedC`, `Spike/Lib/TailDt.lean`) is
made of, at states off the transfer sites (`Kernel.siteAt … = none`). Each
lemma takes a certification step `ThreadStepC A (Kernel.certSem abi A μ x
tid) tid (t, mem) q` and says where `q` is, with the promise set kept. The
twin of `Spike/Lib/Rt/A64BlkDt.lean`, over `Spike/Lib/X64Block.lean`'s
`exec_ai`, `okBlk`, `arun` (sized cells: a pc is a label plus `cellOff`;
no alignment premise, the x86-64 stores having no alignment check):

- `stepC_exec`: at a cell that is not a `syscall`, `q` is the state Kraken's
  `exec` gives; `stepC_tree` the same for a silent tree of states;
- `blk_stepC`: at the `k`-th instruction of a covered block (`okBlk`) whose
  machine data is related (`Abs`) to the abstract run of the first `k`
  instructions, `q` is at the run's pc after `k + 1` instructions, related
  to that run, with the memory outside the region unchanged; `blk_stepC_mid`
  (not the last instruction: at the next cell) and `blk_stepC_last` (the
  last: at the run's exit pc, the next block or the branch target);
- `si_stepC`: at an `SI` (`leaq L(%rip)`);
- `fi_stepC`: at an `FI` (a flag-writing instruction, `imulq` …): past the
  cell with the registers `FI.regs` and some flags;
- `syscall_stepC`: at a `syscall` decoding to `call` (not a `clone` or an
  `arch_prctl`), `q` is past the cell with `%rax` some result of `call` and
  `%rcx`, `%r11` the return address and the flags (`syscallRegs`);
  `Abs.syscallRet` relates it;
- `exit_stepC`: an `exit_group` call has no step.
-/
import Spike.Lib.X64Dead
import Spike.Lib.X64Flags
import Spike.Bridge.CertC
import Scc.Sem.CertStep
import Spike.Lib.TailDt

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem
open Scc.Sem.X64 (abi atSyscall_of_cellAt atSyscall_false_of_cellAt mem_certSuccs_syscall)
open Spike.Bridge.CertC (stepC_silent stepC_dead)
open Spike.Lib.X64

section Step

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat} {t : Thread isa} {mem : Memory}
  {q : Thread isa × Memory}

/-- **A silent tree**: off the sites, at a cell that is not a `syscall`
where Kraken's `exec` gives a silent tree of states in `P`, a certification
step lands in `P`. -/
theorem stepC_tree {d : Directive} {z : Nat} {tr : EvTree State} {P : State → Prop}
    (hsi : Kernel.siteAt abi μ t.st = none) (hc : CellAt t.st d z)
    (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) (hex : isa.exec t.st = some tr) (hs : SilentTree P tr)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) : P q.1.st ∧ q.1.prom = t.prom := by
  have hce : (Kernel.certSem abi A μ x tid).exec t.st = some tr := by
    show Kernel.soloExec abi A μ x tid t.st = _
    rw [Kernel.soloExec_of_not_atSys abi hsi (atSyscall_false_of_cellAt hc hd)]
    exact hex
  obtain ⟨-, hpr, hP⟩ := stepC_silent hce hs h
  exact ⟨hP, hpr⟩

/-- **A silent instruction**: off the sites, at a cell that is not a
`syscall`, a certification step lands where Kraken's `exec` does. -/
theorem stepC_exec {d : Directive} {z : Nat} {s' : State} (hsi : Kernel.siteAt abi μ t.st = none)
    (hc : CellAt t.st d z) (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall))
    (hex : isa.exec t.st = some (.done s'))
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) : q.1.st = s' ∧ q.1.prom = t.prom :=
  stepC_tree hsi hc hd hex (silentTree_done _) h

/-- A covered instruction is not a `syscall`. -/
theorem AI.toDir_ne_syscall {a : AI} (hreg : ∀ w op, a = .reg w op → RegOnly op = true) :
    ∀ w w', a.toDir ≠ .instr (.regular w w' .syscall) := by
  cases a <;> intro _ _ h <;> cases h
  exact absurd (hreg _ _ rfl) (by simp [RegOnly])

/-- **One instruction of a covered block**: at the `k`-th instruction
(`hpc`), the machine data related to the abstract run of the first `k`
instructions (`hA`), a certification step goes to the run's pc after
`k + 1` instructions, the machine data related to that run, the memory
outside the region unchanged, the rest of the state and the promises
kept. -/
theorem blk_stepC {R : Region} {lo hi : Int} {blk : List (Directive × Nat)} {am : AM} {lab : Label → Int64}
    (hsi : Kernel.siteAt abi μ t.st = none) (hlab : labelAddr t.st = lab) (hcode : CodeAt t.st am.pc blk)
    (hok : okBlk lo hi am.so blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) {k : Nat}
    (hk : k < blk.length) (hpc : t.st.st.2 = am.pc + Int64.ofNat (cellOff blk k))
    (hA : Abs R (arun lab (blk.take k) am).so t.st.st.1 (arun lab (blk.take k) am).σ)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ ∃ m', q.1.st = { t.st with st := (m', (arun lab (blk.take (k + 1)) am).pc) } ∧
      Abs R (arun lab (blk.take (k + 1)) am).so m' (arun lab (blk.take (k + 1)) am).σ ∧
        DFrame R t.st.st.1 m' := by
  subst hlab
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (labelAddr t.st) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hc : CellAt t.st a.toDir blk[k].2 :=
    hcode.cell (j := k) (by rw [List.getElem?_eq_getElem hk, ← hdir]) rfl rfl hpc
  obtain ⟨m', hex, hA', hD'⟩ := exec_ai haok hR hlo hhi hc hreg hA
  obtain ⟨hq, hpr⟩ := stepC_exec hsi hc (AI.toDir_ne_syscall hreg) hex h
  have hpck := arun_pc (labelAddr t.st) hok hk
  have hstep : arun (labelAddr t.st) (blk.take (k + 1)) am =
      ⟨a.tgt (labelAddr t.st) (arun (labelAddr t.st) (blk.take k) am).so (t.st.st.2 + Int64.ofNat blk[k].2)
        (arun (labelAddr t.st) (blk.take k) am).σ,
       a.so (arun (labelAddr t.st) (blk.take k) am).so,
       a.step (arun (labelAddr t.st) (blk.take k) am).so (t.st.st.2 + Int64.ofNat blk[k].2)
        (arun (labelAddr t.st) (blk.take k) am).σ⟩ := by
    rw [arun_take_succ _ hk]
    show dstep _ _ (blk[k].1, blk[k].2) = _
    simp only [dstep, hca, hpck, hpc]
  refine ⟨hpr, m', ?_, ?_, hD'⟩
  · rw [hq, hstep]
  · rw [hstep]; exact hA'

/-- **One instruction of a covered block, not the last**: a certification
step goes to the next cell. -/
theorem blk_stepC_mid {R : Region} {lo hi : Int} {blk : List (Directive × Nat)} {am : AM} {lab : Label → Int64}
    (hsi : Kernel.siteAt abi μ t.st = none) (hlab : labelAddr t.st = lab) (hcode : CodeAt t.st am.pc blk)
    (hok : okBlk lo hi am.so blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) {k : Nat}
    (hk : k + 1 < blk.length) (hpc : t.st.st.2 = am.pc + Int64.ofNat (cellOff blk k))
    (hA : Abs R (arun lab (blk.take k) am).so t.st.st.1 (arun lab (blk.take k) am).σ)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ ∃ m', q.1.st = { t.st with st := (m', am.pc + Int64.ofNat (cellOff blk (k + 1))) } ∧
      Abs R (arun lab (blk.take (k + 1)) am).so m' (arun lab (blk.take (k + 1)) am).σ ∧
        DFrame R t.st.st.1 m' := by
  obtain ⟨hpr, m', hq, hA', hD'⟩ := blk_stepC hsi hlab hcode hok hR hlo hhi (by omega) hpc hA h
  refine ⟨hpr, m', ?_, hA', hD'⟩
  rw [hq, arun_pc lab hok hk]

/-- **The last instruction of a covered block**: a certification step goes
to the abstract run's exit pc (the next block, or the branch target), the
machine data related to the whole run. -/
theorem blk_stepC_last {R : Region} {lo hi : Int} {blk : List (Directive × Nat)} {am : AM} {lab : Label → Int64}
    (hsi : Kernel.siteAt abi μ t.st = none) (hlab : labelAddr t.st = lab) (hcode : CodeAt t.st am.pc blk)
    (hok : okBlk lo hi am.so blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) {k : Nat}
    (hk : k + 1 = blk.length) (hpc : t.st.st.2 = am.pc + Int64.ofNat (cellOff blk k))
    (hA : Abs R (arun lab (blk.take k) am).so t.st.st.1 (arun lab (blk.take k) am).σ)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ ∃ m', q.1.st = { t.st with st := (m', (arun lab blk am).pc) } ∧
      Abs R (arun lab blk am).so m' (arun lab blk am).σ ∧ DFrame R t.st.st.1 m' := by
  have he : blk.take (k + 1) = blk := by rw [hk, List.take_length]
  have := blk_stepC hsi hlab hcode hok hR hlo hhi (by omega) hpc hA h
  rw [he] at this
  exact this

/-- **An `SI`**: a certification step goes past the cell with the
registers `SI.regs` (`SI.abs` relates it). -/
theorem si_stepC {si : SI} {z : Nat} (hsi : Kernel.siteAt abi μ t.st = none) (hc : CellAt t.st si.toDir z)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧
      q.1.st = after t.st z { t.st.st.1 with regs := si.regs (labelAddr t.st) t.st.st.1.regs } :=
  (stepC_exec hsi hc (by cases si <;> intro _ _ h <;> cases h) (exec_si hc) h).symm

/-- **An `FI`**: a certification step goes past the cell with the
registers `FI.regs` and some flags. -/
theorem fi_stepC {fi : FI} {z : Nat} (hsi : Kernel.siteAt abi μ t.st = none) (hc : CellAt t.st fi.toDir z)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ ∃ fl, q.1.st = after t.st z (fi.post t.st.st.1 fl) := by
  obtain ⟨tr, hex, hs⟩ := exec_fi hc
  obtain ⟨hP, hpr⟩ := stepC_tree hsi hc (by cases fi <;> intro _ _ h <;> cases h) hex hs h
  exact ⟨hpr, hP⟩

/-- **A system call**: at a `syscall` decoding to `call` (not a `clone`, not
an `arch_prctl`), a certification step goes past the cell with `%rax` some
result of `call`, `%rcx` the return address and `%r11` the flags, the rest
of the state and the promises kept. -/
theorem syscall_stepC {call : Kernel.Call} {z : Nat} (hsi : Kernel.siteAt abi μ t.st = none)
    (hc : CellAt t.st (op64 .syscall) z) (hd : syscallCall t.st.st.1.regs = some call)
    (hna : ∀ a, call ≠ .archSetFs a) (hcl : ∀ st tl, call ≠ .clone st tl)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ ∃ v ∈ Kernel.results call, q.1.st = { t.st with st := (
      { t.st.st.1 with
        regs := syscallRegs (t.st.st.2 + Int64.ofNat z) (Scc.Sem.X64.rflags t.st.st.1.status) v t.st.st.1.regs },
      t.st.st.2 + Int64.ofNat z) } := by
  have hat : abi.atSys t.st = true := atSyscall_of_cellAt hc
  have hd' : Kernel.decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some call := hd
  obtain ⟨outs, o, hso, ho, rfl⟩ := h
  obtain ⟨-, hpr, hmem⟩ := Kernel.certSem_step_sys hsi hat hd' hcl hso ho
  obtain ⟨v, hv, hr⟩ := (mem_certSuccs_syscall hc hna).mp hmem
  refine ⟨hpr, v, hv, ?_⟩
  rw [← hr]
  simp only [syscallRet, after, Scc.Sem.X64.kret, syscallRegs]
  rfl

/-- **The relation after a system call** returning `v`, `nx` the next pc:
`%rax`, `%rcx`, `%r11` written, their static offsets forgotten. -/
theorem Abs.syscallRet {R : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs R o m σ) (nx : Int64)
    (v : BitVec 64) :
    Abs R (syscallSO o) { m with regs := syscallRegs nx (Scc.Sem.X64.rflags m.status) v m.regs }
      (syscallStep nx v σ) := by
  refine ⟨by simp only [syscallStep, hA.regs, hA.status], hA.zmms, hA.status, ?_, hA.slot⟩
  exact syscallSO_rel hA.so _ _ _

/-- **`exit_group` has no step**: at a `syscall` with `%rax = 231`. -/
theorem exit_stepC {z : Nat} (hsi : Kernel.siteAt abi μ t.st = none) (hc : CellAt t.st (op64 .syscall) z)
    (hx : t.st.st.1.regs.rax.toNat = 231) : ¬ ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q := by
  have hat : abi.atSys t.st = true := atSyscall_of_cellAt hc
  have hd : Kernel.decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some (.exitGroup t.st.st.1.regs.rdi.toNat) :=
    syscallCall_exitGroup hx
  refine stepC_dead (n := 0) (f := fun i => .done ([] : List isa.State)[i]) ?_ rfl
  simp only [Kernel.certSem, Kernel.soloExec, hsi, hat, ite_true, hd, Kernel.results, List.filterMap_nil]
  rfl

end Step

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.blk_stepC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blk_stepC

end Spike.Lib.X64.Rt
