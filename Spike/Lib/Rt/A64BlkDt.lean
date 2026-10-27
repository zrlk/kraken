/-
**Certification steps inside covered code** (AArch64): the one-instruction
steps a write tail's closure proof (`ClosedC`, `Spike/Lib/TailDt.lean`) is
made of, at states off the transfer sites (`Kernel.siteAt … = none`). Each
lemma takes a certification step `ThreadStepC A (Kernel.certSem abi A μ x
tid) tid (t, mem) q` and says where `q` is, with the promise set kept:

- `stepC_exec`: at a cell that is not a system call, `q` is the state
  Kraken's `exec` gives;
- `blk_stepC`: at the `k`-th instruction of a covered block (`okBlk`) whose
  machine data is related (`Abs`) to the abstract run of the first `k`
  instructions, `q` is at the run's pc after `k + 1` instructions, related
  to that run, with the memory outside the region unchanged; `blk_stepC_mid`
  (not the last instruction: at the next cell) and `blk_stepC_last` (the
  last: at the run's exit pc, the next block or the branch target);
- `si_stepC`: at an `SI` (`adrp`, `add :lo12:`, `nop`, `msr`);
- `svc_stepC`: at a system call decoding to `call` (not a `clone`), `q` is
  past the cell with `x0` some result of `call`; `Abs.svcRet` relates it;
- `exit_stepC`: an `exit_group` call has no step.
-/
import Spike.Lib.A64Dead
import Spike.Bridge.CertC
import Scc.Sem.CertStep
import Spike.Lib.TailDt

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower.A64 (CellAt after labelAddr)
open Kraken.Promising.Lower (silentTree_done)
open Scc.Sem
open Scc.Sem.A64 (abi atSvc_of_cellAt atSvc_false_of_cellAt mem_certSuccs_svc)
open Spike.Bridge.CertC (stepC_silent stepC_dead)
open Spike.Lib.A64.Flow
open Spike.Lib.A64

section Step

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat} {t : Thread isaLSE2} {mem : Memory}
  {q : Thread isaLSE2 × Memory}

/-- **A silent instruction**: off the sites, at a cell that is not a system
call, a certification step lands where Kraken's `exec` does. -/
theorem stepC_exec {d : Directive} {s' : State} (hsi : Kernel.siteAt abi μ t.st = none) (hc : CellAt t.st d 4)
    (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) (hex : isaLSE2.exec t.st = some (.done s'))
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) : q.1.st = s' ∧ q.1.prom = t.prom := by
  have hce : (Kernel.certSem abi A μ x tid).exec t.st = some (.done s') := by
    show Kernel.soloExec abi A μ x tid t.st = _
    rw [Kernel.soloExec_of_not_atSys abi hsi (atSvc_false_of_cellAt hc hd)]
    exact hex
  obtain ⟨-, hpr, hP⟩ := stepC_silent hce (silentTree_done _) h
  exact ⟨hP, hpr⟩

/-- **One instruction of a covered block**: at the `k`-th instruction
(`hpc`), the machine data related to the abstract run of the first `k`
instructions (`hA`), a certification step goes to the run's pc after
`k + 1` instructions, the machine data related to that run, the memory
outside the region unchanged, the rest of the state and the promises
kept. -/
theorem blk_stepC {R : Region} {lo hi : Int} {blk : List Directive} {am : AM} {lab : Label → Int64}
    (hsi : Kernel.siteAt abi μ t.st = none) (hlab : labA t.st = lab) (hcode : CodeAt t.st am.pc blk)
    (hok : okBlk lo hi am.so blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) {k : Nat} (hk : k < blk.length) (hpc : t.st.st.2 = am.pc + Int64.ofNat (4 * k))
    (hA : Abs R (arun lab (blk.take k) am).so t.st.st.1 (arun lab (blk.take k) am).σ)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ ∃ m', q.1.st = { t.st with st := (m', (arun lab (blk.take (k + 1)) am).pc) } ∧
      Abs R (arun lab (blk.take (k + 1)) am).so m' (arun lab (blk.take (k + 1)) am).σ ∧ DFrame R t.st.st.1 m' := by
  subst hlab
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (labA t.st) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hc : CellAt t.st a.toDir 4 :=
    hcode.cell (j := k) (by rw [List.getElem?_eq_getElem hk, hdir]) rfl rfl hpc
  obtain ⟨m', hex, hA', hD'⟩ := exec_ai haok hR hal hlo hhi hc hreg hA
  have hns : ∀ imm, a.toDir ≠ .instr ⟨.W64, .SVC imm⟩ := by
    cases a <;> intro _ h <;> cases h
    exact absurd (hreg _ _ rfl) (by simp [RegOnly])
  obtain ⟨hq, hpr⟩ := stepC_exec hsi hc hns hex h
  have hpck := arun_pc (labA t.st) hok hk
  have hstep : arun (labA t.st) (blk.take (k + 1)) am =
      ⟨a.tgt (labA t.st) (t.st.st.2 + Int64.ofNat 4) (arun (labA t.st) (blk.take k) am).σ,
       a.so (arun (labA t.st) (blk.take k) am).so,
       a.step (arun (labA t.st) (blk.take k) am).so (t.st.st.2 + Int64.ofNat 4)
        (arun (labA t.st) (blk.take k) am).σ⟩ := by
    rw [arun_take_succ _ hk, dstep, hca]
    simp only [hpck, hpc]
  refine ⟨hpr, m', ?_, ?_, hD'⟩
  · rw [hq, hstep]
  · rw [hstep]; exact hA'

/-- **One instruction of a covered block, not the last**: a certification
step goes to the next cell. -/
theorem blk_stepC_mid {R : Region} {lo hi : Int} {blk : List Directive} {am : AM} {lab : Label → Int64}
    (hsi : Kernel.siteAt abi μ t.st = none) (hlab : labA t.st = lab) (hcode : CodeAt t.st am.pc blk)
    (hok : okBlk lo hi am.so blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) {k : Nat} (hk : k + 1 < blk.length) (hpc : t.st.st.2 = am.pc + Int64.ofNat (4 * k))
    (hA : Abs R (arun lab (blk.take k) am).so t.st.st.1 (arun lab (blk.take k) am).σ)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ ∃ m', q.1.st = { t.st with st := (m', am.pc + Int64.ofNat (4 * (k + 1))) } ∧
      Abs R (arun lab (blk.take (k + 1)) am).so m' (arun lab (blk.take (k + 1)) am).σ ∧ DFrame R t.st.st.1 m' := by
  obtain ⟨hpr, m', hq, hA', hD'⟩ := blk_stepC hsi hlab hcode hok hR hal hlo hhi (by omega) hpc hA h
  refine ⟨hpr, m', ?_, hA', hD'⟩
  rw [hq, arun_pc lab hok hk]

/-- **The last instruction of a covered block**: a certification step goes
to the abstract run's exit pc (the next block, or the branch target), the
machine data related to the whole run. -/
theorem blk_stepC_last {R : Region} {lo hi : Int} {blk : List Directive} {am : AM} {lab : Label → Int64}
    (hsi : Kernel.siteAt abi μ t.st = none) (hlab : labA t.st = lab) (hcode : CodeAt t.st am.pc blk)
    (hok : okBlk lo hi am.so blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) {k : Nat} (hk : k + 1 = blk.length) (hpc : t.st.st.2 = am.pc + Int64.ofNat (4 * k))
    (hA : Abs R (arun lab (blk.take k) am).so t.st.st.1 (arun lab (blk.take k) am).σ)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ ∃ m', q.1.st = { t.st with st := (m', (arun lab blk am).pc) } ∧
      Abs R (arun lab blk am).so m' (arun lab blk am).σ ∧ DFrame R t.st.st.1 m' := by
  have he : blk.take (k + 1) = blk := by rw [hk, List.take_length]
  have := blk_stepC hsi hlab hcode hok hR hal hlo hhi (by omega) hpc hA h
  rw [he] at this
  exact this

/-- **An `SI`**: a certification step goes past the cell with the
registers `SI.regs` (`SI.abs` relates it). -/
theorem si_stepC {si : SI} (hsi : Kernel.siteAt abi μ t.st = none) (hc : CellAt t.st si.toDir 4)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ q.1.st = after t.st 4 { t.st.st.1 with regs := si.regs (labelAddr t.st) t.st.st.1.regs } :=
  (stepC_exec hsi hc (by cases si <;> intro _ h <;> cases h) (exec_si hc) h).symm

/-- **A system call**: at a `svc` decoding to `call` (not a `clone`), a
certification step goes past the cell with `x0` some result of `call`, the
rest of the state and the promises kept. -/
theorem svc_stepC {call : Kernel.Call} (hsi : Kernel.siteAt abi μ t.st = none) (hc : CellAt t.st svcDir 4)
    (hd : svcCall t.st.st.1.regs = some call) (hcl : ∀ st tl, call ≠ .clone st tl)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ ∃ v ∈ Kernel.results call, q.1.st = { t.st with
      st := ({ t.st.st.1 with regs := { t.st.st.1.regs with X0 := UInt64.ofNat v.toNat } },
        t.st.st.2 + Int64.ofNat 4) } := by
  have hat : abi.atSys t.st = true := atSvc_of_cellAt hc
  have hd' : Kernel.decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some call := hd
  obtain ⟨outs, o, hso, ho, rfl⟩ := h
  obtain ⟨-, hpr, hmem⟩ := Kernel.certSem_step_sys hsi hat hd' hcl hso ho
  obtain ⟨v, hv, hr⟩ := (mem_certSuccs_svc hc hd').mp hmem
  refine ⟨hpr, v, hv, ?_⟩
  rw [← hr]

/-- **The relation after a system call** returning `v`: `x0 := v`, its
static offset forgotten. -/
theorem Abs.svcRet {R : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs R o m σ) (v : BitVec 64) :
    Abs R (o.kill .X0) { m with regs := { m.regs with X0 := UInt64.ofNat v.toNat } } (svcStep v σ) := by
  refine ⟨by simp only [svcStep, hA.regs], hA.status, ?_, hA.slot⟩
  refine hA.so.kill .X0 fun r hr => ?_
  rcases r with y | _
  · cases y <;> first | rfl | exact absurd rfl hr
  · rfl

/-- **`exit_group` has no step**: at a `svc` with `x8 = 94`. -/
theorem exit_stepC (hsi : Kernel.siteAt abi μ t.st = none) (hc : CellAt t.st svcDir 4)
    (h8 : t.st.st.1.regs.X8.toNat = 94) : ¬ ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q := by
  have hat : abi.atSys t.st = true := atSvc_of_cellAt hc
  have hd : Kernel.decode abi.nrs (abi.nr t.st) (abi.arg t.st) = some (.exitGroup t.st.st.1.regs.X0.toNat) :=
    svcCall_exitGroup h8
  refine stepC_dead (n := 0) (f := fun i => .done ([] : List isaLSE2.State)[i]) ?_ rfl
  simp only [Kernel.certSem, Kernel.soloExec, hsi, hat, ite_true, hd, Kernel.results, List.filterMap_nil]
  rfl

end Step

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Rt.blk_stepC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blk_stepC

end Spike.Lib.A64.Rt
