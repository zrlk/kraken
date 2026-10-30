/-
**Certification steps at a fence** (AArch64): `Spike/Lib/Rt/A64BlkDt.lean`'s
one-instruction steps for a barrier `dmb <opt>` (its event tree one fence
then a leaf, `exec_dmb`), and `Spike/Lib/Rt/A64TailDt.lean`'s tail points
across one (the write block of `scc_rt_print` is led by `dmb ish`).

- `stepC_fence`: a certification step at a fence-then-leaf tree keeps the
  memory and the promises and ends at the leaf (`stepC_silent`'s
  counterpart; only the views move, `Spike/Lib/FenceStep.lean`);
- `dmb_stepC`: at a `dmb` cell off the transfer sites, a certification step
  goes past the cell, the machine data unchanged;
- `fence_steps`: a tail point at a `dmb` steps to the tail point one
  instruction on, the same offsets and abstract states.
-/
import Spike.Lib.Rt.A64TailDt
import Spike.Lib.FenceStep

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower.A64 (CellAt after exec_dmb)
open Kraken.Promising.Lower
open Scc.Sem
open Scc.Sem.A64 (abi atSvc_false_of_cellAt)
open Spike.Lib.A64.Flow
open Spike.Lib (StepsTo)
open Scc.Cert.Rt.A64.Print (add0)

/-- **A certification step at a fence-then-leaf tree**: the memory and the
promises stay, the thread is at the leaf. -/
theorem stepC_fence {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat} {t : Thread I} {mem : Memory}
    {q : Thread I × Memory} {k : FenceKind} {s' : I.State}
    (hex : cs.exec t.st = some (.fence k fun _ => .done s')) (h : ThreadStepC A cs tid (t, mem) q) :
    q.2 = mem ∧ q.1.prom = t.prom ∧ q.1.st = s' := by
  obtain ⟨outs, o, hso, ho, rfl⟩ := h
  simp only [CertSem.step, stepOneWithD, hex, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hso
  subst hso
  rw [List.mem_flatMap] at ho
  obtain ⟨x, hx, ho⟩ := ho
  rw [Spike.Lib.FenceStep.run_fence, List.mem_singleton] at hx
  subst hx
  simp only [List.mem_map, Except.ok.injEq] at ho
  obtain ⟨th, hth, rfl⟩ := ho
  refine ⟨by simp, ?_, finishInstr_st hth⟩
  rw [(finishInstr_relKey hth).1]
  simp

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}

/-- **A barrier** `dmb <opt>` (off the transfer sites): a certification step
goes past the cell, the machine data and the promises kept. -/
theorem dmb_stepC {t : Thread isaLSE2} {mem : Memory} {q : Thread isaLSE2 × Memory} {k : FenceKind}
    (hsi : Kernel.siteAt abi μ t.st = none) (hc : CellAt t.st (.instr ⟨.W64, .DMB k⟩) 4)
    (h : ThreadStepC A (Kernel.certSem abi A μ x tid) tid (t, mem) q) :
    q.1.prom = t.prom ∧ q.1.st = after t.st 4 t.st.st.1 := by
  have hce : (Kernel.certSem abi A μ x tid).exec t.st = some (.fence k fun _ => .done (after t.st 4 t.st.st.1)) := by
    show Kernel.soloExec abi A μ x tid t.st = _
    rw [Kernel.soloExec_of_not_atSys abi hsi (atSvc_false_of_cellAt hc (by intro _ h; cases h))]
    exact exec_dmb hc
  obtain ⟨-, hpr, hst⟩ := stepC_fence hce h
  exact ⟨hpr, hst⟩

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {C : MachineData → Prop} {pc : Int64} {o : SO}
  {J : Flow.AS → Prop}

/-- **A tail point at a barrier** (off the transfer sites, `hns`) steps to
the point one instruction on, the offsets and abstract states kept. -/
theorem fence_steps {k : FenceKind}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc [.instr ⟨.W64, .DMB k⟩])
    (hns : ∀ s, Pt exe endPc R C pc o J s → Kernel.siteAt abi μ s = none) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid (Pt exe endPc R C pc o J) (Pt exe endPc R C (pc + 4) o J) := by
  refine StepsTo.of_into fun ⟨t, mem⟩ q hD h => ?_
  have hsi := hns _ hD
  obtain ⟨he, hn, hd, hpc, σ, hJ, hA, hC⟩ := hD
  have hc := (hcode t.st he hn).cell (j := 0) rfl rfl rfl (by rw [add0]; exact hpc)
  obtain ⟨hpr, hq⟩ := dmb_stepC hsi hc h
  refine ⟨?_, hpr⟩
  rw [hq]
  exact ⟨he, hn, hd, by show t.st.st.2 + Int64.ofNat 4 = _; rw [hpc]; rfl, σ, hJ, hA, hC⟩

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Rt.fence_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fence_steps

end Spike.Lib.A64.Rt
