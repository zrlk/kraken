/-
**The worker's steps after the spawn, case by case** (data in `Spike/Lib/WakeW1.lean`).

- `step1_cases`: a step of thread `tid` of the two-slot canonical machine is
  an instruction off a system call (one `stepOne` outcome, certified), a
  certified promise, a kernel system-call step, a `clone`, or a range
  transfer at a transfer site.
-/
import Spike.Lib.WakeW1

namespace Spike.Lib.WakeW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64

/-- **The cases of a step of thread `tid`** of the two-slot canonical
machine, the thread being `t1`. -/
theorem step1_cases {μ : Marks} {tid : Nat} {t t' : (machine (kernel 2)).Cfg} {es : List Ev}
    {t1 : Thread isaLSE2} (h1 : t.1.threads[tid]? = some t1) (hs : (machine (kernel 2)).Step μ tid t es t') :
    (es = [] ∧ abi.atSys t1.st = false ∧ ∃ outs o, stepOne Arch.armv8 t1 tid t.1.mem = some outs ∧ .ok o ∈ outs ∧
        t' = (t.1.withThread tid o.thread o.mem, t.2) ∧
        CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 tid) tid o.thread o.mem) ∨
      (es = [] ∧ ∃ w : Msg, w.tid = tid ∧
        t' = (t.1.withThread tid (Live.Sem.promThread t1 t.1.mem w) (t.1.mem.append w).1, t.2) ∧
        CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 tid) tid (Live.Sem.promThread t1 t.1.mem w)
          (t.1.mem.append w).1) ∨
      (∃ p, sysStep abi Arch.armv8 tid t p = some (es, t') ∧ CertAfter abi Arch.armv8 μ tid t') ∨
      (es = [] ∧ ∃ j r, spawnStep abi tid t j r = some t') ∨
      (es = [] ∧ ∃ k, (machine (kernel 2)).AtSite μ k t tid ∧ xferStep abi k tid t = some t') := by
  cases hs with
  | instr _ hna _ hstep =>
    have hns : abi.atSys t1.st = false := by
      cases hk : abi.atSys t1.st
      · rfl
      · exact absurd ⟨t1, h1, hk⟩ hna
    rcases hstep with ⟨t', outs, o, ht', hso, ho, hco, rfl⟩ | ⟨t', w, ht', hwt, hc, rfl⟩
    · rw [h1] at ht'; cases ht'
      exact .inl ⟨rfl, hns, outs, o, hso, ho, rfl, hco⟩
    · rw [h1] at ht'; cases ht'
      exact .inr (.inl ⟨rfl, w, hwt, rfl, hc⟩)
  | spawn _ h =>
    obtain ⟨j, r, hsp, -⟩ := h
    exact .inr (.inr (.inr (.inl ⟨rfl, j, r, hsp⟩)))
  | sys _ hsy _ _ _ =>
    obtain ⟨p, hp, hca⟩ := hsy
    exact .inr (.inr (.inl ⟨p, hp, hca⟩))
  | xfer k _ hs h => exact .inr (.inr (.inr (.inr ⟨rfl, k, hs, h⟩)))

end Spike.Lib.WakeW1
