/-
**Forward kernel steps of a `Solo` thread on the canonical targets**
(`ExtMachine.ofHooks I A (Kernel.hooks K A n)`, any ISA and `Abi`): the
converse direction of `Spike/Lib/ExtThread.lean`'s kernel cases, for the
system calls and the transfer that a start-up path takes.

- `fwd_rtSigaction`: a thread at a system call asking for `rt_sigaction`
  (`callOf`) steps to `Abi.ret … 0`; no event; memory and kernel state
  unchanged.
- `fwd_archSetFs`: `arch_prctl(ARCH_SET_FS, a)` steps to `Abi.ret` of the
  state with thread pointer `a`, returning 0; no event; memory and kernel
  state unchanged.
- `fwd_take`: a thread at the take site (a `nop`) whose argument registers
  name a `fresh` range takes it: its private memory gets the pool's bytes
  there (`copyRange`), the range is held by it and erased from the pool,
  and the thread steps past the `nop` (`Abi.skip`).

Each is stated at `Solo` (`Spike/Lib/X64Fwd.lean`) and gives `Solo` again,
with the other threads unchanged. `ready` comes from `Solo` and the
`atSys` fact (`Kernel.ready_of`); certification from `prom = []`
(`Kernel.certAfter_of_prom`, inside the `KernelStep` lemmas).

Nothing here is specific to a program.
-/
import Spike.Lib.X64Fwd
import Spike.Lib.ExtThread
import Scc.Sem.KernelStep

namespace Spike.Lib.Fwd

open Scc.Sem Kraken Kraken.Promising

variable {I : ISA} {A : Arch} {K : Kernel.Abi I} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat} {μ : Marks}

/-- The other threads are unchanged by replacing thread `tid`. -/
theorem withThread_others {c : Config I} {tid : Nat} {t th : Thread I} {mem : Memory}
    (ht : c.threads[tid]? = some t) : ∀ i, i ≠ tid → (c.withThread tid th mem).threads[i]? = c.threads[i]? := by
  intro i hi
  exact (Config.withThread_get? c th mem (lt_size_of_get? ht)).trans (by simp [Ne.symm hi])

/-- A `Solo` thread at a system call is `ready`. -/
theorem Solo.ready {c : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Cfg} {tid : Nat} {s : I.State}
    {t : Thread I} (h : Solo c tid s) (hst : t.st = s)
    (hs : K.atSys s = true) : Kernel.ready K tid c t = true := by
  refine Kernel.ready_of K (hst ▸ hs) ?_ h.exited
  have := h.running
  simp only [Kernel.hooks, Bool.not_eq_false] at this
  exact this

/-- **`rt_sigaction` returns 0**, as a forward step of a `Solo` thread at a
system call asking for it: no event, memory and kernel state unchanged. -/
theorem fwd_rtSigaction {c : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Cfg} {tid : Nat}
    {s : I.State} (h : Solo c tid s) (hs : K.atSys s = true)
    (hc : Kernel.decode K.nrs (K.nr s) (K.arg s) = some .rtSigaction) :
    ∃ c', (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Step μ tid c [] c' ∧
      Solo c' tid (K.ret s 0) ∧ c'.1.mem = c.1.mem ∧ Keeps tid c c' := by
  obtain ⟨t, ht, rfl, hp, hb⟩ := h.thread
  refine ⟨_, .sys ⟨⟨t, ht⟩, h.exited, h.running⟩
      (Kernel.sys_rtSigaction K A n (μ := μ) ht (h.ready rfl hs) hp hc) (by simp) (by simp) (by simp),
    ⟨⟨_, ExtMachine.withThread_self ht, Kernel.retThread_st (K := K) t 0, by rw [Kernel.retThread_prom, hp],
      ExtThread.bnd_retThread K hb 0⟩, h.exited, h.running⟩, rfl, rfl, withThread_others ht⟩

/-- **`arch_prctl(ARCH_SET_FS, a)` sets the thread pointer and returns 0**,
as a forward step of a `Solo` thread at a system call asking for it: no
event, memory and kernel state unchanged. -/
theorem fwd_archSetFs {c : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Cfg} {tid : Nat}
    {s : I.State} {a : Nat} (h : Solo c tid s) (hs : K.atSys s = true)
    (hc : Kernel.decode K.nrs (K.nr s) (K.arg s) = some (.archSetFs a)) :
    ∃ c', (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Step μ tid c [] c' ∧
      Solo c' tid (K.ret (K.setTp s a) 0) ∧ c'.1.mem = c.1.mem ∧ Keeps tid c c' := by
  obtain ⟨t, ht, rfl, hp, hb⟩ := h.thread
  refine ⟨_, .sys ⟨⟨t, ht⟩, h.exited, h.running⟩
      (Kernel.sys_archSetFs K A n (μ := μ) ht (h.ready rfl hs) hp hc) (by simp) (by simp) (by simp),
    ⟨⟨_, ExtMachine.withThread_self ht, Kernel.retThread_st (K := K) _ 0, by rw [Kernel.retThread_prom]; exact hp,
      ExtThread.bnd_retThread K (t := { t with st := K.setTp t.st a }) ⟨hb.views, hb.regs⟩ 0⟩, h.exited, h.running⟩, rfl, rfl, withThread_others ht⟩

/-- **The take**, as a forward step of a `Solo` thread at the take site (a
`nop`, `pcf s` the resolved take site) whose argument registers name a
`fresh` range `r`: the thread's private memory gets the pool's bytes on `r`
and it steps past the `nop`; `r` becomes held by it and leaves the pool;
memory and the other threads unchanged. -/
theorem fwd_take {c : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Cfg} {tid : Nat}
    {s : I.State} (h : Solo c tid s) (hsite : μ.site .take = some (pcf s)) (hn : K.atNop s = true)
    (hf : Kernel.fresh c (Kernel.siteRange K s) = true) :
    ∃ c', (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Step μ tid c [] c' ∧
      Solo c' tid (K.skip (K.setDmem s (Kernel.copyRange c.2.pmem (K.dmem s) (Kernel.siteRange K s)))) ∧
      c'.1.mem = c.1.mem ∧
      c'.2 = { c.2 with held := (tid, Kernel.siteRange K s) :: c.2.held,
                        pmem := Kernel.eraseRange c.2.pmem (Kernel.siteRange K s) } ∧
      ∀ i, i ≠ tid → c'.1.threads[i]? = c.1.threads[i]? := by
  obtain ⟨t, ht, rfl, hp, hb⟩ := h.thread
  have hr : c.2.runs tid = true := by
    have := h.running
    simp only [Kernel.hooks, Bool.not_eq_false] at this
    exact this
  refine ⟨_, .xfer .take ⟨⟨t, ht⟩, h.exited, h.running⟩ ⟨_, hsite, t, ht, rfl⟩
      (Kernel.xfer_take (K := K) A n ht hr h.exited hn hf),
    ⟨⟨_, ExtMachine.withThread_self ht, rfl, hp, ⟨hb.views, hb.regs⟩⟩, h.exited, h.running⟩, rfl, rfl,
    withThread_others ht⟩

/-- info: 'Spike.Lib.Fwd.fwd_rtSigaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_rtSigaction

/-- info: 'Spike.Lib.Fwd.fwd_archSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_archSetFs

/-- info: 'Spike.Lib.Fwd.fwd_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.Fwd.fwd_take

end Spike.Lib.Fwd
