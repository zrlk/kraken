/-
**The canonical hooks, step by step, for any ISA and `Abi`**: the facts a
consumer of a canonical target (`ExtMachine.ofHooks I A (Kernel.hooks K A n)`)
needs about the kernel's steps beyond `Scc/Sem/Kernel.lean` and
`Scc/Sem/SysLink.lean`, extracted from the closed toys
`Spike/Lib/A64ExtToy.lean` and `Spike/Lib/A64ExtToy2.lean`.

- `ready_of`: a thread at a system call, in a running slot of a process
  that has not exited, may take a kernel step.
- **Returns that are always possible** (each with no event and no
  memory effect, the calling thread certified when it has no promise):
  `sys_writeIntr` (a `write` before any byte returns `-EINTR`),
  `sys_futexWait` (`0`), `sys_futexWake` (`0`), `sys_rtSigaction` (`0`),
  `sys_archSetFs` (`0`, the thread pointer set); with `Kernel.sys_exitGroup`
  this is a step at every supported call but `exit` and `clone`.
- `sys_exitGroupAbort`: `exit_group` at the abort status may end the process
  as `abort k`.
- **After the exit** (`exited_progress`, `exited_no_step`): a process that
  has exited has progress (no fault, an outcome) and no step.
-/
import Scc.Sem.Kernel
import Scc.Sem.Target

namespace Scc.Sem.Kernel

open Kraken.Promising

variable {I : ISA} (K : Abi I) {μ : Marks}

/-- **A thread at a system call** in a running slot of a process that has not
exited is `ready`. -/
theorem ready_of {tid : Nat} {c : Config I × KState} {t : Thread I} (hs : K.atSys t.st = true)
    (hr : c.2.runs tid = true) (hx : c.2.exited = none) : ready K tid c t = true := by
  simp [ready, hs, hr, hx]

/-- **A `write` may return `-EINTR` before any byte is out**, with no
event. -/
theorem sys_writeIntr (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I}
    {fd buf len : Nat} (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some (.write fd buf len)) (hj : c.2.wr tid = 0) :
    (hooks K A n).sys μ tid c [] (c.1.withThread tid (retThread K t (neg eintr)) c.1.mem, c.2) :=
  ⟨.ret (neg eintr), by simp [sysStep, ht, hr, hc, hj, back] <;> rfl,
    certAfter_of_prom K (prom_withThread ht hp (by simp [hp]))⟩

/-- **`FUTEX_WAIT` may return `0`**, with no event. -/
theorem sys_futexWait (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some .futexWait) :
    (hooks K A n).sys μ tid c [] (c.1.withThread tid (retThread K t 0) c.1.mem, c.2) :=
  ⟨.ret 0, by simp [sysStep, ht, hr, hc, back, futexWaitRet] <;> rfl,
    certAfter_of_prom K (prom_withThread ht hp (by simp [hp]))⟩

/-- **`FUTEX_WAKE` may return `0`** (no waiter woken), with no event. -/
theorem sys_futexWake (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I} {k : Nat}
    (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some (.futexWake k)) :
    (hooks K A n).sys μ tid c [] (c.1.withThread tid (retThread K t 0) c.1.mem, c.2) :=
  ⟨.ret 0, by simp [sysStep, ht, hr, hc, back] <;> rfl,
    certAfter_of_prom K (prom_withThread ht hp (by simp [hp]))⟩

/-- **`rt_sigaction` returns `0`**, with no event. -/
theorem sys_rtSigaction (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some .rtSigaction) :
    (hooks K A n).sys μ tid c [] (c.1.withThread tid (retThread K t 0) c.1.mem, c.2) :=
  ⟨.ret 0, by simp [sysStep, ht, hr, hc, back] <;> rfl,
    certAfter_of_prom K (prom_withThread ht hp (by simp [hp]))⟩

/-- **`arch_prctl(ARCH_SET_FS, a)` sets the thread pointer and returns `0`**,
with no event. -/
theorem sys_archSetFs (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I} {a : Nat}
    (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some (.archSetFs a)) :
    (hooks K A n).sys μ tid c [] (c.1.withThread tid (retThread K { t with st := K.setTp t.st a } 0) c.1.mem, c.2) :=
  ⟨.ret 0, by simp [sysStep, ht, hr, hc, back] <;> rfl,
    certAfter_of_prom K (prom_withThread ht hp (by simp [hp]))⟩

/-- **`exit_group` at the abort status may end the process as `abort k`**
(`Step.sys` admits it only at the abort site of kind `k`). -/
theorem sys_exitGroupAbort (A : Arch) (n : Nat) {c : Config I × KState} {tid : Nat} {t : Thread I} {v : Nat}
    (k : AbortKind) (ht : c.1.threads[tid]? = some t) (hr : ready K tid c t = true) (hp : t.prom = [])
    (hc : callOf K t = some (.exitGroup v)) (hv : v % 256 = abortStatus) :
    (hooks K A n).sys μ tid c [.abort k] (c.1, { c.2 with exited := some (.abort k) }) :=
  ⟨.abort k, by simp [sysStep, ht, hr, hc, hv] <;> rfl,
    certAfter_of_prom K fun t' h' => by rw [ht] at h'; cases h'; exact hp⟩

/-! ## After the exit -/

variable {A : Arch} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat}

/-- **A process that has exited has progress**: no fault (every fault is of
a running thread of a process that has not exited) and an outcome. -/
theorem exited_progress {μ : Marks} {c : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg}
    {o : Outcome} (hx : c.2.exited = some o) : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Progress μ c := by
  refine ⟨?_, .inl ?_⟩
  · rintro (⟨tid, m, ⟨-, hx', -⟩, -⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, -, -, hx', -⟩))
    · exact absurd (hx'.symm.trans hx) (by simp)
    · unfold faultAt at hf
      split at hf
      · simp [hx] at hf
      · cases hf
    · exact absurd (hx'.symm.trans hx) (by simp)
  · show (match (hooks K A n).exited c.2 with
      | some o => some o
      | none => if c.1.final then some .halted else none).isSome
    rw [show (hooks K A n).exited c.2 = c.2.exited from rfl, hx]; rfl

/-- **A process that has exited takes no step.** -/
theorem exited_no_step {μ : Marks} {c c' : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg}
    {tid : Nat} {es : List Ev} {o : Outcome} (hx : c.2.exited = some o)
    (hs : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Step μ tid c es c') : False := by
  obtain ⟨-, hx', -⟩ := hs.runs
  exact absurd (hx'.symm.trans hx) (by simp)

end Scc.Sem.Kernel
