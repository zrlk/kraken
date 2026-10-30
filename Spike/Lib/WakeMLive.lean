/-
**main's liveness fact after the spawn**: the small module
the kernel-side relation `KR` imports for its liveness conjunct,
without `Spike/Lib/WakeM0.lean`.

- `wlRet`: `waitLoop`'s return of `0`, the term main's source returns at.
- `MainLive k s`: while the process runs (`k.exited = none`), main's source
  (thread 0 of `s`) is not at `wlRet`. A conjunct of `KR w t s` at
  `MainLive t.2 s`; `WakeM0.mainLive_of` reads it.

`exit_group` keeps the thread state and only sets `exited`
(`Kernel.sysStep`), and the source's return is the `exit` event, so only the
kernel state tells main's source before its return from after it.
-/
import Scc.Sem.Kernel
import WeakCore.TermRun

namespace Spike.Lib.WakeMLive

open CoreTerm

/-- `waitLoop`'s return of `0`. -/
def wlRet : Expr := .ret (.lit 0)

/-- **main's source has not returned while the process runs.** -/
def MainLive (k : Scc.Sem.Kernel.KState) (s : TermRun.Cfg) : Prop :=
  k.exited = none → ∀ s0, s.ths[0]? = some s0 → s0.term ≠ wlRet

end Spike.Lib.WakeMLive
