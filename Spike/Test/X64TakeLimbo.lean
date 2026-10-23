/-
**Certification through the take site (x86-64)**: the counterpart of
`Scc/Test/TakeLimbo.lean` for the emitted x64 `ret0.w` and `hello1.w`
(`SccCode.ret0Asm`, `SccCode.hello1Asm`) on `target (kernel slots)
Entry.linux` under `Arch.tso`.

At the first state of the deterministic run whose thread 0 is at the take
mark (step 202 for both programs):

- under the solo projection of the kernel step (`Kernel.certSem`, fuel 60)
  thread 0 certifies one write, the TCB's self word
  `134217736 := 134217736`, in shared memory and outside the stack pool.
  The set is nonempty, so the projection still lets the thread promise. For
  `ret0` it is the whole set: at fuel 120 the search ends below the bound.
- under the old semantics (`Kernel.certExec`, `certifiedPromisesWith`,
  fuel 60) the set is the same one write: on x64 the old semantics admits
  no stack-pool write at the take mark (the AArch64 one does).
-/
import Scc.Sem.Test.RunX64
import Spike.Lib.X64Ret0Code
import Spike.Lib.X64Hello1Code

namespace Spike.Test.X64TakeLimbo

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Test Scc.Sem.Test.RunX64

/-- The configuration of the deterministic run of `a` at its first state
whose thread 0 is at the take mark, with the layout, the marks and the
number of steps. -/
def atTake (a : Asm) (cells : List (Directive × Nat)) :
    Option (Scc.Sem.Layout × RunMarks × (Kraken.Promising.Config isa × Kernel.KState) × Nat) :=
  let μ := marksIn cells
  let Λ := (layoutIn a cells).1
  ((target (kernel slots) Entry.linux).load a Λ).bind fun c =>
    let r := runUntil abi Arch.tso pcOf μ
      (fun c => c.1.threads[0]?.any fun t => some (pcOf t.st) == μ.take) 4000 0 { cfg := c }
    if r.stop == "condition" then some (Λ, μ, r.cfg, r.steps) else none

/-- The writes thread 0 may promise at the take mark under `Kernel.certSem`
(fuel `fuel`), as (address, value); those outside shared memory; those in
the stack pool; whether the bound was hit; and the step of the mark. -/
def solo (a : Asm) (cells : List (Directive × Nat)) (fuel : Nat) :
    Option (Nat × List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat) × Bool) :=
  (atTake a cells).bind fun (Λ, μ, c, k) =>
    (promisable Arch.tso (Kernel.certSem abi Arch.tso μ.marks c.2 0) c.1 0 fuel).map fun (ws, hit) =>
      (k, ws, ws.filter (fun (a, _) => !(Λ.data.contains a || Λ.heap.contains a || Λ.pinned.contains a)),
        ws.filter (fun (a, _) => Λ.stackPool.contains a), hit)

/-- info: (some (202, [(134217736, 134217736)], [], [], true), some (202, [(134217736, 134217736)], [], [], true)) -/
#guard_msgs in
#eval (solo SccCode.ret0Asm SccCode.ret0Cells 60, solo SccCode.hello1Asm SccCode.hello1Cells 60)

-- The projection is not a dead end at the take site.
#guard [solo SccCode.ret0Asm SccCode.ret0Cells 60, solo SccCode.hello1Asm SccCode.hello1Cells 60].all
  fun r => r.any (0 < ·.2.1.length)

-- `ret0` at fuel 120: the same write, and the search ends below the bound.
#guard (solo SccCode.ret0Asm SccCode.ret0Cells 120).map (fun r => (r.2.1, r.2.2.2.2)) ==
  some ([(134217736, 134217736)], false)

/-- The writes thread 0 may promise at the take mark under the old
`Kernel.certExec` (fuel 60), and those in the stack pool. -/
def old (a : Asm) (cells : List (Directive × Nat)) : Option (List (Nat × Nat) × List (Nat × Nat)) :=
  (atTake a cells).map fun (Λ, _, c, _) =>
    let ws := (certifiedPromisesWith Arch.tso (Kernel.certExec abi) {} c.1 0 60).1.filterMap
      fun (c', _) => c'.mem.msgs.back?.map fun m => (m.loc.addr.toNat, m.val.toNat)
    (ws, ws.filter fun (a, _) => Λ.stackPool.contains a)

/-- info: (some ([(134217736, 134217736)], []), some ([(134217736, 134217736)], [])) -/
#guard_msgs in
#eval (old SccCode.ret0Asm SccCode.ret0Cells, old SccCode.hello1Asm SccCode.hello1Cells)

end Spike.Test.X64TakeLimbo
