/-
**No promise is certified across `clone`** (AArch64): under
the solo projection of the kernel step (`Kernel.certSem`) `clone` ends a
certifying run, like `exit_group`, while the kernel step itself is unchanged.

The program stores the result of a system call to the shared word `val`,
then exits. At the start, thread 0 may promise that store:

- after `futex` wake (count 2): with each count the kernel model may return,
  `2`, `1`, `0` (certification runs through a system call);
- after `clone`: with nothing. The projection used to admit every child id
  and the refusals `-EAGAIN` and `-ENOMEM`; it now has no branch at `clone`,
  so the search ends there below the bound.

The deterministic run of the same `clone` program on the kernel model
still takes the `clone` (`Kernel.spawnStep`, `Scc/Sem/Test/Run.lean`) and
runs to `exit 0`: the kernel step, and with it progress, is untouched. The
take-mark promise sets of `ret0` and `hello1` (`Scc/Test/TakeLimbo.lean`) do not change:
their code has no `clone`.
-/
import Scc.Sem.Test.RunA64

namespace Spike.Test.A64CloneCert

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Test Scc.Sem.Test.RunA64

/-- A program: `call` (a system call, `x9` kept), `str x0, [val]`,
`exit_group(0)`; `val` a shared `.data` word. -/
def prog (call : String) : String :=
  "\t.text\n\t.globl _start\n_start:\n\tadrp x9, val\n\tadd x9, x9, :lo12:val\n" ++ call ++
    "\tsvc #0\n\tstr x0, [x9]\n\tmovz x0, #0\n\tmovz x8, #94\n\tsvc #0\n\t.data\n\t.p2align 3\nval:\n\t.quad 0\n"

/-- `futex(0, FUTEX_WAKE_PRIVATE, 2)`. -/
def futexWake : String := "\tmovz x0, #0\n\tmovz x1, #129\n\tmovz x2, #2\n\tmovz x8, #98\n"

/-- `clone(cloneFlags, 0x2000, 0, tls = 0x77, 0)`. -/
def cloneCall : String :=
  "\tmovz x0, #0x0f00\n\tmovk x0, #0xd, lsl #16\n\tmovz x1, #0x2000\n\tmovz x2, #0\n\tmovz x3, #0x77\n" ++
    "\tmovz x4, #0\n\tmovz x8, #220\n"

/-- The values thread 0 may promise to `val` at the load of `asm` under
`Kernel.certSem` (no transfer sites), and whether the bound was hit. -/
def promised (asm : String) : Option (List Nat × Bool) :=
  let p := progOf asm
  let Λ := (layoutIn asm p).1
  ((target (kernel slots) Entry.linux).load asm Λ).bind fun c =>
    (promisable Arch.armv8 (Kernel.certSem abi Arch.armv8 (marksIn p).marks c.2 0) c.1 0 32).map
      fun (ws, hit) => ((ws.filter fun (a, _) => Λ.data.contains a).map (·.2), hit)

/-- info: (some ([2, 1, 0], false), some ([], false)) -/
#guard_msgs in
#eval (promised (prog futexWake), promised (prog cloneCall))

/-- info: "out=\"\" events=[exit 0] stop=exited steps=17 poolMsgs=0" -/
#guard_msgs in
#eval runAsm (prog cloneCall) 100

end Spike.Test.A64CloneCert
