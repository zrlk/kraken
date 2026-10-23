/-
**No promise is certified across `clone`** (x86-64): under
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
take-mark promise sets of `ret0` and `hello1` (`Spike/Test/X64TakeLimbo.lean`) do not change:
their code has no `clone`.
-/
import Scc.Sem.Test.RunX64

namespace Spike.Test.X64CloneCert

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Test Scc.Sem.Test.RunX64

/-- A program: `call` (a system call, `%r9` kept), `movq %rax, val`,
`exit_group(0)`; `val` a shared `.data` word; one byte per instruction
(`unitAsm`). -/
def prog (call : String) : Asm :=
  unitAsm ("\t.text\n\t.globl _start\n_start:\n\tleaq val(%rip), %r9\n" ++ call ++
    "\tsyscall\n\tmovq %rax, (%r9)\n\tmovq $0, %rdi\n\tmovq $231, %rax\n\tsyscall\n" ++
    "\t.data\n\t.p2align 3\nval:\n\t.quad 0\n")

/-- `futex(0, FUTEX_WAKE_PRIVATE, 2)`. -/
def futexWake : String := "\tmovq $0, %rdi\n\tmovq $129, %rsi\n\tmovq $2, %rdx\n\tmovq $202, %rax\n"

/-- `clone(cloneFlags, 0x2000, 0, 0, tls = 0x77)`. -/
def cloneCall : String :=
  "\tmovq $0xd0f00, %rdi\n\tmovq $0x2000, %rsi\n\tmovq $0, %rdx\n\tmovq $0, %r10\n\tmovq $0x77, %r8\n" ++
    "\tmovq $56, %rax\n"

/-- The values thread 0 may promise to `val` at the load of `a` under
`Kernel.certSem` (no transfer sites), and whether the bound was hit. -/
def promised (a : Asm) : Option (List Nat × Bool) :=
  let cells := cellsIn a
  let Λ := (layoutIn a cells).1
  ((target (kernel slots) Entry.linux).load a Λ).bind fun c =>
    (promisable Arch.tso (Kernel.certSem abi Arch.tso (marksIn cells).marks c.2 0) c.1 0 32).map
      fun (ws, hit) => ((ws.filter fun (a, _) => Λ.data.contains a).map (·.2), hit)

/-- info: (some ([2, 1, 0], false), some ([], false)) -/
#guard_msgs in
#eval (promised (prog futexWake), promised (prog cloneCall))

/-- info: "out=\"\" events=[exit 0] stop=exited steps=15 poolMsgs=0" -/
#guard_msgs in
#eval runAsm (prog cloneCall) 100

end Spike.Test.X64CloneCert
