import Scc.Cert.Rt.WideX64
import Scc.Test.AllocOrderX64

/-!
# The one-word x86-64 fragment on scc's listings

`Scc/Cert/Rt/WideX64.lean`: `wideIn` holds of the parsed x86-64 listing of
`Scc/Test/hello1.w` and `Scc/Test/hello.w` (every memory write is `movq`,
`pushq`, `call`, `lock xaddq` or `xchgq`), so the certification semantics of
its canonical thread writes words only (`wideSt_threadAt`, `certExec_w8`).
Narrower memory writes, vector stores and `cmpxchg16b` are refused.
-/

namespace Scc.Test.WideX64

open Scc.Cert.WideX64 Scc.Sem.X64

/-- `wideIn` of the parsed listing; `none` if it does not parse. -/
def wideOf (asm : String) : Option Bool := (textProgram asm).toOption.map wideIn

#guard Scc.Test.AllocOrderX64.hello1 != "" && Scc.Test.AllocOrderX64.hello != ""
#guard wideOf Scc.Test.AllocOrderX64.hello1 = some true
#guard wideOf Scc.Test.AllocOrderX64.hello = some true

-- The fragment's memory writes, and narrow loads and register writes.
#guard ["movq %rax, (%rbx)", "movq %rax, 8(%rsp)", "movq $1, (%rbx)", "pushq %rax", "call f",
  "lock xaddq %rax, (%rbx)", "xchgq %rax, (%rbx)", "lock cmpxchgq %rcx, (%rbx)", "lock addq $1, (%rbx)",
  "movl (%rbx), %eax", "movzbl (%rbx), %eax", "movl $1, %eax", "addl (%rbx), %eax",
  "sete %al", "movdqu (%rbx), %xmm0"].all fun l => wideOf l = some true

-- Every narrower memory write, vector store and `cmpxchg16b` is refused.
#guard ["movb %al, (%rbx)", "movw %ax, (%rbx)", "movl %eax, (%rbx)", "movl $1, (%rbx)",
  "sete (%rbx)", "addl %eax, (%rbx)", "xchgl %eax, (%rbx)", "lock addl $1, (%rbx)",
  "lock xaddl %eax, (%rbx)", "movnti %eax, (%rbx)", "movups %xmm0, (%rbx)", "movdqa %xmm0, (%rbx)",
  "lock cmpxchg16b (%rbx)"].all fun l => wideOf l = some false

end Scc.Test.WideX64
