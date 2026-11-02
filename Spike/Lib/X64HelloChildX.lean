/-
**hello.w's child words at main's clone, register-explicit** (x86-64; the twin of `Spike/Lib/A64HelloChildX.lean`'s
live part): the child's words as main's registers at the clone (not fresh witnesses), so the facts stated at those
registers plug in: `X64HelloSpawnR.words_clone` (`hv`, `htag`, `hvu`), `X64HelloPreA.sl_clone`, `r13_clone`,
`hm_clone`.

- `wordsX`: main's words at the clone, `%r12, %rbx, %r13, %r14, %r15, %r9`.

**Unlike AArch64**, the words are `%r12, %rbx, %r13, %r14, %r15, %r9` read with `get64` (AArch64: `x9 .. x14`, as
`X64HelloChildAt`'s and `X64HelloChildSvcClone`'s), and only `wordsX` is twinned, so the module imports only the
child's `Words` (`X64HelloChild`), not `A64HelloWorkerSegP`/`A64HelloStackB`'s twins.

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only live constants):
`clonePreH_child_atX`, `childP_of_cloneX`, `childP_of_cloneR1X`.
-/
import Spike.Lib.X64HelloChild

namespace Spike.Lib.X64.Flow.Worker.Hello.SegR

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)

/-- main's words at the clone, `%r12, %rbx, %r13, %r14, %r15, %r9`. Its consumers are the clone's word facts
(`X64HelloCPWords`, `X64HelloCPSvc`). -/
abbrev wordsX (th : Thread isa) : Words :=
  ⟨th.st.st.1.regs.get64 .r12, th.st.st.1.regs.get64 .rbx, th.st.st.1.regs.get64 .r13,
    th.st.st.1.regs.get64 .r14, th.st.st.1.regs.get64 .r15, th.st.st.1.regs.get64 .r9⟩

/-- `wordsX`'s third word is main's `%r13` (the slice's count at the clone, `X64HelloPreA.r13_clone`). -/
example (th : Thread isa) : (wordsX th).w2 = th.st.st.1.regs.get64 .r13 := rfl

end Spike.Lib.X64.Flow.Worker.Hello.SegR
