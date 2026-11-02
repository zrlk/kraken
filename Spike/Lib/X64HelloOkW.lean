/-
**hello.w's buffer label** (x86-64; the twin of `Spike/Lib/HelloOkW.lean`, its live part).

- `lBH := freshLabel 0 2 0 1` (`= 2`): rodata runs on thread 0 of `setupStartT 2` (`lbase = 0`, stripe `n = 2`,
  one allocation made, the `ThreadId` box), and its `newBuf` is the thread's first allocation after the box.

**Where this differs from AArch64**: only `lBH` is restated. A64's `okH` record facts (`okH_okW`, `okH_buf`,
`okH_sub`, `b0_eq`, `okH_frz*`, `bufPl_W`), `lBH_eq` and the `setupStartT_*` lemmas are not used by the hello proof
and have no twin. The label is ISA-independent, so the module needs only `WeakCore.TermRun`.
-/
import WeakCore.TermRun

namespace Spike.Lib.X64HelloOkW

/-- **rodata's buffer label**: thread 0's allocation `1` (the first after
the `ThreadId` box) in stripe `2`, base `0`. -/
def lBH : WeakMem.AllocLabel := TermRun.freshLabel 0 2 0 1

end Spike.Lib.X64HelloOkW

/-- info: 'Spike.Lib.X64HelloOkW.lBH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOkW.lBH
