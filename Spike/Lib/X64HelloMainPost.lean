/-
**hello.w on x86-64: `scc_rt_main`'s return point after `wc_main`** (the twin of
`Spike/Lib/A64HelloMainPost.lean`'s code facts; wake's `X64WakeMainPost.mainX2`, `wake_exitIn`): back from the
clone, main runs `Hello.Parent.seg_parent`, the wait loop (`X64WaitLoopX` at `X64HelloLoopCode.waitXL`), and `ret`
to `scc_rt_main`'s return point after `call wc_main`:

    .Lscc_rt_main.x3: movq %rax, -48(%rbp); movq -48(%rbp), %rdi; movl $231, %eax; syscall

whose `exit_group(0)` is main's exit. Unlike wake's (`.x2`, spill at `-16(%rbp)`), hello's `scc_rt_main` calls
`wc_rodata` first and spills its four results, so `wc_main` returns to `.x3` and the spill is at `-48(%rbp)`.

- `mainX3`: `scc_rt_main`'s return point after `call wc_main`.
- `hello_exitIn`: the `exit_group` tail there, its spill at `-48(%rbp)` (`X64CodeSegs.exitIn`, as wake's
  `wake_exitIn`).

## Differences from the AArch64 version

- The return point is `.Lscc_rt_main.x3` (`mainX3`; AArch64: `.L1_scc_rt_main.sp1`, `mainSp1`), the spill
  `-48(%rbp)` with the instruction sizes `4 4 5` (AArch64: `[sp, #40]`); stated on `SccCode.helloCells`.
- A64's `seg_waitExitH` and `seg_mainPostH` are dead and not twinned (wake's `X64WakeMainPost.seg_waitExit`,
  `seg_mainPost` take `hello_exitIn` with `X64HelloParent.hello_parentIn` and `X64HelloLoopCode`'s code facts).
-/
import Spike.Lib.X64HelloParent
import Spike.Lib.X64CodeSegs

namespace Spike.Lib.X64.Flow.Worker.Hello.MainPost

open Kraken

/-- `scc_rt_main`'s return point after `call wc_main` (after `.x2`'s call of `wc_rodata`). -/
abbrev mainX3 : Label := ".Lscc_rt_main.x3"

/-- **The `exit_group` tail at `scc_rt_main`'s return point** in hello's cells, the value spilled at
`-48(%rbp)`. -/
theorem hello_exitIn : Spike.Lib.X64.Flow.exitIn SccCode.helloCells mainX3 (-48) 4 4 5 = true := by decide +kernel

end Spike.Lib.X64.Flow.Worker.Hello.MainPost

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.MainPost.hello_exitIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.MainPost.hello_exitIn
