/-
**Every covered block of `hello.w`'s AArch64 code**, through `block_spec`
(`Spike/Lib/A64Flow.lean`).

The text is `scc`'s listing of `Scc/Test/hello.w` for AArch64, produced at
an earlier revision by

    scc --arch arm -S Scc/Test/hello.w

and copied here as data: each block is a run of covered instructions (stack
loads and stores `ldr`/`str Xt, [sp, #n]`, register operations including
`add`/`sub` of an immediate to `sp`) ending at a label, at an uncovered
instruction, or with a branch (`b`, `b.cond`, `cbz`/`cbnz`, `bl`, `ret`),
parsed by Kraken's own `parseAArch64`. The comment above each block gives
its function and its line numbers in the listing.

Each block's region and entry offsets come from a static-offset pass over
its function: on entry `sp` is at offset 0 from the region's base, offsets
flow along fall-through and branch edges (at a label, the meet of all
incoming edges, to a fixpoint), `sub`/`add` of an immediate moves `sp` or
sets a register to a known offset (`sub x9, sp, #n` before the stack check,
`add x29, sp, #n`), `bl` keeps `sp` and forgets the caller-saved registers
(`x0`–`x18`, `x30`), and an uncovered instruction forgets the register it
writes (all registers for `svc` and atomics). The region is `[lo, hi)`, the
least and greatest offsets the function accesses. `block_spec name lo hi o
b` proves `name_ok : okBlk lo hi o b = true` (by `decide`: every directive
classified, every access inside the region with `sp` 16-aligned, only the
last directive a branch), so that `seg_block` applies, and `name_run : ∀ lab
pc σ, arun lab b ⟨pc, o, σ⟩ = …`, the block's exit pc, offsets and abstract
state in closed form (by `simp`).

Blocks are maximal: `block_spec` keeps `AI.step`/`AI.tgt` and
`StatusFlags.subs` folded (see its docstring), so long runs of constant
arithmetic and a branch after a `movk` chain need no cut.

Coverage (instructions of the listing's text; directives, labels and data
are not counted):

| | instructions | covered | non-frame memory | label address | system | shared memory | other |
|---|---|---|---|---|---|---|---|
| compiled functions (`wc_*`) | 748 | 722 (96.5%) | 20 | 0 | 4 | 2 | 0 |
| runtime (`scc_rt_*`, `_start`) | 1236 | 1117 (90.4%) | 39 | 46 | 17 | 13 | 4 |
| total | 1984 | 1839 (92.7%) | | | | | |

"Non-frame memory" includes the `ldur`/`stur` accesses below a header
(`[x10, #-16]`). "Other": the thread start's and `scc_rt_morestack`'s stack
switches (2) and `nop` (2). Label addresses (46), `nop` (2) and `msr
tpidr_el0` (1) are nodes of their own (`si_nd`, `Spike/Lib/A64Nodes.lean`),
as are the stack switches (`sw_nd`, `Spike/Lib/A64Switch.lean`; after a
switch the offsets restart at 0 in a region based at the new `sp`), which
brings the runtime's covered count to 1168 (94.5%) and the total to 1890
(95.3%). The system calls `svc #0` are nodes too (`svc_nd`, through
`Out.sys`): 5 with no kernel event (`rt_sigaction`, `exit_group`, `futex`,
`exit`), 5 abort exits whose number is set before their label, and 7
`write`/`clone` (1 in compiled functions) matched for the thread's control
only; with all 17 the counts are 723 (96.7%), 1184 (95.8%) and 1907
(96.1%). 358 blocks (108 in compiled functions), 1 to 32 instructions each,
221 of them ending
with a branch. The whole file checks in 33 s (wall) with 2.1 GB of memory.
-/
import Spike.Lib.A64Flow
import Kraken.AArch64.Parser

namespace Spike.Lib.A64.Hello

open Kraken Kraken.AArch64.Parser Spike.Lib.A64.Flow

-- _start, listing lines 7–7
block_spec _start_0 (0) 0 ⟨0, []⟩ parseAArch64("b scc_rt_start")

-- scc_rt_start, listing lines 11–14
block_spec scc_rt_start_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")

-- scc_rt_start, listing lines 18–23
block_spec scc_rt_start_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x9, [sp]
movz x0, #13
ldr x1, [sp]
movz x2, #0
movz x3, #8
movz x8, #134")

-- scc_rt_start, listing lines 25–28
block_spec scc_rt_start_2 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #8]
movz x0, #2051
movz x1, #1
bl scc_rt_alloc_tcb")

-- scc_rt_start, listing lines 30–32
block_spec scc_rt_start_3 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #16]
ldr x0, [sp, #16]
bl scc_rt_thread_init")

-- scc_rt_start, listing lines 34–37
block_spec scc_rt_start_4 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #24]
ldr x9, [sp, #24]
ldr x10, [sp, #16]
ldr x0, [sp, #16]")

-- scc_rt_start, listing lines 40–41
block_spec scc_rt_start_5 (0) 0 ⟨0, []⟩ parseAArch64("movz x29, #0
bl scc_rt_main")

-- scc_rt_start, listing lines 43–43
block_spec scc_rt_start_6 (0) 0 ⟨0, []⟩ parseAArch64("b .L0_scc_rt_start.halt4")

-- scc_rt_main, listing lines 48–49
block_spec scc_rt_main_0 (-80) 0 ⟨0, []⟩ parseAArch64("sub x9, sp, #80
mrs x10, tpidr_el0")

-- scc_rt_main, listing lines 51–52
block_spec scc_rt_main_1 (-80) 0 ⟨0, [(.X9, -80)]⟩ parseAArch64("subs xzr, x9, x10
b.lo .L1_scc_rt_main.stack_grow")

-- scc_rt_main, listing lines 53–57
block_spec scc_rt_main_2 (-80) 0 ⟨0, [(.X9, -80)]⟩ parseAArch64("add sp, x9, #0
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
str x0, [sp]")

-- scc_rt_main, listing lines 59–59
block_spec scc_rt_main_3 (-80) 0 ⟨-80, [(.X29, -16), (.X9, -80)]⟩ parseAArch64("bl wc_rodata")

-- scc_rt_main, listing lines 61–70
block_spec scc_rt_main_4 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("str x0, [sp, #8]
str x1, [sp, #16]
str x2, [sp, #24]
str x3, [sp, #32]
ldr x0, [sp, #8]
ldr x1, [sp, #16]
ldr x2, [sp, #24]
ldr x3, [sp, #32]
ldr x4, [sp]
bl wc_main")

-- scc_rt_main, listing lines 72–74
block_spec scc_rt_main_5 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("str x0, [sp, #40]
ldr x0, [sp, #40]
movz x8, #94")

-- scc_rt_main, listing lines 76–76
block_spec scc_rt_main_6 (-80) 0 ⟨-80, []⟩ parseAArch64("str x0, [sp, #48]")

-- scc_rt_main, listing lines 78–78
block_spec scc_rt_main_7 (-80) 0 ⟨-80, []⟩ parseAArch64("b .L1_scc_rt_main.halt3")

-- scc_rt_main, listing lines 80–93
block_spec scc_rt_main_8 (-80) 0 ⟨0, [(.X9, -80)]⟩ parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #80
bl scc_rt_morestack")

-- scc_rt_main, listing lines 95–106
block_spec scc_rt_main_9 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L1_scc_rt_main.stack_check")

-- scc_rt_alloc, listing lines 110–115
block_spec scc_rt_alloc_0 (-192) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #192
str x29, [sp, #176]
str x30, [sp, #184]
add x29, sp, #176
str x0, [sp]
str x1, [sp, #8]")

-- scc_rt_alloc, listing lines 117–120
block_spec scc_rt_alloc_1 (-192) 0 ⟨-192, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #8]
movz x10, #4096, lsl #16
subs xzr, x9, x10
b.hs .L2_scc_rt_alloc.2_full")

-- scc_rt_alloc, listing lines 121–121
block_spec scc_rt_alloc_2 (-192) 0 ⟨-192, [(.X29, -16)]⟩ parseAArch64("b .L2_scc_rt_alloc.1_len")

-- scc_rt_alloc, listing lines 123–154
block_spec scc_rt_alloc_3 (-192) 0 ⟨-192, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp]
movz x10, #8
lsrv x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp]
movz x10, #22
lsrv x9, x9, x10
str x9, [sp, #32]
ldr x9, [sp, #32]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #40]
ldr x9, [sp, #24]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #8]
ldr x10, [sp, #48]
madd x9, x9, x10, xzr
str x9, [sp, #56]
ldr x9, [sp, #56]
movz x10, #1
add x9, x9, x10
str x9, [sp, #64]
ldr x9, [sp, #64]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #72]")

-- scc_rt_alloc, listing lines 157–159
block_spec scc_rt_alloc_4 (-192) 0 ⟨-192, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #80]
ldr x9, [sp, #72]
ldr x10, [sp, #80]")

-- scc_rt_alloc, listing lines 161–169
block_spec scc_rt_alloc_5 (-192) 0 ⟨-192, []⟩ parseAArch64("str x11, [sp, #88]
ldr x9, [sp, #88]
ldr x10, [sp, #72]
add x9, x9, x10
str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #1024, lsl #16
subs xzr, x9, x10
b.hi .L2_scc_rt_alloc.2_full")

-- scc_rt_alloc, listing lines 170–170
block_spec scc_rt_alloc_6 (-192) 0 ⟨-192, []⟩ parseAArch64("b .L2_scc_rt_alloc.3_ok")

-- scc_rt_alloc, listing lines 172–173
block_spec scc_rt_alloc_7 (-192) 0 ⟨-192, []⟩ parseAArch64("movz x0, #2
bl scc_rt_abort")

-- scc_rt_alloc, listing lines 176–176
block_spec scc_rt_alloc_8 (-192) 0 ⟨-192, []⟩ parseAArch64("b .L2_scc_rt_alloc.halt14")

-- scc_rt_alloc, listing lines 180–206
block_spec scc_rt_alloc_9 (-192) 0 ⟨-192, []⟩ parseAArch64("str x9, [sp, #104]
ldr x9, [sp, #104]
ldr x10, [sp, #88]
add x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #8]
ldr x10, [sp, #40]
madd x9, x9, x10, xzr
str x9, [sp, #120]
ldr x9, [sp, #120]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #128]
ldr x9, [sp, #8]
movz x10, #36
lslv x9, x9, x10
str x9, [sp, #136]
ldr x9, [sp]
ldr x10, [sp, #136]
orr x9, x9, x10
str x9, [sp, #144]
ldr x9, [sp, #112]
ldr x10, [sp, #128]
add x9, x9, x10
str x9, [sp, #152]
ldr x9, [sp, #144]
ldr x10, [sp, #152]")

-- scc_rt_alloc, listing lines 208–220
block_spec scc_rt_alloc_10 (-192) 0 ⟨-192, []⟩ parseAArch64("ldr x9, [sp, #112]
ldr x10, [sp, #128]
add x9, x9, x10
str x9, [sp, #160]
ldr x9, [sp, #160]
movz x10, #8
add x9, x9, x10
str x9, [sp, #168]
ldr x0, [sp, #168]
ldr x29, [sp, #176]
ldr x30, [sp, #184]
add sp, sp, #192
ret")

-- scc_rt_alloc_tcb, listing lines 224–229
block_spec scc_rt_alloc_tcb_0 (-192) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #192
str x29, [sp, #176]
str x30, [sp, #184]
add x29, sp, #176
str x0, [sp]
str x1, [sp, #8]")

-- scc_rt_alloc_tcb, listing lines 231–234
block_spec scc_rt_alloc_tcb_1 (-192) 0 ⟨-192, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #8]
movz x10, #4096, lsl #16
subs xzr, x9, x10
b.hs .L3_scc_rt_alloc_tcb.2_full")

-- scc_rt_alloc_tcb, listing lines 235–235
block_spec scc_rt_alloc_tcb_2 (-192) 0 ⟨-192, [(.X29, -16)]⟩ parseAArch64("b .L3_scc_rt_alloc_tcb.1_len")

-- scc_rt_alloc_tcb, listing lines 237–268
block_spec scc_rt_alloc_tcb_3 (-192) 0 ⟨-192, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp]
movz x10, #8
lsrv x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp]
movz x10, #22
lsrv x9, x9, x10
str x9, [sp, #32]
ldr x9, [sp, #32]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #40]
ldr x9, [sp, #24]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #8]
ldr x10, [sp, #48]
madd x9, x9, x10, xzr
str x9, [sp, #56]
ldr x9, [sp, #56]
movz x10, #1
add x9, x9, x10
str x9, [sp, #64]
ldr x9, [sp, #64]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #72]")

-- scc_rt_alloc_tcb, listing lines 271–273
block_spec scc_rt_alloc_tcb_4 (-192) 0 ⟨-192, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #80]
ldr x9, [sp, #72]
ldr x10, [sp, #80]")

-- scc_rt_alloc_tcb, listing lines 275–284
block_spec scc_rt_alloc_tcb_5 (-192) 0 ⟨-192, []⟩ parseAArch64("str x11, [sp, #88]
ldr x9, [sp, #88]
ldr x10, [sp, #72]
add x9, x9, x10
str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #57344
movk x10, #1, lsl #16
subs xzr, x9, x10
b.hi .L3_scc_rt_alloc_tcb.2_full")

-- scc_rt_alloc_tcb, listing lines 285–285
block_spec scc_rt_alloc_tcb_6 (-192) 0 ⟨-192, []⟩ parseAArch64("b .L3_scc_rt_alloc_tcb.3_ok")

-- scc_rt_alloc_tcb, listing lines 287–288
block_spec scc_rt_alloc_tcb_7 (-192) 0 ⟨-192, []⟩ parseAArch64("movz x0, #5
bl scc_rt_abort")

-- scc_rt_alloc_tcb, listing lines 291–291
block_spec scc_rt_alloc_tcb_8 (-192) 0 ⟨-192, []⟩ parseAArch64("b .L3_scc_rt_alloc_tcb.halt14")

-- scc_rt_alloc_tcb, listing lines 295–321
block_spec scc_rt_alloc_tcb_9 (-192) 0 ⟨-192, []⟩ parseAArch64("str x9, [sp, #104]
ldr x9, [sp, #104]
ldr x10, [sp, #88]
add x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #8]
ldr x10, [sp, #40]
madd x9, x9, x10, xzr
str x9, [sp, #120]
ldr x9, [sp, #120]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #128]
ldr x9, [sp, #8]
movz x10, #36
lslv x9, x9, x10
str x9, [sp, #136]
ldr x9, [sp]
ldr x10, [sp, #136]
orr x9, x9, x10
str x9, [sp, #144]
ldr x9, [sp, #112]
ldr x10, [sp, #128]
add x9, x9, x10
str x9, [sp, #152]
ldr x9, [sp, #144]
ldr x10, [sp, #152]")

-- scc_rt_alloc_tcb, listing lines 323–335
block_spec scc_rt_alloc_tcb_10 (-192) 0 ⟨-192, []⟩ parseAArch64("ldr x9, [sp, #112]
ldr x10, [sp, #128]
add x9, x9, x10
str x9, [sp, #160]
ldr x9, [sp, #160]
movz x10, #8
add x9, x9, x10
str x9, [sp, #168]
ldr x0, [sp, #168]
ldr x29, [sp, #176]
ldr x30, [sp, #184]
add sp, sp, #192
ret")

-- scc_rt_thread_reserve, listing lines 339–342
block_spec scc_rt_thread_reserve_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")

-- scc_rt_thread_reserve, listing lines 346–348
block_spec scc_rt_thread_reserve_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x9, [sp]
movz x9, #1
ldr x10, [sp]")

-- scc_rt_thread_reserve, listing lines 350–358
block_spec scc_rt_thread_reserve_2 (-48) 0 ⟨-48, []⟩ parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #1023
subs xzr, x9, x10
b.hi .L4_scc_rt_thread_reserve.1_full")

-- scc_rt_thread_reserve, listing lines 359–359
block_spec scc_rt_thread_reserve_3 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L4_scc_rt_thread_reserve.2_ok")

-- scc_rt_thread_reserve, listing lines 361–362
block_spec scc_rt_thread_reserve_4 (-48) 0 ⟨-48, []⟩ parseAArch64("movz x0, #5
bl scc_rt_abort")

-- scc_rt_thread_reserve, listing lines 365–365
block_spec scc_rt_thread_reserve_5 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L4_scc_rt_thread_reserve.halt5")

-- scc_rt_thread_reserve, listing lines 367–371
block_spec scc_rt_thread_reserve_6 (-48) 0 ⟨-48, []⟩ parseAArch64("ldr x0, [sp, #16]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

-- scc_rt_thread_init, listing lines 375–379
block_spec scc_rt_thread_init_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]")

-- scc_rt_thread_init, listing lines 381–382
block_spec scc_rt_thread_init_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("movz x0, #16384
bl scc_rt_stack_take")

-- scc_rt_thread_init, listing lines 384–394
block_spec scc_rt_thread_init_2 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x0, [sp, #8]
ldr x9, [sp, #8]
movz x10, #4096
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #8]
movz x10, #16384
add x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp]
ldr x10, [sp]")

-- scc_rt_thread_init, listing lines 396–397
block_spec scc_rt_thread_init_3 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #16]
ldr x10, [sp]")

-- scc_rt_thread_init, listing lines 399–400
block_spec scc_rt_thread_init_4 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("movz x9, #0
ldr x10, [sp]")

-- scc_rt_thread_init, listing lines 402–403
block_spec scc_rt_thread_init_5 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("movz x9, #0
ldr x10, [sp]")

-- scc_rt_thread_init, listing lines 405–406
block_spec scc_rt_thread_init_6 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #8]
ldr x10, [sp]")

-- scc_rt_thread_init, listing lines 408–409
block_spec scc_rt_thread_init_7 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #24]
ldr x10, [sp]")

-- scc_rt_thread_init, listing lines 411–415
block_spec scc_rt_thread_init_8 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #24]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

-- scc_rt_stack_take, listing lines 419–423
block_spec scc_rt_stack_take_0 (-208) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #208
str x29, [sp, #192]
str x30, [sp, #200]
add x29, sp, #192
str x0, [sp]")

-- scc_rt_stack_take, listing lines 425–433
block_spec scc_rt_stack_take_1 (-208) 0 ⟨-208, [(.X29, -16)]⟩ parseAArch64("movz x9, #16384
str x9, [sp, #8]
movz x9, #0
str x9, [sp, #16]
movz x9, #32768
str x9, [sp, #24]
movz x9, #0
str x9, [sp, #32]
b .L6_scc_rt_stack_take.1_cls5")

-- scc_rt_stack_take, listing lines 435–438
block_spec scc_rt_stack_take_2 (-208) 0 ⟨-208, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #8]
ldr x10, [sp]
subs xzr, x9, x10
b.lo .L6_scc_rt_stack_take.2_clsnext6")

-- scc_rt_stack_take, listing lines 439–439
block_spec scc_rt_stack_take_3 (-208) 0 ⟨-208, [(.X29, -16)]⟩ parseAArch64("b .L6_scc_rt_stack_take.3_clsdone7")

-- scc_rt_stack_take, listing lines 441–461
block_spec scc_rt_stack_take_4 (-208) 0 ⟨-208, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #24]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #40]
ldr x9, [sp, #16]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #24]
movz x10, #1
lsrv x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp, #8]
movz x10, #1
lslv x9, x9, x10
str x9, [sp, #8]
ldr x9, [sp, #32]
movz x10, #8
add x9, x9, x10
str x9, [sp, #32]
b .L6_scc_rt_stack_take.1_cls5")

-- scc_rt_stack_take, listing lines 465–469
block_spec scc_rt_stack_take_5 (-208) 0 ⟨-208, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #48]
ldr x9, [sp, #48]
ldr x10, [sp, #32]
add x9, x9, x10
str x9, [sp, #56]")

-- scc_rt_stack_take, listing lines 472–476
block_spec scc_rt_stack_take_6 (-208) 0 ⟨-208, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #64]
ldr x9, [sp, #64]
ldr x10, [sp, #16]
add x9, x9, x10
str x9, [sp, #72]")

-- scc_rt_stack_take, listing lines 479–480
block_spec scc_rt_stack_take_7 (-208) 0 ⟨-208, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #80]
b .L6_scc_rt_stack_take.4_spin14")

-- scc_rt_stack_take, listing lines 482–483
block_spec scc_rt_stack_take_8 (-208) 0 ⟨-208, []⟩ parseAArch64("movz x9, #1
ldr x10, [sp, #80]")

-- scc_rt_stack_take, listing lines 485–489
block_spec scc_rt_stack_take_9 (-208) 0 ⟨-208, []⟩ parseAArch64("str x11, [sp, #88]
ldr x9, [sp, #88]
movz x10, #0
subs xzr, x9, x10
b.eq .L6_scc_rt_stack_take.5_locked15")

-- scc_rt_stack_take, listing lines 490–490
block_spec scc_rt_stack_take_10 (-208) 0 ⟨-208, []⟩ parseAArch64("b .L6_scc_rt_stack_take.4_spin14")

-- scc_rt_stack_take, listing lines 492–492
block_spec scc_rt_stack_take_11 (-208) 0 ⟨-208, []⟩ parseAArch64("ldr x10, [sp, #56]")

-- scc_rt_stack_take, listing lines 494–498
block_spec scc_rt_stack_take_12 (-208) 0 ⟨-208, []⟩ parseAArch64("str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #0
subs xzr, x9, x10
b.eq .L6_scc_rt_stack_take.7_bump")

-- scc_rt_stack_take, listing lines 499–499
block_spec scc_rt_stack_take_13 (-208) 0 ⟨-208, []⟩ parseAArch64("b .L6_scc_rt_stack_take.6_pop")

-- scc_rt_stack_take, listing lines 501–506
block_spec scc_rt_stack_take_14 (-208) 0 ⟨-208, []⟩ parseAArch64("ldr x9, [sp, #96]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #104]
ldr x9, [sp, #104]
ldr x10, [sp, #56]")

-- scc_rt_stack_take, listing lines 508–516
block_spec scc_rt_stack_take_15 (-208) 0 ⟨-208, []⟩ parseAArch64("ldr x9, [sp, #104]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #72]
ldr x10, [sp, #112]
add x9, x9, x10
str x9, [sp, #120]
ldr x10, [sp, #120]")

-- scc_rt_stack_take, listing lines 518–518
block_spec scc_rt_stack_take_16 (-208) 0 ⟨-208, []⟩ parseAArch64("str x9, [sp, #128]")

-- scc_rt_stack_take, listing lines 521–523
block_spec scc_rt_stack_take_17 (-208) 0 ⟨-208, []⟩ parseAArch64("str x9, [sp, #136]
movz x9, #0
ldr x10, [sp, #136]")

-- scc_rt_stack_take, listing lines 525–525
block_spec scc_rt_stack_take_18 (-208) 0 ⟨-208, []⟩ parseAArch64("b .L6_scc_rt_stack_take.10_taken")

-- scc_rt_stack_take, listing lines 529–531
block_spec scc_rt_stack_take_19 (-208) 0 ⟨-208, []⟩ parseAArch64("str x9, [sp, #144]
movz x9, #0
ldr x10, [sp, #144]")

-- scc_rt_stack_take, listing lines 535–537
block_spec scc_rt_stack_take_20 (-208) 0 ⟨-208, []⟩ parseAArch64("str x9, [sp, #152]
ldr x9, [sp]
ldr x10, [sp, #152]")

-- scc_rt_stack_take, listing lines 539–547
block_spec scc_rt_stack_take_21 (-208) 0 ⟨-208, []⟩ parseAArch64("str x11, [sp, #160]
ldr x9, [sp, #160]
ldr x10, [sp]
add x9, x9, x10
str x9, [sp, #168]
ldr x9, [sp, #168]
movz x10, #8192, lsl #16
subs xzr, x9, x10
b.hi .L6_scc_rt_stack_take.8_full")

-- scc_rt_stack_take, listing lines 548–548
block_spec scc_rt_stack_take_22 (-208) 0 ⟨-208, []⟩ parseAArch64("b .L6_scc_rt_stack_take.9_ok")

-- scc_rt_stack_take, listing lines 550–551
block_spec scc_rt_stack_take_23 (-208) 0 ⟨-208, []⟩ parseAArch64("movz x0, #3
bl scc_rt_abort")

-- scc_rt_stack_take, listing lines 554–554
block_spec scc_rt_stack_take_24 (-208) 0 ⟨-208, []⟩ parseAArch64("b .L6_scc_rt_stack_take.halt37")

-- scc_rt_stack_take, listing lines 558–563
block_spec scc_rt_stack_take_25 (-208) 0 ⟨-208, []⟩ parseAArch64("str x9, [sp, #176]
ldr x9, [sp, #176]
ldr x10, [sp, #160]
add x9, x9, x10
str x9, [sp, #128]
b .L6_scc_rt_stack_take.10_taken")

-- scc_rt_stack_take, listing lines 565–566
block_spec scc_rt_stack_take_26 (-208) 0 ⟨-208, []⟩ parseAArch64("ldr x0, [sp, #128]
ldr x1, [sp]")

-- scc_rt_stack_take, listing lines 569–573
block_spec scc_rt_stack_take_27 (-208) 0 ⟨-208, []⟩ parseAArch64("ldr x0, [sp, #128]
ldr x29, [sp, #192]
ldr x30, [sp, #200]
add sp, sp, #208
ret")

-- scc_rt_stack_release, listing lines 577–582
block_spec scc_rt_stack_release_0 (-160) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #160
str x29, [sp, #144]
str x30, [sp, #152]
add x29, sp, #144
str x0, [sp]
str x1, [sp, #8]")

-- scc_rt_stack_release, listing lines 584–585
block_spec scc_rt_stack_release_1 (-160) 0 ⟨-160, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]")

-- scc_rt_stack_release, listing lines 588–596
block_spec scc_rt_stack_release_2 (-160) 0 ⟨-160, [(.X29, -16)]⟩ parseAArch64("movz x9, #16384
str x9, [sp, #16]
movz x9, #0
str x9, [sp, #24]
movz x9, #32768
str x9, [sp, #32]
movz x9, #0
str x9, [sp, #40]
b .L7_scc_rt_stack_release.1_cls4")

-- scc_rt_stack_release, listing lines 598–601
block_spec scc_rt_stack_release_3 (-160) 0 ⟨-160, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #16]
ldr x10, [sp, #8]
subs xzr, x9, x10
b.lo .L7_scc_rt_stack_release.2_clsnext5")

-- scc_rt_stack_release, listing lines 602–602
block_spec scc_rt_stack_release_4 (-160) 0 ⟨-160, [(.X29, -16)]⟩ parseAArch64("b .L7_scc_rt_stack_release.3_clsdone6")

-- scc_rt_stack_release, listing lines 604–624
block_spec scc_rt_stack_release_5 (-160) 0 ⟨-160, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #32]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #24]
ldr x10, [sp, #48]
add x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp, #32]
movz x10, #1
lsrv x9, x9, x10
str x9, [sp, #32]
ldr x9, [sp, #16]
movz x10, #1
lslv x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #40]
movz x10, #8
add x9, x9, x10
str x9, [sp, #40]
b .L7_scc_rt_stack_release.1_cls4")

-- scc_rt_stack_release, listing lines 628–632
block_spec scc_rt_stack_release_6 (-160) 0 ⟨-160, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #56]
ldr x9, [sp, #56]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #64]")

-- scc_rt_stack_release, listing lines 635–639
block_spec scc_rt_stack_release_7 (-160) 0 ⟨-160, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #72]
ldr x9, [sp, #72]
ldr x10, [sp, #24]
add x9, x9, x10
str x9, [sp, #80]")

-- scc_rt_stack_release, listing lines 642–643
block_spec scc_rt_stack_release_8 (-160) 0 ⟨-160, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #88]
b .L7_scc_rt_stack_release.4_spin13")

-- scc_rt_stack_release, listing lines 645–646
block_spec scc_rt_stack_release_9 (-160) 0 ⟨-160, []⟩ parseAArch64("movz x9, #1
ldr x10, [sp, #88]")

-- scc_rt_stack_release, listing lines 648–652
block_spec scc_rt_stack_release_10 (-160) 0 ⟨-160, []⟩ parseAArch64("str x11, [sp, #96]
ldr x9, [sp, #96]
movz x10, #0
subs xzr, x9, x10
b.eq .L7_scc_rt_stack_release.5_locked14")

-- scc_rt_stack_release, listing lines 653–653
block_spec scc_rt_stack_release_11 (-160) 0 ⟨-160, []⟩ parseAArch64("b .L7_scc_rt_stack_release.4_spin13")

-- scc_rt_stack_release, listing lines 655–655
block_spec scc_rt_stack_release_12 (-160) 0 ⟨-160, []⟩ parseAArch64("ldr x10, [sp, #64]")

-- scc_rt_stack_release, listing lines 657–667
block_spec scc_rt_stack_release_13 (-160) 0 ⟨-160, []⟩ parseAArch64("str x9, [sp, #104]
ldr x9, [sp, #104]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #80]
ldr x10, [sp, #112]
add x9, x9, x10
str x9, [sp, #120]
ldr x9, [sp]
ldr x10, [sp, #120]")

-- scc_rt_stack_release, listing lines 669–674
block_spec scc_rt_stack_release_14 (-160) 0 ⟨-160, []⟩ parseAArch64("ldr x9, [sp, #104]
movz x10, #1
add x9, x9, x10
str x9, [sp, #128]
ldr x9, [sp, #128]
ldr x10, [sp, #64]")

-- scc_rt_stack_release, listing lines 678–680
block_spec scc_rt_stack_release_15 (-160) 0 ⟨-160, []⟩ parseAArch64("str x9, [sp, #136]
movz x9, #0
ldr x10, [sp, #136]")

-- scc_rt_stack_release, listing lines 682–685
block_spec scc_rt_stack_release_16 (-160) 0 ⟨-160, []⟩ parseAArch64("ldr x29, [sp, #144]
ldr x30, [sp, #152]
add sp, sp, #160
ret")

-- scc_rt_grow, listing lines 689–694
block_spec scc_rt_grow_0 (-368) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #368
str x29, [sp, #352]
str x30, [sp, #360]
add x29, sp, #352
str x0, [sp]
str x1, [sp, #8]")

-- scc_rt_grow, listing lines 696–698
block_spec scc_rt_grow_1 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("mrs x9, tpidr_el0
str x9, [sp, #16]
ldr x10, [sp, #16]")

-- scc_rt_grow, listing lines 700–701
block_spec scc_rt_grow_2 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #24]
ldr x10, [sp, #16]")

-- scc_rt_grow, listing lines 703–724
block_spec scc_rt_grow_3 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #32]
ldr x9, [sp, #32]
ldr x10, [sp, #24]
sub x9, x9, x10
str x9, [sp, #40]
ldr x9, [sp, #32]
ldr x10, [sp]
sub x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #48]
ldr x10, [sp, #8]
add x9, x9, x10
str x9, [sp, #56]
ldr x9, [sp, #56]
movz x10, #4352
add x9, x9, x10
str x9, [sp, #64]
ldr x9, [sp, #40]
movz x10, #1
lslv x9, x9, x10
str x9, [sp, #72]
b .L8_scc_rt_grow.1_dbl")

-- scc_rt_grow, listing lines 726–729
block_spec scc_rt_grow_4 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #72]
ldr x10, [sp, #64]
subs xzr, x9, x10
b.lo .L8_scc_rt_grow.2_dbl2")

-- scc_rt_grow, listing lines 730–730
block_spec scc_rt_grow_5 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.3_cap")

-- scc_rt_grow, listing lines 732–736
block_spec scc_rt_grow_6 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #72]
movz x10, #1
lslv x9, x9, x10
str x9, [sp, #72]
b .L8_scc_rt_grow.1_dbl")

-- scc_rt_grow, listing lines 738–741
block_spec scc_rt_grow_7 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #72]
movz x10, #1024, lsl #16
subs xzr, x9, x10
b.hi .L8_scc_rt_grow.4_full")

-- scc_rt_grow, listing lines 742–742
block_spec scc_rt_grow_8 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.5_take")

-- scc_rt_grow, listing lines 744–745
block_spec scc_rt_grow_9 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("movz x0, #3
bl scc_rt_abort")

-- scc_rt_grow, listing lines 748–748
block_spec scc_rt_grow_10 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.halt14")

-- scc_rt_grow, listing lines 750–751
block_spec scc_rt_grow_11 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #72]
bl scc_rt_stack_take")

-- scc_rt_grow, listing lines 753–764
block_spec scc_rt_grow_12 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x0, [sp, #80]
ldr x9, [sp, #80]
ldr x10, [sp, #72]
add x9, x9, x10
str x9, [sp, #88]
ldr x9, [sp, #88]
ldr x10, [sp, #32]
sub x9, x9, x10
str x9, [sp, #96]
ldr x9, [sp]
str x9, [sp, #104]
b .L8_scc_rt_grow.6_copy")

-- scc_rt_grow, listing lines 766–769
block_spec scc_rt_grow_13 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #104]
ldr x10, [sp, #32]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.8_walk0")

-- scc_rt_grow, listing lines 770–770
block_spec scc_rt_grow_14 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.7_copy1")

-- scc_rt_grow, listing lines 772–772
block_spec scc_rt_grow_15 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x10, [sp, #104]")

-- scc_rt_grow, listing lines 774–780
block_spec scc_rt_grow_16 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #112]
ldr x9, [sp, #104]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #120]
ldr x9, [sp, #112]
ldr x10, [sp, #120]")

-- scc_rt_grow, listing lines 782–786
block_spec scc_rt_grow_17 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #104]
movz x10, #8
add x9, x9, x10
str x9, [sp, #104]
b .L8_scc_rt_grow.6_copy")

-- scc_rt_grow, listing lines 788–789
block_spec scc_rt_grow_18 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp]
str x9, [sp, #128]")

-- scc_rt_grow, listing lines 792–793
block_spec scc_rt_grow_19 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #136]
ldr x10, [sp, #136]")

-- scc_rt_grow, listing lines 795–808
block_spec scc_rt_grow_20 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #144]
ldr x9, [sp, #144]
movz x10, #32
madd x9, x9, x10, xzr
str x9, [sp, #152]
ldr x9, [sp, #152]
movz x10, #8
add x9, x9, x10
str x9, [sp, #160]
ldr x9, [sp, #136]
ldr x10, [sp, #160]
add x9, x9, x10
str x9, [sp, #168]
b .L8_scc_rt_grow.9_walk")

-- scc_rt_grow, listing lines 810–810
block_spec scc_rt_grow_21 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x10, [sp, #128]")

-- scc_rt_grow, listing lines 812–816
block_spec scc_rt_grow_22 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #176]
ldr x9, [sp, #176]
ldr x10, [sp, #24]
subs xzr, x9, x10
b.lo .L8_scc_rt_grow.24_done")

-- scc_rt_grow, listing lines 817–817
block_spec scc_rt_grow_23 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.10_walk1")

-- scc_rt_grow, listing lines 819–822
block_spec scc_rt_grow_24 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #176]
ldr x10, [sp, #32]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.24_done")

-- scc_rt_grow, listing lines 823–823
block_spec scc_rt_grow_25 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.11_walk2")

-- scc_rt_grow, listing lines 825–834
block_spec scc_rt_grow_26 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #128]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #184]
ldr x9, [sp, #176]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #192]
ldr x9, [sp, #192]
ldr x10, [sp, #184]")

-- scc_rt_grow, listing lines 836–836
block_spec scc_rt_grow_27 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x10, [sp, #128]")

-- scc_rt_grow, listing lines 838–843
block_spec scc_rt_grow_28 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #200]
movz x9, #0
str x9, [sp, #208]
ldr x9, [sp, #144]
str x9, [sp, #216]
b .L8_scc_rt_grow.12_bs")

-- scc_rt_grow, listing lines 845–848
block_spec scc_rt_grow_29 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #208]
ldr x10, [sp, #216]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.23_next")

-- scc_rt_grow, listing lines 849–849
block_spec scc_rt_grow_30 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.13_bs1")

-- scc_rt_grow, listing lines 851–871
block_spec scc_rt_grow_31 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #208]
ldr x10, [sp, #216]
add x9, x9, x10
str x9, [sp, #224]
ldr x9, [sp, #224]
movz x10, #1
lsrv x9, x9, x10
str x9, [sp, #232]
ldr x9, [sp, #232]
movz x10, #32
madd x9, x9, x10, xzr
str x9, [sp, #240]
ldr x9, [sp, #136]
ldr x10, [sp, #240]
add x9, x9, x10
str x9, [sp, #248]
ldr x9, [sp, #248]
movz x10, #8
add x9, x9, x10
str x9, [sp, #248]
ldr x10, [sp, #248]")

-- scc_rt_grow, listing lines 873–877
block_spec scc_rt_grow_32 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #256]
ldr x9, [sp, #256]
ldr x10, [sp, #200]
subs xzr, x9, x10
b.eq .L8_scc_rt_grow.17_found")

-- scc_rt_grow, listing lines 878–878
block_spec scc_rt_grow_33 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.14_bs2")

-- scc_rt_grow, listing lines 880–883
block_spec scc_rt_grow_34 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #256]
ldr x10, [sp, #200]
subs xzr, x9, x10
b.lo .L8_scc_rt_grow.15_bslo")

-- scc_rt_grow, listing lines 884–884
block_spec scc_rt_grow_35 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.16_bshi")

-- scc_rt_grow, listing lines 886–890
block_spec scc_rt_grow_36 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #232]
movz x10, #1
add x9, x9, x10
str x9, [sp, #208]
b .L8_scc_rt_grow.12_bs")

-- scc_rt_grow, listing lines 892–894
block_spec scc_rt_grow_37 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #232]
str x9, [sp, #216]
b .L8_scc_rt_grow.12_bs")

-- scc_rt_grow, listing lines 896–896
block_spec scc_rt_grow_38 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x10, [sp, #248]")

-- scc_rt_grow, listing lines 898–899
block_spec scc_rt_grow_39 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #264]
ldr x10, [sp, #248]")

-- scc_rt_grow, listing lines 901–912
block_spec scc_rt_grow_40 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #272]
ldr x9, [sp, #272]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #280]
ldr x9, [sp, #280]
ldr x10, [sp, #168]
add x9, x9, x10
str x9, [sp, #280]
movz x9, #0
str x9, [sp, #288]
b .L8_scc_rt_grow.18_fix")

-- scc_rt_grow, listing lines 914–917
block_spec scc_rt_grow_41 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #288]
ldr x10, [sp, #264]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.23_next")

-- scc_rt_grow, listing lines 918–918
block_spec scc_rt_grow_42 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.19_fix1")

-- scc_rt_grow, listing lines 920–920
block_spec scc_rt_grow_43 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x10, [sp, #280]")

-- scc_rt_grow, listing lines 922–927
block_spec scc_rt_grow_44 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #296]
ldr x9, [sp, #176]
ldr x10, [sp, #296]
add x9, x9, x10
str x9, [sp, #304]
ldr x10, [sp, #304]")

-- scc_rt_grow, listing lines 929–933
block_spec scc_rt_grow_45 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #312]
ldr x9, [sp, #312]
ldr x10, [sp, #24]
subs xzr, x9, x10
b.lo .L8_scc_rt_grow.22_skip")

-- scc_rt_grow, listing lines 934–934
block_spec scc_rt_grow_46 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.20_fix2")

-- scc_rt_grow, listing lines 936–939
block_spec scc_rt_grow_47 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #312]
ldr x10, [sp, #32]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.22_skip")

-- scc_rt_grow, listing lines 940–940
block_spec scc_rt_grow_48 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.21_fix3")

-- scc_rt_grow, listing lines 942–951
block_spec scc_rt_grow_49 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #304]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #320]
ldr x9, [sp, #312]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #328]
ldr x9, [sp, #328]
ldr x10, [sp, #320]")

-- scc_rt_grow, listing lines 953–953
block_spec scc_rt_grow_50 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("b .L8_scc_rt_grow.22_skip")

-- scc_rt_grow, listing lines 955–963
block_spec scc_rt_grow_51 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #288]
movz x10, #1
add x9, x9, x10
str x9, [sp, #288]
ldr x9, [sp, #280]
movz x10, #8
add x9, x9, x10
str x9, [sp, #280]
b .L8_scc_rt_grow.18_fix")

-- scc_rt_grow, listing lines 965–967
block_spec scc_rt_grow_52 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #176]
str x9, [sp, #128]
b .L8_scc_rt_grow.9_walk")

-- scc_rt_grow, listing lines 969–970
block_spec scc_rt_grow_53 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #80]
ldr x10, [sp, #16]")

-- scc_rt_grow, listing lines 972–973
block_spec scc_rt_grow_54 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #88]
ldr x10, [sp, #16]")

-- scc_rt_grow, listing lines 975–980
block_spec scc_rt_grow_55 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #80]
movz x10, #4096
add x9, x9, x10
str x9, [sp, #336]
ldr x9, [sp, #336]
ldr x10, [sp, #16]")

-- scc_rt_grow, listing lines 982–988
block_spec scc_rt_grow_56 (-368) 0 ⟨-368, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #96]
ldr x1, [sp, #24]
ldr x2, [sp, #40]
ldr x29, [sp, #352]
ldr x30, [sp, #360]
add sp, sp, #368
ret")

-- scc_rt_print, listing lines 992–997
block_spec scc_rt_print_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]
str x1, [sp, #8]")

-- scc_rt_print, listing lines 999–999
block_spec scc_rt_print_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("b .L9_scc_rt_print.1_loop")

-- scc_rt_print, listing lines 1001–1004
block_spec scc_rt_print_2 (-48) 0 ⟨-48, []⟩ parseAArch64("ldr x9, [sp, #8]
movz x10, #0
subs xzr, x9, x10
b.eq .L9_scc_rt_print.7_done")

-- scc_rt_print, listing lines 1005–1005
block_spec scc_rt_print_3 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L9_scc_rt_print.2_write")

-- scc_rt_print, listing lines 1007–1010
block_spec scc_rt_print_4 (-48) 0 ⟨-48, []⟩ parseAArch64("movz x0, #1
ldr x1, [sp]
ldr x2, [sp, #8]
movz x8, #64")

-- scc_rt_print, listing lines 1012–1019
block_spec scc_rt_print_5 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #16]
ldr x9, [sp, #16]
movz x10, #65532
movk x10, #65535, lsl #16
movk x10, #65535, lsl #32
movk x10, #65535, lsl #48
subs xzr, x9, x10
b.eq .L9_scc_rt_print.1_loop")

-- scc_rt_print, listing lines 1020–1020
block_spec scc_rt_print_6 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L9_scc_rt_print.3_chk2")

-- scc_rt_print, listing lines 1022–1028
block_spec scc_rt_print_7 (-48) 0 ⟨-48, []⟩ parseAArch64("ldr x9, [sp, #16]
movz x10, #65525
movk x10, #65535, lsl #16
movk x10, #65535, lsl #32
movk x10, #65535, lsl #48
subs xzr, x9, x10
b.eq .L9_scc_rt_print.1_loop")

-- scc_rt_print, listing lines 1029–1029
block_spec scc_rt_print_8 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L9_scc_rt_print.4_chk3")

-- scc_rt_print, listing lines 1031–1034
block_spec scc_rt_print_9 (-48) 0 ⟨-48, []⟩ parseAArch64("ldr x9, [sp, #16]
movz x10, #0
subs xzr, x9, x10
b.le .L9_scc_rt_print.6_fail")

-- scc_rt_print, listing lines 1035–1035
block_spec scc_rt_print_10 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L9_scc_rt_print.5_adv")

-- scc_rt_print, listing lines 1037–1045
block_spec scc_rt_print_11 (-48) 0 ⟨-48, []⟩ parseAArch64("ldr x9, [sp]
ldr x10, [sp, #16]
add x9, x9, x10
str x9, [sp]
ldr x9, [sp, #8]
ldr x10, [sp, #16]
sub x9, x9, x10
str x9, [sp, #8]
b .L9_scc_rt_print.1_loop")

-- scc_rt_print, listing lines 1047–1048
block_spec scc_rt_print_12 (-48) 0 ⟨-48, []⟩ parseAArch64("movz x0, #4
bl scc_rt_abort")

-- scc_rt_print, listing lines 1051–1051
block_spec scc_rt_print_13 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L9_scc_rt_print.halt10")

-- scc_rt_print, listing lines 1053–1056
block_spec scc_rt_print_14 (-48) 0 ⟨-48, []⟩ parseAArch64("ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

-- scc_rt_park, listing lines 1060–1063
block_spec scc_rt_park_0 (-64) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #64
str x29, [sp, #48]
str x30, [sp, #56]
add x29, sp, #48")

-- scc_rt_park, listing lines 1065–1069
block_spec scc_rt_park_1 (-64) 0 ⟨-64, [(.X29, -16)]⟩ parseAArch64("mrs x9, tpidr_el0
str x9, [sp]
movz x9, #0
ldr x10, [sp]
add x10, x10, #16")

-- scc_rt_park, listing lines 1071–1075
block_spec scc_rt_park_2 (-64) 0 ⟨-64, []⟩ parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
subs xzr, x9, x10
b.eq .L10_scc_rt_park.2_done")

-- scc_rt_park, listing lines 1076–1076
block_spec scc_rt_park_3 (-64) 0 ⟨-64, []⟩ parseAArch64("b .L10_scc_rt_park.1_wait")

-- scc_rt_park, listing lines 1078–1088
block_spec scc_rt_park_4 (-64) 0 ⟨-64, []⟩ parseAArch64("ldr x9, [sp]
movz x10, #16
add x9, x9, x10
str x9, [sp, #16]
ldr x0, [sp, #16]
movz x1, #128
movz x2, #0
movz x3, #0
movz x4, #0
movz x5, #0
movz x8, #98")

-- scc_rt_park, listing lines 1090–1093
block_spec scc_rt_park_5 (-64) 0 ⟨-64, []⟩ parseAArch64("str x0, [sp, #24]
movz x9, #0
ldr x10, [sp]
add x10, x10, #16")

-- scc_rt_park, listing lines 1095–1099
block_spec scc_rt_park_6 (-64) 0 ⟨-64, []⟩ parseAArch64("str x11, [sp, #32]
ldr x29, [sp, #48]
ldr x30, [sp, #56]
add sp, sp, #64
ret")

-- scc_rt_park, listing lines 1101–1104
block_spec scc_rt_park_7 (-64) 0 ⟨-64, []⟩ parseAArch64("ldr x29, [sp, #48]
ldr x30, [sp, #56]
add sp, sp, #64
ret")

-- scc_rt_unpark, listing lines 1108–1112
block_spec scc_rt_unpark_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]")

-- scc_rt_unpark, listing lines 1114–1116
block_spec scc_rt_unpark_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("movz x9, #1
ldr x10, [sp]
add x10, x10, #16")

-- scc_rt_unpark, listing lines 1118–1122
block_spec scc_rt_unpark_2 (-48) 0 ⟨-48, []⟩ parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #0
subs xzr, x9, x10
b.eq .L11_scc_rt_unpark.1_wake")

-- scc_rt_unpark, listing lines 1123–1123
block_spec scc_rt_unpark_3 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L11_scc_rt_unpark.2_done")

-- scc_rt_unpark, listing lines 1125–1135
block_spec scc_rt_unpark_4 (-48) 0 ⟨-48, []⟩ parseAArch64("ldr x9, [sp]
movz x10, #16
add x9, x9, x10
str x9, [sp, #16]
ldr x0, [sp, #16]
movz x1, #129
movz x2, #1
movz x3, #0
movz x4, #0
movz x5, #0
movz x8, #98")

-- scc_rt_unpark, listing lines 1137–1141
block_spec scc_rt_unpark_5 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #24]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

-- scc_rt_unpark, listing lines 1143–1146
block_spec scc_rt_unpark_6 (-48) 0 ⟨-48, []⟩ parseAArch64("ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

-- scc_rt_abort, listing lines 1150–1154
block_spec scc_rt_abort_0 (-32) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #32
str x29, [sp, #16]
str x30, [sp, #24]
add x29, sp, #16
str x0, [sp]")

-- scc_rt_abort, listing lines 1156–1159
block_spec scc_rt_abort_1 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp]
movz x10, #1
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.1_is0")

-- scc_rt_abort, listing lines 1160–1160
block_spec scc_rt_abort_2 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("b .L12_scc_rt_abort.2_next1")

-- scc_rt_abort, listing lines 1162–1165
block_spec scc_rt_abort_3 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_overflow")

-- scc_rt_abort, listing lines 1167–1170
block_spec scc_rt_abort_4 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp]
movz x10, #2
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.3_is2")

-- scc_rt_abort, listing lines 1171–1171
block_spec scc_rt_abort_5 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("b .L12_scc_rt_abort.4_next3")

-- scc_rt_abort, listing lines 1173–1176
block_spec scc_rt_abort_6 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_heap")

-- scc_rt_abort, listing lines 1178–1181
block_spec scc_rt_abort_7 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp]
movz x10, #3
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.5_is4")

-- scc_rt_abort, listing lines 1182–1182
block_spec scc_rt_abort_8 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("b .L12_scc_rt_abort.6_next5")

-- scc_rt_abort, listing lines 1184–1187
block_spec scc_rt_abort_9 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_stack")

-- scc_rt_abort, listing lines 1189–1192
block_spec scc_rt_abort_10 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp]
movz x10, #4
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.7_is6")

-- scc_rt_abort, listing lines 1193–1193
block_spec scc_rt_abort_11 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("b .L12_scc_rt_abort.8_next7")

-- scc_rt_abort, listing lines 1195–1198
block_spec scc_rt_abort_12 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_write")

-- scc_rt_abort, listing lines 1200–1203
block_spec scc_rt_abort_13 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp]
movz x10, #5
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.9_is8")

-- scc_rt_abort, listing lines 1204–1204
block_spec scc_rt_abort_14 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("b .L12_scc_rt_abort.10_next9")

-- scc_rt_abort, listing lines 1206–1209
block_spec scc_rt_abort_15 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_threads")

-- scc_rt_abort, listing lines 1212–1212
block_spec scc_rt_abort_16 (-32) 0 ⟨-32, [(.X29, -16)]⟩ parseAArch64("b .L12_scc_rt_abort.halt10")

-- scc_rt_abort_overflow, listing lines 1216–1219
block_spec scc_rt_abort_overflow_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")

-- scc_rt_abort_overflow, listing lines 1223–1227
block_spec scc_rt_abort_overflow_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #34
movz x8, #64")

-- scc_rt_abort_overflow, listing lines 1229–1231
block_spec scc_rt_abort_overflow_2 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")

-- scc_rt_abort_overflow, listing lines 1234–1234
block_spec scc_rt_abort_overflow_3 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #16]")

-- scc_rt_abort_overflow, listing lines 1236–1236
block_spec scc_rt_abort_overflow_4 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L13_scc_rt_abort_overflow.halt3")

-- scc_rt_abort_heap, listing lines 1240–1243
block_spec scc_rt_abort_heap_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")

-- scc_rt_abort_heap, listing lines 1247–1251
block_spec scc_rt_abort_heap_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #35
movz x8, #64")

-- scc_rt_abort_heap, listing lines 1253–1255
block_spec scc_rt_abort_heap_2 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")

-- scc_rt_abort_heap, listing lines 1258–1258
block_spec scc_rt_abort_heap_3 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #16]")

-- scc_rt_abort_heap, listing lines 1260–1260
block_spec scc_rt_abort_heap_4 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L14_scc_rt_abort_heap.halt3")

-- scc_rt_abort_stack, listing lines 1264–1267
block_spec scc_rt_abort_stack_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")

-- scc_rt_abort_stack, listing lines 1271–1275
block_spec scc_rt_abort_stack_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #25
movz x8, #64")

-- scc_rt_abort_stack, listing lines 1277–1279
block_spec scc_rt_abort_stack_2 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")

-- scc_rt_abort_stack, listing lines 1282–1282
block_spec scc_rt_abort_stack_3 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #16]")

-- scc_rt_abort_stack, listing lines 1284–1284
block_spec scc_rt_abort_stack_4 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L15_scc_rt_abort_stack.halt3")

-- scc_rt_abort_write, listing lines 1288–1291
block_spec scc_rt_abort_write_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")

-- scc_rt_abort_write, listing lines 1295–1299
block_spec scc_rt_abort_write_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #44
movz x8, #64")

-- scc_rt_abort_write, listing lines 1301–1303
block_spec scc_rt_abort_write_2 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")

-- scc_rt_abort_write, listing lines 1306–1306
block_spec scc_rt_abort_write_3 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #16]")

-- scc_rt_abort_write, listing lines 1308–1308
block_spec scc_rt_abort_write_4 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L16_scc_rt_abort_write.halt3")

-- scc_rt_abort_threads, listing lines 1312–1315
block_spec scc_rt_abort_threads_0 (-48) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")

-- scc_rt_abort_threads, listing lines 1319–1323
block_spec scc_rt_abort_threads_1 (-48) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #35
movz x8, #64")

-- scc_rt_abort_threads, listing lines 1325–1327
block_spec scc_rt_abort_threads_2 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")

-- scc_rt_abort_threads, listing lines 1330–1330
block_spec scc_rt_abort_threads_3 (-48) 0 ⟨-48, []⟩ parseAArch64("str x0, [sp, #16]")

-- scc_rt_abort_threads, listing lines 1332–1332
block_spec scc_rt_abort_threads_4 (-48) 0 ⟨-48, []⟩ parseAArch64("b .L17_scc_rt_abort_threads.halt3")

-- scc_rt_thr_worker, listing lines 1337–1338
block_spec scc_rt_thr_worker_0 (-80) 0 ⟨0, []⟩ parseAArch64("sub x9, sp, #80
mrs x10, tpidr_el0")

-- scc_rt_thr_worker, listing lines 1340–1341
block_spec scc_rt_thr_worker_1 (-80) 0 ⟨0, [(.X9, -80)]⟩ parseAArch64("subs xzr, x9, x10
b.lo .L18_scc_rt_thr_worker.stack_grow")

-- scc_rt_thr_worker, listing lines 1342–1346
block_spec scc_rt_thr_worker_2 (-80) 0 ⟨0, [(.X9, -80)]⟩ parseAArch64("add sp, x9, #0
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
str x0, [sp]")

-- scc_rt_thr_worker, listing lines 1348–1348
block_spec scc_rt_thr_worker_3 (-80) 0 ⟨-80, [(.X29, -16), (.X9, -80)]⟩ parseAArch64("ldr x10, [sp]")

-- scc_rt_thr_worker, listing lines 1350–1351
block_spec scc_rt_thr_worker_4 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #8]
ldr x10, [sp]")

-- scc_rt_thr_worker, listing lines 1353–1354
block_spec scc_rt_thr_worker_5 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #16]
ldr x10, [sp]")

-- scc_rt_thr_worker, listing lines 1356–1357
block_spec scc_rt_thr_worker_6 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #24]
ldr x10, [sp]")

-- scc_rt_thr_worker, listing lines 1359–1360
block_spec scc_rt_thr_worker_7 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #32]
ldr x10, [sp]")

-- scc_rt_thr_worker, listing lines 1362–1363
block_spec scc_rt_thr_worker_8 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #40]
ldr x10, [sp]")

-- scc_rt_thr_worker, listing lines 1365–1372
block_spec scc_rt_thr_worker_9 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #48]
ldr x0, [sp, #8]
ldr x1, [sp, #16]
ldr x2, [sp, #24]
ldr x3, [sp, #32]
ldr x4, [sp, #40]
ldr x5, [sp, #48]
bl wc_worker")

-- scc_rt_thr_worker, listing lines 1374–1376
block_spec scc_rt_thr_worker_10 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("movz x9, #1
ldr x10, [sp]
add x10, x10, #24")

-- scc_rt_thr_worker, listing lines 1378–1379
block_spec scc_rt_thr_worker_11 (-80) 0 ⟨-80, []⟩ parseAArch64("movz x0, #0
movz x8, #93")

-- scc_rt_thr_worker, listing lines 1381–1381
block_spec scc_rt_thr_worker_12 (-80) 0 ⟨-80, []⟩ parseAArch64("str x0, [sp, #56]")

-- scc_rt_thr_worker, listing lines 1383–1383
block_spec scc_rt_thr_worker_13 (-80) 0 ⟨-80, []⟩ parseAArch64("b .L18_scc_rt_thr_worker.halt9")

-- scc_rt_thr_worker, listing lines 1385–1398
block_spec scc_rt_thr_worker_14 (-80) 0 ⟨0, [(.X9, -80)]⟩ parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #80
bl scc_rt_morestack")

-- scc_rt_thr_worker, listing lines 1400–1411
block_spec scc_rt_thr_worker_15 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L18_scc_rt_thr_worker.stack_check")

-- wc_spin, listing lines 1416–1417
block_spec wc_spin_0 (-80) 0 ⟨0, []⟩ parseAArch64("sub x9, sp, #32
mrs x10, tpidr_el0")

-- wc_spin, listing lines 1419–1420
block_spec wc_spin_1 (-80) 0 ⟨0, [(.X9, -32)]⟩ parseAArch64("subs xzr, x9, x10
b.lo .L19_wc_spin.stack_grow")

-- wc_spin, listing lines 1421–1425
block_spec wc_spin_2 (-80) 0 ⟨0, [(.X9, -32)]⟩ parseAArch64("add sp, x9, #0
str x29, [sp, #16]
str x30, [sp, #24]
add x29, sp, #16
str x0, [sp]")

-- wc_spin, listing lines 1427–1431
block_spec wc_spin_3 (-80) 0 ⟨-32, [(.X29, -16), (.X9, -32)]⟩ parseAArch64("ldr x0, [sp]
ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b wc_spin")

-- wc_spin, listing lines 1433–1446
block_spec wc_spin_4 (-80) 0 ⟨0, [(.X9, -32)]⟩ parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #32
bl scc_rt_morestack")

-- wc_spin, listing lines 1448–1459
block_spec wc_spin_5 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L19_wc_spin.stack_check")

-- wc_emit8, listing lines 1464–1465
block_spec wc_emit8_0 (-416) 0 ⟨0, []⟩ parseAArch64("sub x9, sp, #416
mrs x10, tpidr_el0")

-- wc_emit8, listing lines 1467–1468
block_spec wc_emit8_1 (-416) 0 ⟨0, [(.X9, -416)]⟩ parseAArch64("subs xzr, x9, x10
b.lo .L20_wc_emit8.stack_grow")

-- wc_emit8, listing lines 1469–1474
block_spec wc_emit8_2 (-416) 0 ⟨0, [(.X9, -416)]⟩ parseAArch64("add sp, x9, #0
str x29, [sp, #400]
str x30, [sp, #408]
add x29, sp, #400
str x0, [sp]
str x1, [sp, #8]")

-- wc_emit8, listing lines 1476–1499
block_spec wc_emit8_3 (-416) 0 ⟨-416, [(.X29, -16), (.X9, -416)]⟩ parseAArch64("movz x9, #0
movz x10, #7
and x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #24]
ldr x9, [sp]
ldr x10, [sp, #24]
lsrv x9, x9, x10
str x9, [sp, #32]
ldr x9, [sp, #32]
ubfm x9, x9, #0, #7
str x9, [sp, #40]
ldr x9, [sp, #8]
movz x10, #0
subs xzr, x9, x10
csinc x9, xzr, xzr, ne
str x9, [sp, #48]
ldr x9, [sp, #48]
movz x10, #1
subs xzr, x9, x10
b.eq .L20_wc_emit8.1_then5")

-- wc_emit8, listing lines 1500–1500
block_spec wc_emit8_4 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("b .L20_wc_emit8.2_else6")

-- wc_emit8, listing lines 1502–1506
block_spec wc_emit8_5 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #8]
ldr x29, [sp, #400]
ldr x30, [sp, #408]
add sp, sp, #416
ret")

-- wc_emit8, listing lines 1508–1535
block_spec wc_emit8_6 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #8]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #56]
movz x9, #1
movz x10, #7
and x9, x9, x10
str x9, [sp, #64]
ldr x9, [sp, #64]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #72]
ldr x9, [sp]
ldr x10, [sp, #72]
lsrv x9, x9, x10
str x9, [sp, #80]
ldr x9, [sp, #80]
ubfm x9, x9, #0, #7
str x9, [sp, #88]
ldr x9, [sp, #56]
movz x10, #0
subs xzr, x9, x10
csinc x9, xzr, xzr, ne
str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #1
subs xzr, x9, x10
b.eq .L20_wc_emit8.3_then13")

-- wc_emit8, listing lines 1536–1536
block_spec wc_emit8_7 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("b .L20_wc_emit8.4_else14")

-- wc_emit8, listing lines 1538–1542
block_spec wc_emit8_8 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #56]
ldr x29, [sp, #400]
ldr x30, [sp, #408]
add sp, sp, #416
ret")

-- wc_emit8, listing lines 1544–1571
block_spec wc_emit8_9 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #56]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #104]
movz x9, #2
movz x10, #7
and x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #112]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #120]
ldr x9, [sp]
ldr x10, [sp, #120]
lsrv x9, x9, x10
str x9, [sp, #128]
ldr x9, [sp, #128]
ubfm x9, x9, #0, #7
str x9, [sp, #136]
ldr x9, [sp, #104]
movz x10, #0
subs xzr, x9, x10
csinc x9, xzr, xzr, ne
str x9, [sp, #144]
ldr x9, [sp, #144]
movz x10, #1
subs xzr, x9, x10
b.eq .L20_wc_emit8.5_then21")

-- wc_emit8, listing lines 1572–1572
block_spec wc_emit8_10 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("b .L20_wc_emit8.6_else22")

-- wc_emit8, listing lines 1574–1578
block_spec wc_emit8_11 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #104]
ldr x29, [sp, #400]
ldr x30, [sp, #408]
add sp, sp, #416
ret")

-- wc_emit8, listing lines 1580–1607
block_spec wc_emit8_12 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #104]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #152]
movz x9, #3
movz x10, #7
and x9, x9, x10
str x9, [sp, #160]
ldr x9, [sp, #160]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #168]
ldr x9, [sp]
ldr x10, [sp, #168]
lsrv x9, x9, x10
str x9, [sp, #176]
ldr x9, [sp, #176]
ubfm x9, x9, #0, #7
str x9, [sp, #184]
ldr x9, [sp, #152]
movz x10, #0
subs xzr, x9, x10
csinc x9, xzr, xzr, ne
str x9, [sp, #192]
ldr x9, [sp, #192]
movz x10, #1
subs xzr, x9, x10
b.eq .L20_wc_emit8.7_then29")

-- wc_emit8, listing lines 1608–1608
block_spec wc_emit8_13 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("b .L20_wc_emit8.8_else30")

-- wc_emit8, listing lines 1610–1614
block_spec wc_emit8_14 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #152]
ldr x29, [sp, #400]
ldr x30, [sp, #408]
add sp, sp, #416
ret")

-- wc_emit8, listing lines 1616–1643
block_spec wc_emit8_15 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #152]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #200]
movz x9, #4
movz x10, #7
and x9, x9, x10
str x9, [sp, #208]
ldr x9, [sp, #208]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #216]
ldr x9, [sp]
ldr x10, [sp, #216]
lsrv x9, x9, x10
str x9, [sp, #224]
ldr x9, [sp, #224]
ubfm x9, x9, #0, #7
str x9, [sp, #232]
ldr x9, [sp, #200]
movz x10, #0
subs xzr, x9, x10
csinc x9, xzr, xzr, ne
str x9, [sp, #240]
ldr x9, [sp, #240]
movz x10, #1
subs xzr, x9, x10
b.eq .L20_wc_emit8.9_then37")

-- wc_emit8, listing lines 1644–1644
block_spec wc_emit8_16 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("b .L20_wc_emit8.10_else38")

-- wc_emit8, listing lines 1646–1650
block_spec wc_emit8_17 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #200]
ldr x29, [sp, #400]
ldr x30, [sp, #408]
add sp, sp, #416
ret")

-- wc_emit8, listing lines 1652–1679
block_spec wc_emit8_18 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #200]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #248]
movz x9, #5
movz x10, #7
and x9, x9, x10
str x9, [sp, #256]
ldr x9, [sp, #256]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #264]
ldr x9, [sp]
ldr x10, [sp, #264]
lsrv x9, x9, x10
str x9, [sp, #272]
ldr x9, [sp, #272]
ubfm x9, x9, #0, #7
str x9, [sp, #280]
ldr x9, [sp, #248]
movz x10, #0
subs xzr, x9, x10
csinc x9, xzr, xzr, ne
str x9, [sp, #288]
ldr x9, [sp, #288]
movz x10, #1
subs xzr, x9, x10
b.eq .L20_wc_emit8.11_then45")

-- wc_emit8, listing lines 1680–1680
block_spec wc_emit8_19 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("b .L20_wc_emit8.12_else46")

-- wc_emit8, listing lines 1682–1686
block_spec wc_emit8_20 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #248]
ldr x29, [sp, #400]
ldr x30, [sp, #408]
add sp, sp, #416
ret")

-- wc_emit8, listing lines 1688–1715
block_spec wc_emit8_21 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #248]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #296]
movz x9, #6
movz x10, #7
and x9, x9, x10
str x9, [sp, #304]
ldr x9, [sp, #304]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #312]
ldr x9, [sp]
ldr x10, [sp, #312]
lsrv x9, x9, x10
str x9, [sp, #320]
ldr x9, [sp, #320]
ubfm x9, x9, #0, #7
str x9, [sp, #328]
ldr x9, [sp, #296]
movz x10, #0
subs xzr, x9, x10
csinc x9, xzr, xzr, ne
str x9, [sp, #336]
ldr x9, [sp, #336]
movz x10, #1
subs xzr, x9, x10
b.eq .L20_wc_emit8.13_then53")

-- wc_emit8, listing lines 1716–1716
block_spec wc_emit8_22 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("b .L20_wc_emit8.14_else54")

-- wc_emit8, listing lines 1718–1722
block_spec wc_emit8_23 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #296]
ldr x29, [sp, #400]
ldr x30, [sp, #408]
add sp, sp, #416
ret")

-- wc_emit8, listing lines 1724–1751
block_spec wc_emit8_24 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #296]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #344]
movz x9, #7
movz x10, #7
and x9, x9, x10
str x9, [sp, #352]
ldr x9, [sp, #352]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #360]
ldr x9, [sp]
ldr x10, [sp, #360]
lsrv x9, x9, x10
str x9, [sp, #368]
ldr x9, [sp, #368]
ubfm x9, x9, #0, #7
str x9, [sp, #376]
ldr x9, [sp, #344]
movz x10, #0
subs xzr, x9, x10
csinc x9, xzr, xzr, ne
str x9, [sp, #384]
ldr x9, [sp, #384]
movz x10, #1
subs xzr, x9, x10
b.eq .L20_wc_emit8.15_then61")

-- wc_emit8, listing lines 1752–1752
block_spec wc_emit8_25 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("b .L20_wc_emit8.16_else62")

-- wc_emit8, listing lines 1754–1758
block_spec wc_emit8_26 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #344]
ldr x29, [sp, #400]
ldr x30, [sp, #408]
add sp, sp, #416
ret")

-- wc_emit8, listing lines 1760–1768
block_spec wc_emit8_27 (-416) 0 ⟨-416, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #344]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #392]
ldr x0, [sp, #392]
ldr x29, [sp, #400]
ldr x30, [sp, #408]
add sp, sp, #416
ret")

-- wc_emit8, listing lines 1770–1783
block_spec wc_emit8_28 (-416) 0 ⟨0, [(.X9, -416)]⟩ parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #416
bl scc_rt_morestack")

-- wc_emit8, listing lines 1785–1796
block_spec wc_emit8_29 (-416) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L20_wc_emit8.stack_check")

-- wc_printL, listing lines 1801–1802
block_spec wc_printL_0 (-128) 0 ⟨0, []⟩ parseAArch64("sub x9, sp, #128
mrs x10, tpidr_el0")

-- wc_printL, listing lines 1804–1805
block_spec wc_printL_1 (-128) 0 ⟨0, [(.X9, -128)]⟩ parseAArch64("subs xzr, x9, x10
b.lo .L21_wc_printL.stack_grow")

-- wc_printL, listing lines 1806–1814
block_spec wc_printL_2 (-128) 0 ⟨0, [(.X9, -128)]⟩ parseAArch64("add sp, x9, #0
str x29, [sp, #112]
str x30, [sp, #120]
add x29, sp, #112
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]")

-- wc_printL, listing lines 1816–1831
block_spec wc_printL_3 (-128) 0 ⟨-128, [(.X29, -16), (.X9, -128)]⟩ parseAArch64("ldr x9, [sp, #16]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #40]
ldr x9, [sp, #8]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #48]
ubfm x9, x9, #0, #31
str x9, [sp, #56]
ldr x9, [sp]
ldr x10, [sp, #56]
add x9, x9, x10
str x9, [sp, #64]
ldr x10, [sp, #64]")

-- wc_printL, listing lines 1833–1836
block_spec wc_printL_4 (-128) 0 ⟨-128, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #72]
ldr x0, [sp, #72]
ldr x1, [sp, #32]
bl wc_emit8")

-- wc_printL, listing lines 1838–1842
block_spec wc_printL_5 (-128) 0 ⟨-128, [(.X29, -16)]⟩ parseAArch64("str x0, [sp, #80]
ldr x9, [sp, #24]
movz x10, #0
subs xzr, x9, x10
b.eq .L21_wc_printL.1_then6")

-- wc_printL, listing lines 1843–1843
block_spec wc_printL_6 (-128) 0 ⟨-128, [(.X29, -16)]⟩ parseAArch64("b .L21_wc_printL.2_else7")

-- wc_printL, listing lines 1845–1849
block_spec wc_printL_7 (-128) 0 ⟨-128, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp, #80]
ldr x29, [sp, #112]
ldr x30, [sp, #120]
add sp, sp, #128
ret")

-- wc_printL, listing lines 1851–1859
block_spec wc_printL_8 (-128) 0 ⟨-128, [(.X29, -16)]⟩ parseAArch64("ldr x9, [sp, #24]
movz x10, #1
subs x9, x9, x10
csel x9, x9, xzr, hs
str x9, [sp, #88]
ldr x9, [sp, #16]
movz x10, #1
adds x9, x9, x10
b.hs .L21_wc_printL.abort_overflow")

-- wc_printL, listing lines 1860–1869
block_spec wc_printL_9 (-128) 0 ⟨-128, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #96]
ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #96]
ldr x3, [sp, #88]
ldr x4, [sp, #80]
ldr x29, [sp, #112]
ldr x30, [sp, #120]
add sp, sp, #128
b wc_printL")

-- wc_printL, listing lines 1871–1884
block_spec wc_printL_10 (-128) 0 ⟨0, [(.X9, -128)]⟩ parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #128
bl scc_rt_morestack")

-- wc_printL, listing lines 1886–1897
block_spec wc_printL_11 (-128) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L21_wc_printL.stack_check")

-- wc_printL, listing lines 1899–1900
block_spec wc_printL_12 (-128) 0 ⟨-128, [(.X29, -16)]⟩ parseAArch64("movz x0, #1
bl scc_rt_abort")

-- wc_printL, listing lines 1902–1902
block_spec wc_printL_13 (-128) 0 ⟨-128, [(.X29, -16)]⟩ parseAArch64("b .L21_wc_printL.abort_overflow_halt")

-- wc_rodata, listing lines 1907–1908
block_spec wc_rodata_0 (-80) 0 ⟨0, []⟩ parseAArch64("sub x9, sp, #48
mrs x10, tpidr_el0")

-- wc_rodata, listing lines 1910–1911
block_spec wc_rodata_1 (-80) 0 ⟨0, [(.X9, -48)]⟩ parseAArch64("subs xzr, x9, x10
b.lo .L22_wc_rodata.stack_grow")

-- wc_rodata, listing lines 1912–1915
block_spec wc_rodata_2 (-80) 0 ⟨0, [(.X9, -48)]⟩ parseAArch64("add sp, x9, #0
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")

-- wc_rodata, listing lines 1917–1919
block_spec wc_rodata_3 (-80) 0 ⟨-48, [(.X29, -16), (.X9, -48)]⟩ parseAArch64("movz x0, #257
movz x1, #2
bl scc_rt_alloc")

-- wc_rodata, listing lines 1921–1922
block_spec wc_rodata_4 (-80) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x0, [sp]
ldr x10, [sp]")

-- wc_rodata, listing lines 1924–1929
block_spec wc_rodata_5 (-80) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #8]
movz x9, #25928
movk x9, #27756, lsl #16
movk x9, #11375, lsl #32
movk x9, #30496, lsl #48
ldr x10, [sp]")

-- wc_rodata, listing lines 1931–1931
block_spec wc_rodata_6 (-80) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("ldr x10, [sp]")

-- wc_rodata, listing lines 1933–1937
block_spec wc_rodata_7 (-80) 0 ⟨-48, [(.X29, -16)]⟩ parseAArch64("str x9, [sp, #16]
movz x9, #29295
movk x9, #25708, lsl #16
movk x9, #10, lsl #32
ldr x10, [sp]")

-- wc_rodata, listing lines 1940–1947
block_spec wc_rodata_8 (-80) 0 ⟨-48, []⟩ parseAArch64("ldr x0, [sp]
movz x1, #0
movz x2, #2
movz x3, #13
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

-- wc_rodata, listing lines 1949–1962
block_spec wc_rodata_9 (-80) 0 ⟨0, [(.X9, -48)]⟩ parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #48
bl scc_rt_morestack")

-- wc_rodata, listing lines 1964–1975
block_spec wc_rodata_10 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L22_wc_rodata.stack_check")

-- wc_worker, listing lines 1980–1981
block_spec wc_worker_0 (-96) 0 ⟨0, []⟩ parseAArch64("sub x9, sp, #96
mrs x10, tpidr_el0")

-- wc_worker, listing lines 1983–1984
block_spec wc_worker_1 (-96) 0 ⟨0, [(.X9, -96)]⟩ parseAArch64("subs xzr, x9, x10
b.lo .L23_wc_worker.stack_grow")

-- wc_worker, listing lines 1985–1994
block_spec wc_worker_2 (-96) 0 ⟨0, [(.X9, -96)]⟩ parseAArch64("add sp, x9, #0
str x29, [sp, #80]
str x30, [sp, #88]
add x29, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]")

-- wc_worker, listing lines 1996–2016
block_spec wc_worker_3 (-96) 0 ⟨-96, [(.X29, -16), (.X9, -96)]⟩ parseAArch64("ldr x9, [sp, #8]
ubfm x9, x9, #0, #31
str x9, [sp, #48]
ldr x9, [sp]
ldr x10, [sp, #48]
add x9, x9, x10
str x9, [sp, #56]
ldr x9, [sp, #16]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #64]
ldr x9, [sp, #24]
ldr x10, [sp, #64]
subs xzr, x9, x10
ldr x11, [sp, #24]
ldr x12, [sp, #64]
csel x9, x11, x12, lo
str x9, [sp, #72]
ldr x0, [sp, #56]
ldr x1, [sp, #72]
bl scc_rt_print")

-- wc_worker, listing lines 2018–2019
block_spec wc_worker_4 (-96) 0 ⟨-96, [(.X29, -16)]⟩ parseAArch64("movz x9, #1
ldr x10, [sp, #32]")

-- wc_worker, listing lines 2021–2022
block_spec wc_worker_5 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x0, [sp, #40]
bl scc_rt_unpark")

-- wc_worker, listing lines 2024–2027
block_spec wc_worker_6 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x29, [sp, #80]
ldr x30, [sp, #88]
add sp, sp, #96
ret")

-- wc_worker, listing lines 2029–2042
block_spec wc_worker_7 (-96) 0 ⟨0, [(.X9, -96)]⟩ parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #96
bl scc_rt_morestack")

-- wc_worker, listing lines 2044–2055
block_spec wc_worker_8 (-96) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L23_wc_worker.stack_check")

-- wc_waitLoop, listing lines 2060–2061
block_spec wc_waitLoop_0 (-80) 0 ⟨0, []⟩ parseAArch64("sub x9, sp, #32
mrs x10, tpidr_el0")

-- wc_waitLoop, listing lines 2063–2064
block_spec wc_waitLoop_1 (-80) 0 ⟨0, [(.X9, -32)]⟩ parseAArch64("subs xzr, x9, x10
b.lo .L24_wc_waitLoop.stack_grow")

-- wc_waitLoop, listing lines 2065–2069
block_spec wc_waitLoop_2 (-80) 0 ⟨0, [(.X9, -32)]⟩ parseAArch64("add sp, x9, #0
str x29, [sp, #16]
str x30, [sp, #24]
add x29, sp, #16
str x0, [sp]")

-- wc_waitLoop, listing lines 2071–2071
block_spec wc_waitLoop_3 (-80) 0 ⟨-32, [(.X29, -16), (.X9, -32)]⟩ parseAArch64("ldr x10, [sp]")

-- wc_waitLoop, listing lines 2073–2077
block_spec wc_waitLoop_4 (-80) 0 ⟨-32, []⟩ parseAArch64("str x9, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
subs xzr, x9, x10
b.eq .L24_wc_waitLoop.1_then1")

-- wc_waitLoop, listing lines 2078–2078
block_spec wc_waitLoop_5 (-80) 0 ⟨-32, []⟩ parseAArch64("b .L24_wc_waitLoop.2_else2")

-- wc_waitLoop, listing lines 2080–2084
block_spec wc_waitLoop_6 (-80) 0 ⟨-32, []⟩ parseAArch64("movz x0, #0
ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
ret")

-- wc_waitLoop, listing lines 2086–2086
block_spec wc_waitLoop_7 (-80) 0 ⟨-32, []⟩ parseAArch64("bl scc_rt_park")

-- wc_waitLoop, listing lines 2088–2092
block_spec wc_waitLoop_8 (-80) 0 ⟨-32, []⟩ parseAArch64("ldr x0, [sp]
ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b wc_waitLoop")

-- wc_waitLoop, listing lines 2094–2107
block_spec wc_waitLoop_9 (-80) 0 ⟨0, [(.X9, -32)]⟩ parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #32
bl scc_rt_morestack")

-- wc_waitLoop, listing lines 2109–2120
block_spec wc_waitLoop_10 (-80) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L24_wc_waitLoop.stack_check")

-- wc_main, listing lines 2125–2126
block_spec wc_main_0 (-96) 0 ⟨0, []⟩ parseAArch64("sub x9, sp, #96
mrs x10, tpidr_el0")

-- wc_main, listing lines 2128–2129
block_spec wc_main_1 (-96) 0 ⟨0, [(.X9, -96)]⟩ parseAArch64("subs xzr, x9, x10
b.lo .L25_wc_main.stack_grow")

-- wc_main, listing lines 2130–2138
block_spec wc_main_2 (-96) 0 ⟨0, [(.X9, -96)]⟩ parseAArch64("add sp, x9, #0
str x29, [sp, #80]
str x30, [sp, #88]
add x29, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]")

-- wc_main, listing lines 2140–2142
block_spec wc_main_3 (-96) 0 ⟨-96, [(.X29, -16), (.X9, -96)]⟩ parseAArch64("movz x0, #256
movz x1, #1
bl scc_rt_alloc")

-- wc_main, listing lines 2144–2146
block_spec wc_main_4 (-96) 0 ⟨-96, [(.X29, -16)]⟩ parseAArch64("str x0, [sp, #40]
movz x9, #0
ldr x10, [sp, #40]")

-- wc_main, listing lines 2149–2149
block_spec wc_main_5 (-96) 0 ⟨-96, []⟩ parseAArch64("bl scc_rt_thread_reserve")

-- wc_main, listing lines 2151–2155
block_spec wc_main_6 (-96) 0 ⟨-96, []⟩ parseAArch64("str x0, [sp, #48]
movz x0, #2819
movk x0, #192, lsl #16
movz x1, #1
bl scc_rt_alloc_tcb")

-- wc_main, listing lines 2157–2159
block_spec wc_main_7 (-96) 0 ⟨-96, []⟩ parseAArch64("str x0, [sp, #56]
ldr x9, [sp, #48]
ldr x10, [sp, #56]")

-- wc_main, listing lines 2161–2162
block_spec wc_main_8 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x9, [sp]
ldr x10, [sp, #56]")

-- wc_main, listing lines 2164–2165
block_spec wc_main_9 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x9, [sp, #8]
ldr x10, [sp, #56]")

-- wc_main, listing lines 2167–2168
block_spec wc_main_10 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x9, [sp, #16]
ldr x10, [sp, #56]")

-- wc_main, listing lines 2170–2171
block_spec wc_main_11 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x9, [sp, #24]
ldr x10, [sp, #56]")

-- wc_main, listing lines 2173–2174
block_spec wc_main_12 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x9, [sp, #40]
ldr x10, [sp, #56]")

-- wc_main, listing lines 2176–2177
block_spec wc_main_13 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x9, [sp, #32]
ldr x10, [sp, #56]")

-- wc_main, listing lines 2179–2180
block_spec wc_main_14 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x0, [sp, #56]
bl scc_rt_thread_init")

-- wc_main, listing lines 2182–2182
block_spec wc_main_15 (-96) 0 ⟨-96, []⟩ parseAArch64("str x0, [sp, #64]")

-- wc_main, listing lines 2184–2191
block_spec wc_main_16 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x1, [sp, #64]
ldr x3, [sp, #56]
ldr x9, [sp, #56]
movz x0, #3840
movk x0, #13, lsl #16
movz x2, #0
movz x4, #0
movz x8, #220")

-- wc_main, listing lines 2193–2193
block_spec wc_main_17 (-96) 0 ⟨-96, []⟩ parseAArch64("cbnz x0, .L25_wc_main.clone14")

-- wc_main, listing lines 2194–2196
block_spec wc_main_18 (-96) 0 ⟨-96, []⟩ parseAArch64("orr x0, xzr, x9
movz x29, #0
bl scc_rt_thr_worker")

-- wc_main, listing lines 2198–2198
block_spec wc_main_19 (-96) 0 ⟨-96, []⟩ parseAArch64("b .L25_wc_main.child14")

-- wc_main, listing lines 2200–2204
block_spec wc_main_20 (-96) 0 ⟨-96, []⟩ parseAArch64("str x0, [sp, #72]
ldr x9, [sp, #72]
movz x10, #0
subs xzr, x9, x10
b.lt .L25_wc_main.1_spawnfail5")

-- wc_main, listing lines 2205–2205
block_spec wc_main_21 (-96) 0 ⟨-96, []⟩ parseAArch64("b .L25_wc_main.2_spawned6")

-- wc_main, listing lines 2207–2208
block_spec wc_main_22 (-96) 0 ⟨-96, []⟩ parseAArch64("movz x0, #5
bl scc_rt_abort")

-- wc_main, listing lines 2211–2211
block_spec wc_main_23 (-96) 0 ⟨-96, []⟩ parseAArch64("b .L25_wc_main.halt17")

-- wc_main, listing lines 2213–2217
block_spec wc_main_24 (-96) 0 ⟨-96, []⟩ parseAArch64("ldr x0, [sp, #40]
ldr x29, [sp, #80]
ldr x30, [sp, #88]
add sp, sp, #96
b wc_waitLoop")

-- wc_main, listing lines 2219–2232
block_spec wc_main_25 (-96) 0 ⟨0, [(.X9, -96)]⟩ parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #96
bl scc_rt_morestack")

-- wc_main, listing lines 2234–2245
block_spec wc_main_26 (-96) 0 ⟨-80, [(.X29, -16)]⟩ parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L25_wc_main.stack_check")

-- scc_rt_morestack, listing lines 2249–2255
block_spec scc_rt_morestack_0 (-16) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #16
str x29, [sp]
str x30, [sp, #8]
add x29, sp, #0
orr x1, xzr, x0
orr x0, xzr, x29
bl scc_rt_grow")

-- scc_rt_morestack, listing lines 2256–2256
block_spec scc_rt_morestack_1 (-16) 0 ⟨-16, [(.X29, -16)]⟩ parseAArch64("add x29, x29, x0")

-- scc_rt_morestack, listing lines 2258–2260
block_spec scc_rt_morestack_2 (0) 16 ⟨0, []⟩ parseAArch64("orr x0, xzr, x1
orr x1, xzr, x2
bl scc_rt_stack_release")

-- scc_rt_morestack, listing lines 2261–2264
block_spec scc_rt_morestack_3 (0) 16 ⟨0, []⟩ parseAArch64("ldr x29, [sp]
ldr x30, [sp, #8]
add sp, sp, #16
ret")

end Spike.Lib.A64.Hello
