/-
**Every straight-line block of `hello.w`'s x64 code**, through `block_spec`
(`Spike/Lib/X64Block.lean`).

The text is `scc`'s listing of `Scc/Test/hello.w` for x64, written at
an earlier revision by

    scc --arch x64 -o hello.s --blocks X64Hello.blocks.lean Scc/Test/hello.w

and copied here as data: each block is a maximal run of covered
instructions (stack loads and stores, `push`/`pop`, register operations)
ending at a label, at an uncovered instruction, or with a branch (`jmp`,
`jcc`, `call`, `ret`), parsed by Kraken's own x64 parser (`parse`) and
zipped with the assembler's sizes of its instructions in bytes (the cells
of `CodeAt`). The comment above each block gives its function, its line
numbers in the listing, and its address: a label plus a byte offset.

Each block's region and entry offsets come from a static-offset pass over
its function: on entry `%rsp` is at offset 8 from the region's base (the
return address is the cell `[8, 16)`), offsets flow along fall-through and
branch edges (at a label, the meet of all incoming edges, to a fixpoint), a
`call` keeps `%rsp` and the callee-saved registers, and an uncovered
instruction forgets its destination register. The region is `[lo, 16)`, `lo`
the least offset the function accesses. `block_spec name lo hi o b` proves
`name_ok : okBlk lo hi o b = true` (by `decide`: every directive classified,
every access inside the region, only the last directive a branch), so that
`seg_block` applies, and `name_run : ∀ lab pc σ, arun lab b ⟨pc, o, σ⟩ = …`,
the block's exit pc, offsets and abstract state in closed form (by `simp`).

Coverage (instructions of the listing's text; directives, labels and data
are not counted):

| | instructions | covered | undefined flags | non-frame memory | system | other |
|---|---|---|---|---|---|---|
| compiled functions (`wc_*`) | 642 | 585 (91.1%) | 30 | 15 | 4 | 8 |
| runtime (`scc_rt_*`) | 1143 | 994 (87.0%) | 37 | 41 | 33 | 38 |
| total | 1785 | 1579 (88.5%) | | | | |

"Undefined flags": `and`/`or`/`xor`/`test`/`imul`/shifts, whose undefined
flags are a choice in Kraken's event; they end blocks, and 66 of them (30 +
36: the register forms, the shifts by `%cl` and the zeroing `xorl %r32,
%r32`) are nodes of their own (`flag_nd`, `Spike/Lib/X64Flags.lean`), as
are the 23 label addresses (`leaq L(%rip)`: `si_nd`,
`Spike/Lib/X64Nodes.lean`) and the 3 stack switches (`movq %r, %rsp`,
`andq $k, %rsp`: `sw_nd`, `swand_nd`, `Spike/Lib/X64Switch.lean`; after a
switch the offsets restart at 0 in a region based at the new `%rsp`), which
brings the covered counts to 615 (95.8%), 1056 (92.4%) and 1671 (93.6%).
The system calls are nodes too (`syscall_nd`, through `Out.sys`;
`arch_prctl` excluded): 5 with no kernel event (`rt_sigaction`,
`exit_group`, `futex`, `exit`), 5 abort exits whose number is set before
their label, and 7 `write`/`clone` (1 in compiled functions) matched for
the thread's control only; with all 17 the counts are 616 (96.0%), 1072
(93.8%) and 1688 (94.6%). "Other": thread-pointer loads (7 + 4), shared
memory (1 + 9), label addresses (23) and stack switches (2). The
thread-pointer loads `movq %fs:k, %r` are nodes too (`fsld_nd`, through
`Out.rtLoad`), which brings the counts to 623 (97.0%), 1076 (94.1%) and
1699 (95.2%); so are the `ud2` after a call that does not return or after
`exit_group` (3 + 16: `dead_nd`, `Spike/Lib/X64Dead.lean`, a node no run
reaches), which brings them to 626 (97.5%), 1092 (95.5%) and 1718 (96.2%).
411 blocks
(139 in compiled functions), 1 to 19 instructions each, 203 of them ending
with a branch. The whole file checks in 28 s (wall) with 1.9 GB of memory.
-/
import Spike.Lib.X64Block
import Kraken.X64.Parser

namespace Spike.Lib.X64.Hello

open Kraken Kraken.X64.Parser Spike.Lib.X64

-- _start, listing lines 8–8, at _start + 6
block_spec _start_0 (-8) 0 ⟨0, []⟩ (parse("call scc_rt_start")).zip [5]

-- scc_rt_start, listing lines 14–16, at scc_rt_start + 0
block_spec scc_rt_start_0 (-40) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]

-- scc_rt_start, listing lines 19–24, at .Lscc_rt_start.entry + 7
block_spec scc_rt_start_1 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -8(%rbp)
movq $13, %rdi
movq -8(%rbp), %rsi
movq $0, %rdx
movq $8, %r10
movl $13, %eax")).zip [4, 7, 4, 7, 7, 5]

-- scc_rt_start, listing lines 26–29, at .Lscc_rt_start.entry + 43
block_spec scc_rt_start_2 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq $2051, %rdi
movq $1, %rsi
call scc_rt_alloc_tcb")).zip [4, 7, 7, 5]

-- scc_rt_start, listing lines 31–33, at .Lscc_rt_start.x0 + 0
block_spec scc_rt_start_3 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rdi
call scc_rt_thread_init")).zip [4, 4, 5]

-- scc_rt_start, listing lines 35–38, at .Lscc_rt_start.x1 + 0
block_spec scc_rt_start_4 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -32(%rbp)
movq -24(%rbp), %rsi
movl $4098, %edi
movl $158, %eax")).zip [4, 4, 5, 5]

-- scc_rt_start, listing lines 40–41, at .Lscc_rt_start.x1 + 20
block_spec scc_rt_start_5 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -32(%rbp), %rax
movq -24(%rbp), %rdi")).zip [4, 4]

-- scc_rt_start, listing lines 44–44, at .Lscc_rt_start.x1 + 33
block_spec scc_rt_start_6 (-8) 0 ⟨0, []⟩ (parse("call scc_rt_main")).zip [5]

-- scc_rt_main, listing lines 51–52, at scc_rt_main + 0
block_spec scc_rt_main_0 (-72) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]

-- scc_rt_main, listing lines 54–54, at .Lscc_rt_main.chk + 0
block_spec scc_rt_main_1 (-72) 16 ⟨0, [(.rbp, 0)]⟩ (parse("leaq -64(%rsp), %rax")).zip [5]

-- scc_rt_main, listing lines 56–57, at .Lscc_rt_main.chk + 14
block_spec scc_rt_main_2 (-72) 16 ⟨0, [(.rax, -64), (.rbp, 0)]⟩ (parse("cmpq %r11, %rax
jb .Lscc_rt_main.stk")).zip [3, 2]

-- scc_rt_main, listing lines 58–59, at .Lscc_rt_main.chk + 19
block_spec scc_rt_main_3 (-72) 16 ⟨0, [(.rax, -64), (.rbp, 0)]⟩ (parse("subq $64, %rsp
movq %rdi, -8(%rbp)")).zip [4, 4]

-- scc_rt_main, listing lines 61–61, at .Lscc_rt_main.entry + 0
block_spec scc_rt_main_4 (-72) 16 ⟨-64, [(.rax, -64), (.rbp, 0)]⟩ (parse("call wc_rodata")).zip [5]

-- scc_rt_main, listing lines 63–72, at .Lscc_rt_main.x2 + 0
block_spec scc_rt_main_5 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq %rdx, -24(%rbp)
movq %rcx, -32(%rbp)
movq %rsi, -40(%rbp)
movq -16(%rbp), %rdi
movq -24(%rbp), %rsi
movq -32(%rbp), %rdx
movq -40(%rbp), %rcx
movq -8(%rbp), %r8
call wc_main")).zip [4, 4, 4, 4, 4, 4, 4, 4, 4, 5]

-- scc_rt_main, listing lines 74–76, at .Lscc_rt_main.x3 + 0
block_spec scc_rt_main_6 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -48(%rbp)
movq -48(%rbp), %rdi
movl $231, %eax")).zip [4, 4, 5]

-- scc_rt_main, listing lines 78–78, at .Lscc_rt_main.x3 + 15
block_spec scc_rt_main_7 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -56(%rbp)")).zip [4]

-- scc_rt_main, listing lines 81–88, at .Lscc_rt_main.stk + 0
block_spec scc_rt_main_8 (-72) 16 ⟨0, [(.rax, -64), (.rbp, 0)]⟩ (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $64, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]

-- scc_rt_main, listing lines 90–96, at .Lscc_rt_main.x4 + 0
block_spec scc_rt_main_9 (-72) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lscc_rt_main.chk")).zip [2, 2, 1, 1, 1, 1, 2]

-- scc_rt_alloc, listing lines 102–106, at scc_rt_alloc + 0
block_spec scc_rt_alloc_0 (-184) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $176, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)")).zip [1, 3, 7, 4, 4]

-- scc_rt_alloc, listing lines 108–111, at .Lscc_rt_alloc.entry + 0
block_spec scc_rt_alloc_1 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq -16(%rbp), %rax
movq $268435456, %rcx
cmpq %rcx, %rax
jae .Lscc_rt_alloc.full")).zip [4, 7, 3, 6]

-- scc_rt_alloc, listing lines 112–112, at .Lscc_rt_alloc.entry + 20
block_spec scc_rt_alloc_2 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_alloc.len")).zip [2]

-- scc_rt_alloc, listing lines 114–115, at .Lscc_rt_alloc.len + 0
block_spec scc_rt_alloc_3 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $8, %rcx")).zip [4, 7]

-- scc_rt_alloc, listing lines 117–119, at .Lscc_rt_alloc.len + 14
block_spec scc_rt_alloc_4 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $16383, %rcx")).zip [4, 4, 7]

-- scc_rt_alloc, listing lines 121–123, at .Lscc_rt_alloc.len + 32
block_spec scc_rt_alloc_5 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -32(%rbp)
movq -8(%rbp), %rax
movq $22, %rcx")).zip [4, 4, 7]

-- scc_rt_alloc, listing lines 125–127, at .Lscc_rt_alloc.len + 50
block_spec scc_rt_alloc_6 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -40(%rbp)
movq -40(%rbp), %rax
movq $16383, %rcx")).zip [4, 4, 7]

-- scc_rt_alloc, listing lines 129–135, at .Lscc_rt_alloc.len + 68
block_spec scc_rt_alloc_7 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -48(%rbp)
movq -32(%rbp), %rax
movq -48(%rbp), %rcx
addq %rcx, %rax
movq %rax, -56(%rbp)
movq -16(%rbp), %rax
movq -56(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 4]

-- scc_rt_alloc, listing lines 137–143, at .Lscc_rt_alloc.len + 99
block_spec scc_rt_alloc_8 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -64(%rbp)
movq -64(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -72(%rbp)
movq -72(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7, 3, 4, 4, 7]

-- scc_rt_alloc, listing lines 145–145, at .Lscc_rt_alloc.len + 135
block_spec scc_rt_alloc_9 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -80(%rbp)")).zip [4]

-- scc_rt_alloc, listing lines 147–149, at .Lscc_rt_alloc.len + 146
block_spec scc_rt_alloc_10 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -88(%rbp)
movq -88(%rbp), %rcx
movq -80(%rbp), %rax")).zip [4, 4, 4]

-- scc_rt_alloc, listing lines 151–159, at .Lscc_rt_alloc.len + 163
block_spec scc_rt_alloc_11 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq -80(%rbp), %rcx
addq %rcx, %rax
movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $67108864, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_alloc.full")).zip [4, 4, 4, 3, 4, 4, 7, 3, 2]

-- scc_rt_alloc, listing lines 160–160, at .Lscc_rt_alloc.len + 198
block_spec scc_rt_alloc_12 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_alloc.ok")).zip [2]

-- scc_rt_alloc, listing lines 162–163, at .Lscc_rt_alloc.full + 0
block_spec scc_rt_alloc_13 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq $2, %rdi
call scc_rt_abort")).zip [7, 5]

-- scc_rt_alloc, listing lines 168–174, at .Lscc_rt_alloc.ok + 7
block_spec scc_rt_alloc_14 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -112(%rbp)
movq -112(%rbp), %rax
movq -96(%rbp), %rcx
addq %rcx, %rax
movq %rax, -120(%rbp)
movq -16(%rbp), %rax
movq -48(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 4]

-- scc_rt_alloc, listing lines 176–178, at .Lscc_rt_alloc.ok + 38
block_spec scc_rt_alloc_15 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -128(%rbp)
movq -128(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7]

-- scc_rt_alloc, listing lines 180–182, at .Lscc_rt_alloc.ok + 56
block_spec scc_rt_alloc_16 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -136(%rbp)
movq -16(%rbp), %rax
movq $36, %rcx")).zip [7, 4, 7]

-- scc_rt_alloc, listing lines 184–186, at .Lscc_rt_alloc.ok + 77
block_spec scc_rt_alloc_17 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -144(%rbp)
movq -8(%rbp), %rax
movq -144(%rbp), %rcx")).zip [7, 4, 7]

-- scc_rt_alloc, listing lines 188–194, at .Lscc_rt_alloc.ok + 98
block_spec scc_rt_alloc_18 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -152(%rbp)
movq -120(%rbp), %rax
movq -136(%rbp), %rcx
addq %rcx, %rax
movq %rax, -160(%rbp)
movq -160(%rbp), %rcx
movq -152(%rbp), %rax")).zip [7, 4, 7, 3, 7, 7, 7]

-- scc_rt_alloc, listing lines 196–207, at .Lscc_rt_alloc.ok + 143
block_spec scc_rt_alloc_19 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq -120(%rbp), %rax
movq -136(%rbp), %rcx
addq %rcx, %rax
movq %rax, -168(%rbp)
movq -168(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -176(%rbp)
movq -176(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 7, 3, 7, 7, 7, 3, 7, 7, 3, 1, 1]

-- scc_rt_alloc_tcb, listing lines 213–217, at scc_rt_alloc_tcb + 0
block_spec scc_rt_alloc_tcb_0 (-184) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $176, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)")).zip [1, 3, 7, 4, 4]

-- scc_rt_alloc_tcb, listing lines 219–222, at .Lscc_rt_alloc_tcb.entry + 0
block_spec scc_rt_alloc_tcb_1 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq -16(%rbp), %rax
movq $268435456, %rcx
cmpq %rcx, %rax
jae .Lscc_rt_alloc_tcb.full")).zip [4, 7, 3, 6]

-- scc_rt_alloc_tcb, listing lines 223–223, at .Lscc_rt_alloc_tcb.entry + 20
block_spec scc_rt_alloc_tcb_2 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_alloc_tcb.len")).zip [2]

-- scc_rt_alloc_tcb, listing lines 225–226, at .Lscc_rt_alloc_tcb.len + 0
block_spec scc_rt_alloc_tcb_3 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $8, %rcx")).zip [4, 7]

-- scc_rt_alloc_tcb, listing lines 228–230, at .Lscc_rt_alloc_tcb.len + 14
block_spec scc_rt_alloc_tcb_4 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $16383, %rcx")).zip [4, 4, 7]

-- scc_rt_alloc_tcb, listing lines 232–234, at .Lscc_rt_alloc_tcb.len + 32
block_spec scc_rt_alloc_tcb_5 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -32(%rbp)
movq -8(%rbp), %rax
movq $22, %rcx")).zip [4, 4, 7]

-- scc_rt_alloc_tcb, listing lines 236–238, at .Lscc_rt_alloc_tcb.len + 50
block_spec scc_rt_alloc_tcb_6 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -40(%rbp)
movq -40(%rbp), %rax
movq $16383, %rcx")).zip [4, 4, 7]

-- scc_rt_alloc_tcb, listing lines 240–246, at .Lscc_rt_alloc_tcb.len + 68
block_spec scc_rt_alloc_tcb_7 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -48(%rbp)
movq -32(%rbp), %rax
movq -48(%rbp), %rcx
addq %rcx, %rax
movq %rax, -56(%rbp)
movq -16(%rbp), %rax
movq -56(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 4]

-- scc_rt_alloc_tcb, listing lines 248–254, at .Lscc_rt_alloc_tcb.len + 99
block_spec scc_rt_alloc_tcb_8 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -64(%rbp)
movq -64(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -72(%rbp)
movq -72(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7, 3, 4, 4, 7]

-- scc_rt_alloc_tcb, listing lines 256–256, at .Lscc_rt_alloc_tcb.len + 135
block_spec scc_rt_alloc_tcb_9 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -80(%rbp)")).zip [4]

-- scc_rt_alloc_tcb, listing lines 258–260, at .Lscc_rt_alloc_tcb.len + 146
block_spec scc_rt_alloc_tcb_10 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -88(%rbp)
movq -88(%rbp), %rcx
movq -80(%rbp), %rax")).zip [4, 4, 4]

-- scc_rt_alloc_tcb, listing lines 262–270, at .Lscc_rt_alloc_tcb.len + 163
block_spec scc_rt_alloc_tcb_11 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq -80(%rbp), %rcx
addq %rcx, %rax
movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $122880, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_alloc_tcb.full")).zip [4, 4, 4, 3, 4, 4, 7, 3, 2]

-- scc_rt_alloc_tcb, listing lines 271–271, at .Lscc_rt_alloc_tcb.len + 198
block_spec scc_rt_alloc_tcb_12 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_alloc_tcb.ok")).zip [2]

-- scc_rt_alloc_tcb, listing lines 273–274, at .Lscc_rt_alloc_tcb.full + 0
block_spec scc_rt_alloc_tcb_13 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq $5, %rdi
call scc_rt_abort")).zip [7, 5]

-- scc_rt_alloc_tcb, listing lines 279–285, at .Lscc_rt_alloc_tcb.ok + 7
block_spec scc_rt_alloc_tcb_14 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -112(%rbp)
movq -112(%rbp), %rax
movq -96(%rbp), %rcx
addq %rcx, %rax
movq %rax, -120(%rbp)
movq -16(%rbp), %rax
movq -48(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 4]

-- scc_rt_alloc_tcb, listing lines 287–289, at .Lscc_rt_alloc_tcb.ok + 38
block_spec scc_rt_alloc_tcb_15 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -128(%rbp)
movq -128(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7]

-- scc_rt_alloc_tcb, listing lines 291–293, at .Lscc_rt_alloc_tcb.ok + 56
block_spec scc_rt_alloc_tcb_16 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -136(%rbp)
movq -16(%rbp), %rax
movq $36, %rcx")).zip [7, 4, 7]

-- scc_rt_alloc_tcb, listing lines 295–297, at .Lscc_rt_alloc_tcb.ok + 77
block_spec scc_rt_alloc_tcb_17 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -144(%rbp)
movq -8(%rbp), %rax
movq -144(%rbp), %rcx")).zip [7, 4, 7]

-- scc_rt_alloc_tcb, listing lines 299–305, at .Lscc_rt_alloc_tcb.ok + 98
block_spec scc_rt_alloc_tcb_18 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq %rax, -152(%rbp)
movq -120(%rbp), %rax
movq -136(%rbp), %rcx
addq %rcx, %rax
movq %rax, -160(%rbp)
movq -160(%rbp), %rcx
movq -152(%rbp), %rax")).zip [7, 4, 7, 3, 7, 7, 7]

-- scc_rt_alloc_tcb, listing lines 307–318, at .Lscc_rt_alloc_tcb.ok + 143
block_spec scc_rt_alloc_tcb_19 (-184) 16 ⟨-176, [(.rbp, 0)]⟩ (parse("movq -120(%rbp), %rax
movq -136(%rbp), %rcx
addq %rcx, %rax
movq %rax, -168(%rbp)
movq -168(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -176(%rbp)
movq -176(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 7, 3, 7, 7, 7, 3, 7, 7, 3, 1, 1]

-- scc_rt_thread_reserve, listing lines 324–326, at scc_rt_thread_reserve + 0
block_spec scc_rt_thread_reserve_0 (-40) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]

-- scc_rt_thread_reserve, listing lines 329–331, at .Lscc_rt_thread_reserve.entry + 7
block_spec scc_rt_thread_reserve_1 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -8(%rbp)
movq -8(%rbp), %rcx
movq $1, %rax")).zip [4, 4, 7]

-- scc_rt_thread_reserve, listing lines 333–341, at .Lscc_rt_thread_reserve.entry + 27
block_spec scc_rt_thread_reserve_2 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $1023, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_thread_reserve.full")).zip [4, 4, 7, 3, 4, 4, 7, 3, 2]

-- scc_rt_thread_reserve, listing lines 342–342, at .Lscc_rt_thread_reserve.entry + 65
block_spec scc_rt_thread_reserve_3 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_thread_reserve.ok")).zip [2]

-- scc_rt_thread_reserve, listing lines 344–345, at .Lscc_rt_thread_reserve.full + 0
block_spec scc_rt_thread_reserve_4 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq $5, %rdi
call scc_rt_abort")).zip [7, 5]

-- scc_rt_thread_reserve, listing lines 349–352, at .Lscc_rt_thread_reserve.ok + 0
block_spec scc_rt_thread_reserve_5 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -24(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

-- scc_rt_thread_init, listing lines 358–361, at scc_rt_thread_init + 0
block_spec scc_rt_thread_init_0 (-40) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 4, 4]

-- scc_rt_thread_init, listing lines 363–364, at .Lscc_rt_thread_init.entry + 0
block_spec scc_rt_thread_init_1 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq $16384, %rdi
call scc_rt_stack_take")).zip [7, 5]

-- scc_rt_thread_init, listing lines 366–376, at .Lscc_rt_thread_init.x8 + 0
block_spec scc_rt_thread_init_2 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $4096, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -16(%rbp), %rax
movq $16384, %rcx
addq %rcx, %rax
movq %rax, -32(%rbp)
movq -8(%rbp), %rcx
movq -8(%rbp), %rax")).zip [4, 4, 7, 3, 4, 4, 7, 3, 4, 4, 4]

-- scc_rt_thread_init, listing lines 378–379, at .Lscc_rt_thread_init.x8 + 51
block_spec scc_rt_thread_init_3 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx
movq -24(%rbp), %rax")).zip [4, 4]

-- scc_rt_thread_init, listing lines 381–382, at .Lscc_rt_thread_init.x8 + 63
block_spec scc_rt_thread_init_4 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 7]

-- scc_rt_thread_init, listing lines 384–385, at .Lscc_rt_thread_init.x8 + 78
block_spec scc_rt_thread_init_5 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 7]

-- scc_rt_thread_init, listing lines 387–388, at .Lscc_rt_thread_init.x8 + 93
block_spec scc_rt_thread_init_6 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx
movq -16(%rbp), %rax")).zip [4, 4]

-- scc_rt_thread_init, listing lines 390–391, at .Lscc_rt_thread_init.x8 + 105
block_spec scc_rt_thread_init_7 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx
movq -32(%rbp), %rax")).zip [4, 4]

-- scc_rt_thread_init, listing lines 393–396, at .Lscc_rt_thread_init.x8 + 117
block_spec scc_rt_thread_init_8 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -32(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

-- scc_rt_stack_take, listing lines 402–405, at scc_rt_stack_take + 0
block_spec scc_rt_stack_take_0 (-200) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $192, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 7, 4]

-- scc_rt_stack_take, listing lines 407–415, at .Lscc_rt_stack_take.entry + 0
block_spec scc_rt_stack_take_1 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq $16384, %rax
movq %rax, -16(%rbp)
movq $0, %rax
movq %rax, -24(%rbp)
movq $32768, %rax
movq %rax, -32(%rbp)
movq $0, %rax
movq %rax, -40(%rbp)
jmp .Lscc_rt_stack_take.cls5")).zip [7, 4, 7, 4, 7, 4, 7, 4, 2]

-- scc_rt_stack_take, listing lines 417–420, at .Lscc_rt_stack_take.cls5 + 0
block_spec scc_rt_stack_take_2 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq -16(%rbp), %rax
movq -8(%rbp), %rcx
cmpq %rcx, %rax
jb .Lscc_rt_stack_take.clsnext6")).zip [4, 4, 3, 2]

-- scc_rt_stack_take, listing lines 421–421, at .Lscc_rt_stack_take.cls5 + 13
block_spec scc_rt_stack_take_3 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_stack_take.clsdone7")).zip [2]

-- scc_rt_stack_take, listing lines 423–424, at .Lscc_rt_stack_take.clsnext6 + 0
block_spec scc_rt_stack_take_4 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq -32(%rbp), %rax
movq $3, %rcx")).zip [4, 7]

-- scc_rt_stack_take, listing lines 426–432, at .Lscc_rt_stack_take.clsnext6 + 14
block_spec scc_rt_stack_take_5 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -48(%rbp)
movq -24(%rbp), %rax
movq -48(%rbp), %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -32(%rbp), %rax
movq $1, %rcx")).zip [4, 4, 4, 3, 4, 4, 7]

-- scc_rt_stack_take, listing lines 434–436, at .Lscc_rt_stack_take.clsnext6 + 47
block_spec scc_rt_stack_take_6 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -32(%rbp)
movq -16(%rbp), %rax
movq $1, %rcx")).zip [4, 4, 7]

-- scc_rt_stack_take, listing lines 438–443, at .Lscc_rt_stack_take.clsnext6 + 65
block_spec scc_rt_stack_take_7 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq -40(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -40(%rbp)
jmp .Lscc_rt_stack_take.cls5")).zip [4, 4, 7, 3, 4, 2]

-- scc_rt_stack_take, listing lines 446–450, at .Lscc_rt_stack_take.clsdone7 + 7
block_spec scc_rt_stack_take_8 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -56(%rbp)
movq -56(%rbp), %rax
movq -40(%rbp), %rcx
addq %rcx, %rax
movq %rax, -64(%rbp)")).zip [4, 4, 4, 3, 4]

-- scc_rt_stack_take, listing lines 452–456, at .Lscc_rt_stack_take.clsdone7 + 33
block_spec scc_rt_stack_take_9 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -72(%rbp)
movq -72(%rbp), %rax
movq -24(%rbp), %rcx
addq %rcx, %rax
movq %rax, -80(%rbp)")).zip [4, 4, 4, 3, 4]

-- scc_rt_stack_take, listing lines 458–459, at .Lscc_rt_stack_take.clsdone7 + 59
block_spec scc_rt_stack_take_10 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -88(%rbp)
jmp .Lscc_rt_stack_take.spin14")).zip [4, 2]

-- scc_rt_stack_take, listing lines 461–462, at .Lscc_rt_stack_take.spin14 + 0
block_spec scc_rt_stack_take_11 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq -88(%rbp), %rcx
movq $1, %rax")).zip [4, 7]

-- scc_rt_stack_take, listing lines 464–468, at .Lscc_rt_stack_take.spin14 + 14
block_spec scc_rt_stack_take_12 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_stack_take.locked15")).zip [4, 4, 7, 3, 2]

-- scc_rt_stack_take, listing lines 469–469, at .Lscc_rt_stack_take.spin14 + 34
block_spec scc_rt_stack_take_13 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_stack_take.spin14")).zip [2]

-- scc_rt_stack_take, listing lines 471–471, at .Lscc_rt_stack_take.locked15 + 0
block_spec scc_rt_stack_take_14 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rcx")).zip [4]

-- scc_rt_stack_take, listing lines 473–477, at .Lscc_rt_stack_take.locked15 + 7
block_spec scc_rt_stack_take_15 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_stack_take.bump")).zip [4, 4, 7, 3, 2]

-- scc_rt_stack_take, listing lines 478–478, at .Lscc_rt_stack_take.locked15 + 27
block_spec scc_rt_stack_take_16 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_stack_take.pop")).zip [2]

-- scc_rt_stack_take, listing lines 480–485, at .Lscc_rt_stack_take.pop + 0
block_spec scc_rt_stack_take_17 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq -104(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movq %rax, -112(%rbp)
movq -64(%rbp), %rcx
movq -112(%rbp), %rax")).zip [4, 7, 3, 4, 4, 4]

-- scc_rt_stack_take, listing lines 487–488, at .Lscc_rt_stack_take.pop + 29
block_spec scc_rt_stack_take_18 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq -112(%rbp), %rax
movq $3, %rcx")).zip [4, 7]

-- scc_rt_stack_take, listing lines 490–495, at .Lscc_rt_stack_take.pop + 43
block_spec scc_rt_stack_take_19 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -120(%rbp)
movq -80(%rbp), %rax
movq -120(%rbp), %rcx
addq %rcx, %rax
movq %rax, -128(%rbp)
movq -128(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4]

-- scc_rt_stack_take, listing lines 497–497, at .Lscc_rt_stack_take.pop + 69
block_spec scc_rt_stack_take_20 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -136(%rbp)")).zip [7]

-- scc_rt_stack_take, listing lines 499–501, at .Lscc_rt_stack_take.pop + 83
block_spec scc_rt_stack_take_21 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -144(%rbp)
movq -144(%rbp), %rcx
movq $0, %rax")).zip [7, 7, 7]

-- scc_rt_stack_take, listing lines 503–503, at .Lscc_rt_stack_take.pop + 107
block_spec scc_rt_stack_take_22 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_stack_take.taken")).zip [5]

-- scc_rt_stack_take, listing lines 506–508, at .Lscc_rt_stack_take.bump + 7
block_spec scc_rt_stack_take_23 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -152(%rbp)
movq -152(%rbp), %rcx
movq $0, %rax")).zip [7, 7, 7]

-- scc_rt_stack_take, listing lines 511–513, at .Lscc_rt_stack_take.bump + 38
block_spec scc_rt_stack_take_24 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -160(%rbp)
movq -160(%rbp), %rcx
movq -8(%rbp), %rax")).zip [7, 7, 4]

-- scc_rt_stack_take, listing lines 515–523, at .Lscc_rt_stack_take.bump + 61
block_spec scc_rt_stack_take_25 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -168(%rbp)
movq -168(%rbp), %rax
movq -8(%rbp), %rcx
addq %rcx, %rax
movq %rax, -176(%rbp)
movq -176(%rbp), %rax
movq $536870912, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_stack_take.full")).zip [7, 7, 4, 3, 7, 7, 7, 3, 2]

-- scc_rt_stack_take, listing lines 524–524, at .Lscc_rt_stack_take.bump + 108
block_spec scc_rt_stack_take_26 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_stack_take.ok")).zip [2]

-- scc_rt_stack_take, listing lines 526–527, at .Lscc_rt_stack_take.full + 0
block_spec scc_rt_stack_take_27 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq $3, %rdi
call scc_rt_abort")).zip [7, 5]

-- scc_rt_stack_take, listing lines 532–537, at .Lscc_rt_stack_take.ok + 7
block_spec scc_rt_stack_take_28 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq %rax, -184(%rbp)
movq -184(%rbp), %rax
movq -168(%rbp), %rcx
addq %rcx, %rax
movq %rax, -136(%rbp)
jmp .Lscc_rt_stack_take.taken")).zip [7, 7, 7, 3, 7, 2]

-- scc_rt_stack_take, listing lines 539–540, at .Lscc_rt_stack_take.taken + 0
block_spec scc_rt_stack_take_29 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("movq -136(%rbp), %rdi
movq -8(%rbp), %rsi")).zip [7, 4]

-- scc_rt_stack_take, listing lines 542–546, at scc_rt_take_site + 0
block_spec scc_rt_stack_take_30 (-200) 16 ⟨-192, [(.rbp, 0)]⟩ (parse("nop
movq -136(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [1, 7, 3, 1, 1]

-- scc_rt_stack_release, listing lines 552–556, at scc_rt_stack_release + 0
block_spec scc_rt_stack_release_0 (-144) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $144, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)")).zip [1, 3, 7, 4, 4]

-- scc_rt_stack_release, listing lines 558–559, at .Lscc_rt_stack_release.entry + 0
block_spec scc_rt_stack_release_1 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rdi
movq -16(%rbp), %rsi")).zip [4, 4]

-- scc_rt_stack_release, listing lines 561–570, at scc_rt_release_site + 0
block_spec scc_rt_stack_release_2 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("nop
movq $16384, %rax
movq %rax, -24(%rbp)
movq $0, %rax
movq %rax, -32(%rbp)
movq $32768, %rax
movq %rax, -40(%rbp)
movq $0, %rax
movq %rax, -48(%rbp)
jmp .Lscc_rt_stack_release.cls4")).zip [1, 7, 4, 7, 4, 7, 4, 7, 4, 2]

-- scc_rt_stack_release, listing lines 572–575, at .Lscc_rt_stack_release.cls4 + 0
block_spec scc_rt_stack_release_3 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq -24(%rbp), %rax
movq -16(%rbp), %rcx
cmpq %rcx, %rax
jb .Lscc_rt_stack_release.clsnext5")).zip [4, 4, 3, 2]

-- scc_rt_stack_release, listing lines 576–576, at .Lscc_rt_stack_release.cls4 + 13
block_spec scc_rt_stack_release_4 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_stack_release.clsdone6")).zip [2]

-- scc_rt_stack_release, listing lines 578–579, at .Lscc_rt_stack_release.clsnext5 + 0
block_spec scc_rt_stack_release_5 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq -40(%rbp), %rax
movq $3, %rcx")).zip [4, 7]

-- scc_rt_stack_release, listing lines 581–587, at .Lscc_rt_stack_release.clsnext5 + 14
block_spec scc_rt_stack_release_6 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -56(%rbp)
movq -32(%rbp), %rax
movq -56(%rbp), %rcx
addq %rcx, %rax
movq %rax, -32(%rbp)
movq -40(%rbp), %rax
movq $1, %rcx")).zip [4, 4, 4, 3, 4, 4, 7]

-- scc_rt_stack_release, listing lines 589–591, at .Lscc_rt_stack_release.clsnext5 + 47
block_spec scc_rt_stack_release_7 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -40(%rbp)
movq -24(%rbp), %rax
movq $1, %rcx")).zip [4, 4, 7]

-- scc_rt_stack_release, listing lines 593–598, at .Lscc_rt_stack_release.clsnext5 + 65
block_spec scc_rt_stack_release_8 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)
movq -48(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -48(%rbp)
jmp .Lscc_rt_stack_release.cls4")).zip [4, 4, 7, 3, 4, 2]

-- scc_rt_stack_release, listing lines 601–605, at .Lscc_rt_stack_release.clsdone6 + 7
block_spec scc_rt_stack_release_9 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -64(%rbp)
movq -64(%rbp), %rax
movq -48(%rbp), %rcx
addq %rcx, %rax
movq %rax, -72(%rbp)")).zip [4, 4, 4, 3, 4]

-- scc_rt_stack_release, listing lines 607–611, at .Lscc_rt_stack_release.clsdone6 + 33
block_spec scc_rt_stack_release_10 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -80(%rbp)
movq -80(%rbp), %rax
movq -32(%rbp), %rcx
addq %rcx, %rax
movq %rax, -88(%rbp)")).zip [4, 4, 4, 3, 4]

-- scc_rt_stack_release, listing lines 613–614, at .Lscc_rt_stack_release.clsdone6 + 59
block_spec scc_rt_stack_release_11 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -96(%rbp)
jmp .Lscc_rt_stack_release.spin13")).zip [4, 2]

-- scc_rt_stack_release, listing lines 616–617, at .Lscc_rt_stack_release.spin13 + 0
block_spec scc_rt_stack_release_12 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq -96(%rbp), %rcx
movq $1, %rax")).zip [4, 7]

-- scc_rt_stack_release, listing lines 619–623, at .Lscc_rt_stack_release.spin13 + 14
block_spec scc_rt_stack_release_13 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_stack_release.locked14")).zip [4, 4, 7, 3, 2]

-- scc_rt_stack_release, listing lines 624–624, at .Lscc_rt_stack_release.spin13 + 34
block_spec scc_rt_stack_release_14 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_stack_release.spin13")).zip [2]

-- scc_rt_stack_release, listing lines 626–626, at .Lscc_rt_stack_release.locked14 + 0
block_spec scc_rt_stack_release_15 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq -72(%rbp), %rcx")).zip [4]

-- scc_rt_stack_release, listing lines 628–630, at .Lscc_rt_stack_release.locked14 + 7
block_spec scc_rt_stack_release_16 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -112(%rbp)
movq -112(%rbp), %rax
movq $3, %rcx")).zip [4, 4, 7]

-- scc_rt_stack_release, listing lines 632–638, at .Lscc_rt_stack_release.locked14 + 25
block_spec scc_rt_stack_release_17 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -120(%rbp)
movq -88(%rbp), %rax
movq -120(%rbp), %rcx
addq %rcx, %rax
movq %rax, -128(%rbp)
movq -128(%rbp), %rcx
movq -8(%rbp), %rax")).zip [4, 4, 4, 3, 4, 4, 4]

-- scc_rt_stack_release, listing lines 640–645, at .Lscc_rt_stack_release.locked14 + 55
block_spec scc_rt_stack_release_18 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq -112(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -136(%rbp)
movq -72(%rbp), %rcx
movq -136(%rbp), %rax")).zip [4, 7, 3, 7, 4, 7]

-- scc_rt_stack_release, listing lines 648–650, at .Lscc_rt_stack_release.locked14 + 97
block_spec scc_rt_stack_release_19 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rax, -144(%rbp)
movq -144(%rbp), %rcx
movq $0, %rax")).zip [7, 7, 7]

-- scc_rt_stack_release, listing lines 652–654, at .Lscc_rt_stack_release.locked14 + 121
block_spec scc_rt_stack_release_20 (-144) 16 ⟨-144, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

-- scc_rt_grow, listing lines 660–664, at scc_rt_grow + 0
block_spec scc_rt_grow_0 (-360) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $352, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)")).zip [1, 3, 7, 4, 4]

-- scc_rt_grow, listing lines 667–668, at .Lscc_rt_grow.entry + 9
block_spec scc_rt_grow_1 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rcx")).zip [4, 4]

-- scc_rt_grow, listing lines 670–671, at .Lscc_rt_grow.entry + 21
block_spec scc_rt_grow_2 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -32(%rbp)
movq -24(%rbp), %rcx")).zip [4, 4]

-- scc_rt_grow, listing lines 673–691, at .Lscc_rt_grow.entry + 33
block_spec scc_rt_grow_3 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -40(%rbp)
movq -40(%rbp), %rax
movq -32(%rbp), %rcx
subq %rcx, %rax
movq %rax, -48(%rbp)
movq -40(%rbp), %rax
movq -8(%rbp), %rcx
subq %rcx, %rax
movq %rax, -56(%rbp)
movq -56(%rbp), %rax
movq -16(%rbp), %rcx
addq %rcx, %rax
movq %rax, -64(%rbp)
movq -64(%rbp), %rax
movq $4352, %rcx
addq %rcx, %rax
movq %rax, -72(%rbp)
movq -48(%rbp), %rax
movq $1, %rcx")).zip [4, 4, 4, 3, 4, 4, 4, 3, 4, 4, 4, 3, 4, 4, 7, 3, 4, 4, 7]

-- scc_rt_grow, listing lines 693–694, at .Lscc_rt_grow.entry + 114
block_spec scc_rt_grow_4 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -80(%rbp)
jmp .Lscc_rt_grow.dbl")).zip [4, 2]

-- scc_rt_grow, listing lines 696–699, at .Lscc_rt_grow.dbl + 0
block_spec scc_rt_grow_5 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -80(%rbp), %rax
movq -72(%rbp), %rcx
cmpq %rcx, %rax
jb .Lscc_rt_grow.dbl2")).zip [4, 4, 3, 2]

-- scc_rt_grow, listing lines 700–700, at .Lscc_rt_grow.dbl + 13
block_spec scc_rt_grow_6 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.cap")).zip [2]

-- scc_rt_grow, listing lines 702–703, at .Lscc_rt_grow.dbl2 + 0
block_spec scc_rt_grow_7 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -80(%rbp), %rax
movq $1, %rcx")).zip [4, 7]

-- scc_rt_grow, listing lines 705–706, at .Lscc_rt_grow.dbl2 + 14
block_spec scc_rt_grow_8 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -80(%rbp)
jmp .Lscc_rt_grow.dbl")).zip [4, 2]

-- scc_rt_grow, listing lines 708–711, at .Lscc_rt_grow.cap + 0
block_spec scc_rt_grow_9 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -80(%rbp), %rax
movq $67108864, %rcx
cmpq %rcx, %rax
ja .Lscc_rt_grow.full")).zip [4, 7, 3, 2]

-- scc_rt_grow, listing lines 712–712, at .Lscc_rt_grow.cap + 16
block_spec scc_rt_grow_10 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.take")).zip [2]

-- scc_rt_grow, listing lines 714–715, at .Lscc_rt_grow.full + 0
block_spec scc_rt_grow_11 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq $3, %rdi
call scc_rt_abort")).zip [7, 5]

-- scc_rt_grow, listing lines 719–720, at .Lscc_rt_grow.take + 0
block_spec scc_rt_grow_12 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -80(%rbp), %rdi
call scc_rt_stack_take")).zip [4, 5]

-- scc_rt_grow, listing lines 722–733, at .Lscc_rt_grow.x11 + 0
block_spec scc_rt_grow_13 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -88(%rbp)
movq -88(%rbp), %rax
movq -80(%rbp), %rcx
addq %rcx, %rax
movq %rax, -96(%rbp)
movq -96(%rbp), %rax
movq -40(%rbp), %rcx
subq %rcx, %rax
movq %rax, -104(%rbp)
movq -8(%rbp), %rax
movq %rax, -112(%rbp)
jmp .Lscc_rt_grow.copy")).zip [4, 4, 4, 3, 4, 4, 4, 3, 4, 4, 4, 2]

-- scc_rt_grow, listing lines 735–738, at .Lscc_rt_grow.copy + 0
block_spec scc_rt_grow_14 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -112(%rbp), %rax
movq -40(%rbp), %rcx
cmpq %rcx, %rax
jae .Lscc_rt_grow.walk0")).zip [4, 4, 3, 2]

-- scc_rt_grow, listing lines 739–739, at .Lscc_rt_grow.copy + 13
block_spec scc_rt_grow_15 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.copy1")).zip [2]

-- scc_rt_grow, listing lines 741–741, at .Lscc_rt_grow.copy1 + 0
block_spec scc_rt_grow_16 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -112(%rbp), %rcx")).zip [4]

-- scc_rt_grow, listing lines 743–749, at .Lscc_rt_grow.copy1 + 7
block_spec scc_rt_grow_17 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -120(%rbp)
movq -112(%rbp), %rax
movq -104(%rbp), %rcx
addq %rcx, %rax
movq %rax, -128(%rbp)
movq -128(%rbp), %rcx
movq -120(%rbp), %rax")).zip [4, 4, 4, 3, 4, 4, 4]

-- scc_rt_grow, listing lines 751–755, at .Lscc_rt_grow.copy1 + 37
block_spec scc_rt_grow_18 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -112(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -112(%rbp)
jmp .Lscc_rt_grow.copy")).zip [4, 7, 3, 4, 2]

-- scc_rt_grow, listing lines 757–758, at .Lscc_rt_grow.walk0 + 0
block_spec scc_rt_grow_19 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq %rax, -136(%rbp)")).zip [4, 7]

-- scc_rt_grow, listing lines 760–761, at .Lscc_rt_grow.walk0 + 18
block_spec scc_rt_grow_20 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -144(%rbp)
movq -144(%rbp), %rcx")).zip [7, 7]

-- scc_rt_grow, listing lines 763–765, at .Lscc_rt_grow.walk0 + 35
block_spec scc_rt_grow_21 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -152(%rbp)
movq -152(%rbp), %rax
movq $32, %rcx")).zip [7, 7, 7]

-- scc_rt_grow, listing lines 767–776, at .Lscc_rt_grow.walk0 + 60
block_spec scc_rt_grow_22 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -160(%rbp)
movq -160(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -168(%rbp)
movq -144(%rbp), %rax
movq -168(%rbp), %rcx
addq %rcx, %rax
movq %rax, -176(%rbp)
jmp .Lscc_rt_grow.walk")).zip [7, 7, 7, 3, 7, 7, 7, 3, 7, 2]

-- scc_rt_grow, listing lines 778–778, at .Lscc_rt_grow.walk + 0
block_spec scc_rt_grow_23 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -136(%rbp), %rcx")).zip [7]

-- scc_rt_grow, listing lines 780–784, at .Lscc_rt_grow.walk + 10
block_spec scc_rt_grow_24 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -184(%rbp)
movq -184(%rbp), %rax
movq -32(%rbp), %rcx
cmpq %rcx, %rax
jb .Lscc_rt_grow.done")).zip [7, 7, 4, 3, 6]

-- scc_rt_grow, listing lines 785–785, at .Lscc_rt_grow.walk + 37
block_spec scc_rt_grow_25 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.walk1")).zip [2]

-- scc_rt_grow, listing lines 787–790, at .Lscc_rt_grow.walk1 + 0
block_spec scc_rt_grow_26 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -184(%rbp), %rax
movq -40(%rbp), %rcx
cmpq %rcx, %rax
jae .Lscc_rt_grow.done")).zip [7, 4, 3, 6]

-- scc_rt_grow, listing lines 791–791, at .Lscc_rt_grow.walk1 + 20
block_spec scc_rt_grow_27 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.walk2")).zip [2]

-- scc_rt_grow, listing lines 793–802, at .Lscc_rt_grow.walk2 + 0
block_spec scc_rt_grow_28 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -136(%rbp), %rax
movq -104(%rbp), %rcx
addq %rcx, %rax
movq %rax, -192(%rbp)
movq -184(%rbp), %rax
movq -104(%rbp), %rcx
addq %rcx, %rax
movq %rax, -200(%rbp)
movq -192(%rbp), %rcx
movq -200(%rbp), %rax")).zip [7, 4, 3, 7, 7, 4, 3, 7, 7, 7]

-- scc_rt_grow, listing lines 804–804, at .Lscc_rt_grow.walk2 + 59
block_spec scc_rt_grow_29 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -136(%rbp), %rcx")).zip [7]

-- scc_rt_grow, listing lines 806–811, at .Lscc_rt_grow.walk2 + 70
block_spec scc_rt_grow_30 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -208(%rbp)
movq $0, %rax
movq %rax, -216(%rbp)
movq -152(%rbp), %rax
movq %rax, -224(%rbp)
jmp .Lscc_rt_grow.bs")).zip [7, 7, 7, 7, 7, 2]

-- scc_rt_grow, listing lines 813–816, at .Lscc_rt_grow.bs + 0
block_spec scc_rt_grow_31 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -216(%rbp), %rax
movq -224(%rbp), %rcx
cmpq %rcx, %rax
jae .Lscc_rt_grow.next")).zip [7, 7, 3, 6]

-- scc_rt_grow, listing lines 817–817, at .Lscc_rt_grow.bs + 23
block_spec scc_rt_grow_32 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.bs1")).zip [2]

-- scc_rt_grow, listing lines 819–824, at .Lscc_rt_grow.bs1 + 0
block_spec scc_rt_grow_33 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -216(%rbp), %rax
movq -224(%rbp), %rcx
addq %rcx, %rax
movq %rax, -232(%rbp)
movq -232(%rbp), %rax
movq $1, %rcx")).zip [7, 7, 3, 7, 7, 7]

-- scc_rt_grow, listing lines 826–828, at .Lscc_rt_grow.bs1 + 41
block_spec scc_rt_grow_34 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -240(%rbp)
movq -240(%rbp), %rax
movq $32, %rcx")).zip [7, 7, 7]

-- scc_rt_grow, listing lines 830–839, at .Lscc_rt_grow.bs1 + 66
block_spec scc_rt_grow_35 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -248(%rbp)
movq -144(%rbp), %rax
movq -248(%rbp), %rcx
addq %rcx, %rax
movq %rax, -256(%rbp)
movq -256(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -256(%rbp)
movq -256(%rbp), %rcx")).zip [7, 7, 7, 3, 7, 7, 7, 3, 7, 7]

-- scc_rt_grow, listing lines 841–845, at .Lscc_rt_grow.bs1 + 131
block_spec scc_rt_grow_36 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -264(%rbp)
movq -264(%rbp), %rax
movq -208(%rbp), %rcx
cmpq %rcx, %rax
je .Lscc_rt_grow.found")).zip [7, 7, 7, 3, 2]

-- scc_rt_grow, listing lines 846–846, at .Lscc_rt_grow.bs1 + 157
block_spec scc_rt_grow_37 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.bs2")).zip [2]

-- scc_rt_grow, listing lines 848–851, at .Lscc_rt_grow.bs2 + 0
block_spec scc_rt_grow_38 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -264(%rbp), %rax
movq -208(%rbp), %rcx
cmpq %rcx, %rax
jb .Lscc_rt_grow.bslo")).zip [7, 7, 3, 2]

-- scc_rt_grow, listing lines 852–852, at .Lscc_rt_grow.bs2 + 19
block_spec scc_rt_grow_39 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.bshi")).zip [2]

-- scc_rt_grow, listing lines 854–858, at .Lscc_rt_grow.bslo + 0
block_spec scc_rt_grow_40 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -240(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -216(%rbp)
jmp .Lscc_rt_grow.bs")).zip [7, 7, 3, 7, 5]

-- scc_rt_grow, listing lines 860–862, at .Lscc_rt_grow.bshi + 0
block_spec scc_rt_grow_41 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -240(%rbp), %rax
movq %rax, -224(%rbp)
jmp .Lscc_rt_grow.bs")).zip [7, 7, 5]

-- scc_rt_grow, listing lines 864–864, at .Lscc_rt_grow.found + 0
block_spec scc_rt_grow_42 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -256(%rbp), %rcx")).zip [7]

-- scc_rt_grow, listing lines 866–867, at .Lscc_rt_grow.found + 11
block_spec scc_rt_grow_43 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -272(%rbp)
movq -256(%rbp), %rcx")).zip [7, 7]

-- scc_rt_grow, listing lines 869–871, at .Lscc_rt_grow.found + 29
block_spec scc_rt_grow_44 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -280(%rbp)
movq -280(%rbp), %rax
movq $3, %rcx")).zip [7, 7, 7]

-- scc_rt_grow, listing lines 873–880, at .Lscc_rt_grow.found + 53
block_spec scc_rt_grow_45 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -288(%rbp)
movq -288(%rbp), %rax
movq -176(%rbp), %rcx
addq %rcx, %rax
movq %rax, -288(%rbp)
movq $0, %rax
movq %rax, -296(%rbp)
jmp .Lscc_rt_grow.fix")).zip [7, 7, 7, 3, 7, 7, 7, 2]

-- scc_rt_grow, listing lines 882–885, at .Lscc_rt_grow.fix + 0
block_spec scc_rt_grow_46 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -296(%rbp), %rax
movq -272(%rbp), %rcx
cmpq %rcx, %rax
jae .Lscc_rt_grow.next")).zip [7, 7, 3, 6]

-- scc_rt_grow, listing lines 886–886, at .Lscc_rt_grow.fix + 23
block_spec scc_rt_grow_47 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.fix1")).zip [2]

-- scc_rt_grow, listing lines 888–888, at .Lscc_rt_grow.fix1 + 0
block_spec scc_rt_grow_48 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -288(%rbp), %rcx")).zip [7]

-- scc_rt_grow, listing lines 890–895, at .Lscc_rt_grow.fix1 + 10
block_spec scc_rt_grow_49 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -304(%rbp)
movq -184(%rbp), %rax
movq -304(%rbp), %rcx
addq %rcx, %rax
movq %rax, -312(%rbp)
movq -312(%rbp), %rcx")).zip [7, 7, 7, 3, 7, 7]

-- scc_rt_grow, listing lines 897–901, at .Lscc_rt_grow.fix1 + 51
block_spec scc_rt_grow_50 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq %rax, -320(%rbp)
movq -320(%rbp), %rax
movq -32(%rbp), %rcx
cmpq %rcx, %rax
jb .Lscc_rt_grow.skip")).zip [7, 7, 4, 3, 2]

-- scc_rt_grow, listing lines 902–902, at .Lscc_rt_grow.fix1 + 74
block_spec scc_rt_grow_51 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.fix2")).zip [2]

-- scc_rt_grow, listing lines 904–907, at .Lscc_rt_grow.fix2 + 0
block_spec scc_rt_grow_52 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -320(%rbp), %rax
movq -40(%rbp), %rcx
cmpq %rcx, %rax
jae .Lscc_rt_grow.skip")).zip [7, 4, 3, 2]

-- scc_rt_grow, listing lines 908–908, at .Lscc_rt_grow.fix2 + 16
block_spec scc_rt_grow_53 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.fix3")).zip [2]

-- scc_rt_grow, listing lines 910–919, at .Lscc_rt_grow.fix3 + 0
block_spec scc_rt_grow_54 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -312(%rbp), %rax
movq -104(%rbp), %rcx
addq %rcx, %rax
movq %rax, -328(%rbp)
movq -320(%rbp), %rax
movq -104(%rbp), %rcx
addq %rcx, %rax
movq %rax, -336(%rbp)
movq -328(%rbp), %rcx
movq -336(%rbp), %rax")).zip [7, 4, 3, 7, 7, 4, 3, 7, 7, 7]

-- scc_rt_grow, listing lines 921–921, at .Lscc_rt_grow.fix3 + 59
block_spec scc_rt_grow_55 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_grow.skip")).zip [2]

-- scc_rt_grow, listing lines 923–931, at .Lscc_rt_grow.skip + 0
block_spec scc_rt_grow_56 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -296(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
movq %rax, -296(%rbp)
movq -288(%rbp), %rax
movq $8, %rcx
addq %rcx, %rax
movq %rax, -288(%rbp)
jmp .Lscc_rt_grow.fix")).zip [7, 7, 3, 7, 7, 7, 3, 7, 5]

-- scc_rt_grow, listing lines 933–935, at .Lscc_rt_grow.next + 0
block_spec scc_rt_grow_57 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -184(%rbp), %rax
movq %rax, -136(%rbp)
jmp .Lscc_rt_grow.walk")).zip [7, 7, 5]

-- scc_rt_grow, listing lines 937–938, at .Lscc_rt_grow.done + 0
block_spec scc_rt_grow_58 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -24(%rbp), %rcx
movq -88(%rbp), %rax")).zip [4, 4]

-- scc_rt_grow, listing lines 940–941, at .Lscc_rt_grow.done + 12
block_spec scc_rt_grow_59 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -24(%rbp), %rcx
movq -96(%rbp), %rax")).zip [4, 4]

-- scc_rt_grow, listing lines 943–948, at .Lscc_rt_grow.done + 24
block_spec scc_rt_grow_60 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -88(%rbp), %rax
movq $4096, %rcx
addq %rcx, %rax
movq %rax, -344(%rbp)
movq -24(%rbp), %rcx
movq -344(%rbp), %rax")).zip [4, 7, 3, 7, 4, 7]

-- scc_rt_grow, listing lines 950–955, at .Lscc_rt_grow.done + 60
block_spec scc_rt_grow_61 (-360) 16 ⟨-352, [(.rbp, 0)]⟩ (parse("movq -104(%rbp), %rax
movq -32(%rbp), %rdx
movq -48(%rbp), %rcx
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 4, 4, 3, 1, 1]

-- scc_rt_print, listing lines 961–965, at scc_rt_print + 0
block_spec scc_rt_print_0 (-40) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)")).zip [1, 3, 4, 4, 4]

-- scc_rt_print, listing lines 967–967, at .Lscc_rt_print.entry + 0
block_spec scc_rt_print_1 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_print.loop")).zip [2]

-- scc_rt_print, listing lines 969–972, at .Lscc_rt_print.loop + 0
block_spec scc_rt_print_2 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -16(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_print.done")).zip [4, 7, 3, 6]

-- scc_rt_print, listing lines 973–973, at .Lscc_rt_print.loop + 20
block_spec scc_rt_print_3 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_print.write")).zip [2]

-- scc_rt_print, listing lines 975–978, at .Lscc_rt_print.write + 0
block_spec scc_rt_print_4 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq $1, %rdi
movq -8(%rbp), %rsi
movq -16(%rbp), %rdx
movl $1, %eax")).zip [7, 4, 4, 5]

-- scc_rt_print, listing lines 980–984, at .Lscc_rt_print.write + 22
block_spec scc_rt_print_5 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $-4, %rcx
cmpq %rcx, %rax
je .Lscc_rt_print.loop")).zip [4, 4, 7, 3, 2]

-- scc_rt_print, listing lines 985–985, at .Lscc_rt_print.write + 42
block_spec scc_rt_print_6 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_print.chk2")).zip [2]

-- scc_rt_print, listing lines 987–990, at .Lscc_rt_print.chk2 + 0
block_spec scc_rt_print_7 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -24(%rbp), %rax
movq $-11, %rcx
cmpq %rcx, %rax
je .Lscc_rt_print.loop")).zip [4, 7, 3, 2]

-- scc_rt_print, listing lines 991–991, at .Lscc_rt_print.chk2 + 16
block_spec scc_rt_print_8 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_print.chk3")).zip [2]

-- scc_rt_print, listing lines 993–996, at .Lscc_rt_print.chk3 + 0
block_spec scc_rt_print_9 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -24(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
jle .Lscc_rt_print.fail")).zip [4, 7, 3, 2]

-- scc_rt_print, listing lines 997–997, at .Lscc_rt_print.chk3 + 16
block_spec scc_rt_print_10 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_print.adv")).zip [2]

-- scc_rt_print, listing lines 999–1007, at .Lscc_rt_print.adv + 0
block_spec scc_rt_print_11 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq -24(%rbp), %rcx
addq %rcx, %rax
movq %rax, -8(%rbp)
movq -16(%rbp), %rax
movq -24(%rbp), %rcx
subq %rcx, %rax
movq %rax, -16(%rbp)
jmp .Lscc_rt_print.loop")).zip [4, 4, 3, 4, 4, 4, 3, 4, 5]

-- scc_rt_print, listing lines 1009–1010, at .Lscc_rt_print.fail + 0
block_spec scc_rt_print_12 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq $4, %rdi
call scc_rt_abort")).zip [7, 5]

-- scc_rt_print, listing lines 1014–1016, at .Lscc_rt_print.done + 0
block_spec scc_rt_print_13 (-40) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

-- scc_rt_park, listing lines 1022–1024, at scc_rt_park + 0
block_spec scc_rt_park_0 (-40) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $48, %rsp")).zip [1, 3, 4]

-- scc_rt_park, listing lines 1027–1029, at .Lscc_rt_park.entry + 9
block_spec scc_rt_park_1 (-40) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("movq %rax, -8(%rbp)
movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 4, 7]

-- scc_rt_park, listing lines 1031–1035, at .Lscc_rt_park.entry + 28
block_spec scc_rt_park_2 (-40) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lscc_rt_park.done")).zip [4, 4, 7, 3, 2]

-- scc_rt_park, listing lines 1036–1036, at .Lscc_rt_park.entry + 48
block_spec scc_rt_park_3 (-40) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_park.wait")).zip [2]

-- scc_rt_park, listing lines 1038–1048, at .Lscc_rt_park.wait + 0
block_spec scc_rt_park_4 (-40) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $16, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -24(%rbp), %rdi
movq $128, %rsi
movq $0, %rdx
movq $0, %r10
movq $0, %r8
movq $0, %r9
movl $202, %eax")).zip [4, 7, 3, 4, 4, 7, 7, 7, 7, 7, 5]

-- scc_rt_park, listing lines 1050–1052, at .Lscc_rt_park.wait + 64
block_spec scc_rt_park_5 (-40) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("movq %rax, -32(%rbp)
movq -8(%rbp), %rcx
movq $0, %rax")).zip [4, 4, 7]

-- scc_rt_park, listing lines 1054–1057, at .Lscc_rt_park.wait + 83
block_spec scc_rt_park_6 (-40) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("movq %rax, -40(%rbp)
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

-- scc_rt_park, listing lines 1059–1061, at .Lscc_rt_park.done + 0
block_spec scc_rt_park_7 (-40) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

-- scc_rt_unpark, listing lines 1067–1070, at scc_rt_unpark + 0
block_spec scc_rt_unpark_0 (-32) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 4, 4]

-- scc_rt_unpark, listing lines 1072–1073, at .Lscc_rt_unpark.entry + 0
block_spec scc_rt_unpark_1 (-32) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx
movq $1, %rax")).zip [4, 7]

-- scc_rt_unpark, listing lines 1075–1079, at .Lscc_rt_unpark.entry + 15
block_spec scc_rt_unpark_2 (-32) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_unpark.wake")).zip [4, 4, 7, 3, 2]

-- scc_rt_unpark, listing lines 1080–1080, at .Lscc_rt_unpark.entry + 35
block_spec scc_rt_unpark_3 (-32) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_unpark.done")).zip [2]

-- scc_rt_unpark, listing lines 1082–1092, at .Lscc_rt_unpark.wake + 0
block_spec scc_rt_unpark_4 (-32) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $16, %rcx
addq %rcx, %rax
movq %rax, -24(%rbp)
movq -24(%rbp), %rdi
movq $129, %rsi
movq $1, %rdx
movq $0, %r10
movq $0, %r8
movq $0, %r9
movl $202, %eax")).zip [4, 7, 3, 4, 4, 7, 7, 7, 7, 7, 5]

-- scc_rt_unpark, listing lines 1094–1097, at .Lscc_rt_unpark.wake + 64
block_spec scc_rt_unpark_5 (-32) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -32(%rbp)
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

-- scc_rt_unpark, listing lines 1099–1101, at .Lscc_rt_unpark.done + 0
block_spec scc_rt_unpark_6 (-32) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

-- scc_rt_abort, listing lines 1107–1110, at scc_rt_abort + 0
block_spec scc_rt_abort_0 (-8) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $16, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 4, 4]

-- scc_rt_abort, listing lines 1112–1115, at .Lscc_rt_abort.entry + 0
block_spec scc_rt_abort_1 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is0")).zip [4, 7, 3, 2]

-- scc_rt_abort, listing lines 1116–1116, at .Lscc_rt_abort.entry + 16
block_spec scc_rt_abort_2 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_abort.next1")).zip [2]

-- scc_rt_abort, listing lines 1118–1120, at .Lscc_rt_abort.is0 + 0
block_spec scc_rt_abort_3 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_overflow")).zip [3, 1, 2]

-- scc_rt_abort, listing lines 1122–1125, at .Lscc_rt_abort.next1 + 0
block_spec scc_rt_abort_4 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $2, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is2")).zip [4, 7, 3, 2]

-- scc_rt_abort, listing lines 1126–1126, at .Lscc_rt_abort.next1 + 16
block_spec scc_rt_abort_5 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_abort.next3")).zip [2]

-- scc_rt_abort, listing lines 1128–1130, at .Lscc_rt_abort.is2 + 0
block_spec scc_rt_abort_6 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_heap")).zip [3, 1, 5]

-- scc_rt_abort, listing lines 1132–1135, at .Lscc_rt_abort.next3 + 0
block_spec scc_rt_abort_7 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $3, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is4")).zip [4, 7, 3, 2]

-- scc_rt_abort, listing lines 1136–1136, at .Lscc_rt_abort.next3 + 16
block_spec scc_rt_abort_8 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_abort.next5")).zip [2]

-- scc_rt_abort, listing lines 1138–1140, at .Lscc_rt_abort.is4 + 0
block_spec scc_rt_abort_9 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_stack")).zip [3, 1, 5]

-- scc_rt_abort, listing lines 1142–1145, at .Lscc_rt_abort.next5 + 0
block_spec scc_rt_abort_10 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $4, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is6")).zip [4, 7, 3, 2]

-- scc_rt_abort, listing lines 1146–1146, at .Lscc_rt_abort.next5 + 16
block_spec scc_rt_abort_11 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_abort.next7")).zip [2]

-- scc_rt_abort, listing lines 1148–1150, at .Lscc_rt_abort.is6 + 0
block_spec scc_rt_abort_12 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_write")).zip [3, 1, 5]

-- scc_rt_abort, listing lines 1152–1155, at .Lscc_rt_abort.next7 + 0
block_spec scc_rt_abort_13 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $5, %rcx
cmpq %rcx, %rax
je .Lscc_rt_abort.is8")).zip [4, 7, 3, 2]

-- scc_rt_abort, listing lines 1156–1156, at .Lscc_rt_abort.next7 + 16
block_spec scc_rt_abort_14 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("jmp .Lscc_rt_abort.next9")).zip [2]

-- scc_rt_abort, listing lines 1158–1160, at .Lscc_rt_abort.is8 + 0
block_spec scc_rt_abort_15 (-8) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
jmp scc_rt_abort_threads")).zip [3, 1, 5]

-- scc_rt_abort_overflow, listing lines 1168–1170, at scc_rt_abort_overflow + 0
block_spec scc_rt_abort_overflow_0 (-24) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]

-- scc_rt_abort_overflow, listing lines 1173–1177, at .Lscc_rt_abort_overflow.entry + 7
block_spec scc_rt_abort_overflow_1 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $34, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

-- scc_rt_abort_overflow, listing lines 1179–1181, at .Lscc_rt_abort_overflow.entry + 36
block_spec scc_rt_abort_overflow_2 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq $101, %rdi
movl $231, %eax")).zip [4, 7, 5]

-- scc_rt_abort_overflow, listing lines 1184–1184, at scc_rt_abort_overflow_exit + 2
block_spec scc_rt_abort_overflow_3 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)")).zip [4]

-- scc_rt_abort_heap, listing lines 1191–1193, at scc_rt_abort_heap + 0
block_spec scc_rt_abort_heap_0 (-24) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]

-- scc_rt_abort_heap, listing lines 1196–1200, at .Lscc_rt_abort_heap.entry + 7
block_spec scc_rt_abort_heap_1 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $35, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

-- scc_rt_abort_heap, listing lines 1202–1204, at .Lscc_rt_abort_heap.entry + 36
block_spec scc_rt_abort_heap_2 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq $101, %rdi
movl $231, %eax")).zip [4, 7, 5]

-- scc_rt_abort_heap, listing lines 1207–1207, at scc_rt_abort_heap_exit + 2
block_spec scc_rt_abort_heap_3 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)")).zip [4]

-- scc_rt_abort_stack, listing lines 1214–1216, at scc_rt_abort_stack + 0
block_spec scc_rt_abort_stack_0 (-24) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]

-- scc_rt_abort_stack, listing lines 1219–1223, at .Lscc_rt_abort_stack.entry + 7
block_spec scc_rt_abort_stack_1 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $25, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

-- scc_rt_abort_stack, listing lines 1225–1227, at .Lscc_rt_abort_stack.entry + 36
block_spec scc_rt_abort_stack_2 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq $101, %rdi
movl $231, %eax")).zip [4, 7, 5]

-- scc_rt_abort_stack, listing lines 1230–1230, at scc_rt_abort_stack_exit + 2
block_spec scc_rt_abort_stack_3 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)")).zip [4]

-- scc_rt_abort_write, listing lines 1237–1239, at scc_rt_abort_write + 0
block_spec scc_rt_abort_write_0 (-24) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]

-- scc_rt_abort_write, listing lines 1242–1246, at .Lscc_rt_abort_write.entry + 7
block_spec scc_rt_abort_write_1 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $44, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

-- scc_rt_abort_write, listing lines 1248–1250, at .Lscc_rt_abort_write.entry + 36
block_spec scc_rt_abort_write_2 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq $101, %rdi
movl $231, %eax")).zip [4, 7, 5]

-- scc_rt_abort_write, listing lines 1253–1253, at scc_rt_abort_write_exit + 2
block_spec scc_rt_abort_write_3 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)")).zip [4]

-- scc_rt_abort_threads, listing lines 1260–1262, at scc_rt_abort_threads + 0
block_spec scc_rt_abort_threads_0 (-24) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]

-- scc_rt_abort_threads, listing lines 1265–1269, at .Lscc_rt_abort_threads.entry + 7
block_spec scc_rt_abort_threads_1 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -8(%rbp)
movq $2, %rdi
movq -8(%rbp), %rsi
movq $35, %rdx
movl $1, %eax")).zip [4, 7, 4, 7, 5]

-- scc_rt_abort_threads, listing lines 1271–1273, at .Lscc_rt_abort_threads.entry + 36
block_spec scc_rt_abort_threads_2 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq $101, %rdi
movl $231, %eax")).zip [4, 7, 5]

-- scc_rt_abort_threads, listing lines 1276–1276, at scc_rt_abort_threads_exit + 2
block_spec scc_rt_abort_threads_3 (-24) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)")).zip [4]

-- scc_rt_thr_worker, listing lines 1283–1284, at scc_rt_thr_worker + 0
block_spec scc_rt_thr_worker_0 (-72) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]

-- scc_rt_thr_worker, listing lines 1286–1286, at .Lscc_rt_thr_worker.chk + 0
block_spec scc_rt_thr_worker_1 (-72) 16 ⟨0, [(.rbp, 0)]⟩ (parse("leaq -64(%rsp), %rax")).zip [5]

-- scc_rt_thr_worker, listing lines 1288–1289, at .Lscc_rt_thr_worker.chk + 14
block_spec scc_rt_thr_worker_2 (-72) 16 ⟨0, [(.rax, -64), (.rbp, 0)]⟩ (parse("cmpq %r11, %rax
jb .Lscc_rt_thr_worker.stk")).zip [3, 6]

-- scc_rt_thr_worker, listing lines 1290–1291, at .Lscc_rt_thr_worker.chk + 23
block_spec scc_rt_thr_worker_3 (-72) 16 ⟨0, [(.rax, -64), (.rbp, 0)]⟩ (parse("subq $64, %rsp
movq %rdi, -8(%rbp)")).zip [4, 4]

-- scc_rt_thr_worker, listing lines 1293–1293, at .Lscc_rt_thr_worker.entry + 0
block_spec scc_rt_thr_worker_4 (-72) 16 ⟨-64, [(.rax, -64), (.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx")).zip [4]

-- scc_rt_thr_worker, listing lines 1295–1296, at .Lscc_rt_thr_worker.entry + 8
block_spec scc_rt_thr_worker_5 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq -8(%rbp), %rcx")).zip [4, 4]

-- scc_rt_thr_worker, listing lines 1298–1299, at .Lscc_rt_thr_worker.entry + 20
block_spec scc_rt_thr_worker_6 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)
movq -8(%rbp), %rcx")).zip [4, 4]

-- scc_rt_thr_worker, listing lines 1301–1302, at .Lscc_rt_thr_worker.entry + 32
block_spec scc_rt_thr_worker_7 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -32(%rbp)
movq -8(%rbp), %rcx")).zip [4, 4]

-- scc_rt_thr_worker, listing lines 1304–1305, at .Lscc_rt_thr_worker.entry + 44
block_spec scc_rt_thr_worker_8 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -40(%rbp)
movq -8(%rbp), %rcx")).zip [4, 4]

-- scc_rt_thr_worker, listing lines 1307–1308, at .Lscc_rt_thr_worker.entry + 56
block_spec scc_rt_thr_worker_9 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -48(%rbp)
movq -8(%rbp), %rcx")).zip [4, 4]

-- scc_rt_thr_worker, listing lines 1310–1317, at .Lscc_rt_thr_worker.entry + 68
block_spec scc_rt_thr_worker_10 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -56(%rbp)
movq -16(%rbp), %rdi
movq -24(%rbp), %rsi
movq -32(%rbp), %rdx
movq -40(%rbp), %rcx
movq -48(%rbp), %r8
movq -56(%rbp), %r9
call wc_worker")).zip [4, 4, 4, 4, 4, 4, 4, 5]

-- scc_rt_thr_worker, listing lines 1319–1320, at .Lscc_rt_thr_worker.x13 + 0
block_spec scc_rt_thr_worker_11 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx
movq $1, %rax")).zip [4, 7]

-- scc_rt_thr_worker, listing lines 1322–1323, at .Lscc_rt_thr_worker.x13 + 15
block_spec scc_rt_thr_worker_12 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq $0, %rdi
movl $60, %eax")).zip [7, 5]

-- scc_rt_thr_worker, listing lines 1325–1325, at .Lscc_rt_thr_worker.x13 + 29
block_spec scc_rt_thr_worker_13 (-72) 16 ⟨-64, [(.rbp, 0)]⟩ (parse("movq %rax, -64(%rbp)")).zip [4]

-- scc_rt_thr_worker, listing lines 1328–1335, at .Lscc_rt_thr_worker.stk + 0
block_spec scc_rt_thr_worker_14 (-72) 16 ⟨0, [(.rax, -64), (.rbp, 0)]⟩ (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $64, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]

-- scc_rt_thr_worker, listing lines 1337–1343, at .Lscc_rt_thr_worker.x14 + 0
block_spec scc_rt_thr_worker_15 (-72) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lscc_rt_thr_worker.chk")).zip [2, 2, 1, 1, 1, 1, 5]

-- wc_spin, listing lines 1349–1350, at wc_spin + 0
block_spec wc_spin_0 (-56) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]

-- wc_spin, listing lines 1352–1352, at .Lwc_spin.chk + 0
block_spec wc_spin_1 (-56) 16 ⟨0, [(.rbp, 0)]⟩ (parse("leaq -16(%rsp), %rax")).zip [5]

-- wc_spin, listing lines 1354–1355, at .Lwc_spin.chk + 14
block_spec wc_spin_2 (-56) 16 ⟨0, [(.rax, -16), (.rbp, 0)]⟩ (parse("cmpq %r11, %rax
jb .Lwc_spin.stk")).zip [3, 2]

-- wc_spin, listing lines 1356–1357, at .Lwc_spin.chk + 19
block_spec wc_spin_3 (-56) 16 ⟨0, [(.rax, -16), (.rbp, 0)]⟩ (parse("subq $16, %rsp
movq %rdi, -8(%rbp)")).zip [4, 4]

-- wc_spin, listing lines 1359–1362, at .Lwc_spin.entry + 0
block_spec wc_spin_4 (-56) 16 ⟨-16, [(.rax, -16), (.rbp, 0)]⟩ (parse("movq -8(%rbp), %rdi
movq %rbp, %rsp
popq %rbp
jmp wc_spin")).zip [4, 3, 1, 2]

-- wc_spin, listing lines 1364–1371, at .Lwc_spin.stk + 0
block_spec wc_spin_5 (-56) 16 ⟨0, [(.rax, -16), (.rbp, 0)]⟩ (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $16, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]

-- wc_spin, listing lines 1373–1379, at .Lwc_spin.x15 + 0
block_spec wc_spin_6 (-56) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lwc_spin.chk")).zip [2, 2, 1, 1, 1, 1, 2]

-- wc_emit8, listing lines 1385–1386, at wc_emit8 + 0
block_spec wc_emit8_0 (-400) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]

-- wc_emit8, listing lines 1388–1388, at .Lwc_emit8.chk + 0
block_spec wc_emit8_1 (-400) 16 ⟨0, [(.rbp, 0)]⟩ (parse("leaq -400(%rsp), %rax")).zip [8]

-- wc_emit8, listing lines 1390–1391, at .Lwc_emit8.chk + 17
block_spec wc_emit8_2 (-400) 16 ⟨0, [(.rax, -400), (.rbp, 0)]⟩ (parse("cmpq %r11, %rax
jb .Lwc_emit8.stk")).zip [3, 6]

-- wc_emit8, listing lines 1392–1394, at .Lwc_emit8.chk + 26
block_spec wc_emit8_3 (-400) 16 ⟨0, [(.rax, -400), (.rbp, 0)]⟩ (parse("subq $400, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)")).zip [7, 4, 4]

-- wc_emit8, listing lines 1396–1397, at .Lwc_emit8.entry + 0
block_spec wc_emit8_4 (-400) 16 ⟨-400, [(.rax, -400), (.rbp, 0)]⟩ (parse("movq $0, %rax
movq $7, %rcx")).zip [7, 7]

-- wc_emit8, listing lines 1399–1401, at .Lwc_emit8.entry + 17
block_spec wc_emit8_5 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $8, %rcx")).zip [4, 4, 7]

-- wc_emit8, listing lines 1403–1405, at .Lwc_emit8.entry + 36
block_spec wc_emit8_6 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -32(%rbp)
movq -8(%rbp), %rax
movq -32(%rbp), %rcx")).zip [4, 4, 4]

-- wc_emit8, listing lines 1407–1420, at .Lwc_emit8.entry + 51
block_spec wc_emit8_7 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -40(%rbp)
movq -40(%rbp), %rax
movzbl %al, %eax
movq %rax, -48(%rbp)
movq -16(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
sete %al
movzbl %al, %eax
movq %rax, -56(%rbp)
movq -56(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_emit8.then5")).zip [4, 4, 3, 4, 4, 7, 3, 3, 3, 4, 4, 7, 3, 2]

-- wc_emit8, listing lines 1421–1421, at .Lwc_emit8.entry + 106
block_spec wc_emit8_8 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("jmp .Lwc_emit8.else6")).zip [2]

-- wc_emit8, listing lines 1423–1426, at .Lwc_emit8.then5 + 0
block_spec wc_emit8_9 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -16(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

-- wc_emit8, listing lines 1428–1433, at .Lwc_emit8.else6 + 0
block_spec wc_emit8_10 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -16(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movq %rax, -64(%rbp)
movq $1, %rax
movq $7, %rcx")).zip [4, 7, 3, 4, 7, 7]

-- wc_emit8, listing lines 1435–1437, at .Lwc_emit8.else6 + 35
block_spec wc_emit8_11 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -72(%rbp)
movq -72(%rbp), %rax
movq $8, %rcx")).zip [4, 4, 7]

-- wc_emit8, listing lines 1439–1441, at .Lwc_emit8.else6 + 54
block_spec wc_emit8_12 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -80(%rbp)
movq -8(%rbp), %rax
movq -80(%rbp), %rcx")).zip [4, 4, 4]

-- wc_emit8, listing lines 1443–1456, at .Lwc_emit8.else6 + 69
block_spec wc_emit8_13 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -88(%rbp)
movq -88(%rbp), %rax
movzbl %al, %eax
movq %rax, -96(%rbp)
movq -64(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
sete %al
movzbl %al, %eax
movq %rax, -104(%rbp)
movq -104(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_emit8.then13")).zip [4, 4, 3, 4, 4, 7, 3, 3, 3, 4, 4, 7, 3, 2]

-- wc_emit8, listing lines 1457–1457, at .Lwc_emit8.else6 + 124
block_spec wc_emit8_14 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("jmp .Lwc_emit8.else14")).zip [2]

-- wc_emit8, listing lines 1459–1462, at .Lwc_emit8.then13 + 0
block_spec wc_emit8_15 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

-- wc_emit8, listing lines 1464–1469, at .Lwc_emit8.else14 + 0
block_spec wc_emit8_16 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movq %rax, -112(%rbp)
movq $2, %rax
movq $7, %rcx")).zip [4, 7, 3, 4, 7, 7]

-- wc_emit8, listing lines 1471–1473, at .Lwc_emit8.else14 + 35
block_spec wc_emit8_17 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -120(%rbp)
movq -120(%rbp), %rax
movq $8, %rcx")).zip [4, 4, 7]

-- wc_emit8, listing lines 1475–1477, at .Lwc_emit8.else14 + 54
block_spec wc_emit8_18 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -128(%rbp)
movq -8(%rbp), %rax
movq -128(%rbp), %rcx")).zip [4, 4, 4]

-- wc_emit8, listing lines 1479–1492, at .Lwc_emit8.else14 + 69
block_spec wc_emit8_19 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -136(%rbp)
movq -136(%rbp), %rax
movzbl %al, %eax
movq %rax, -144(%rbp)
movq -112(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
sete %al
movzbl %al, %eax
movq %rax, -152(%rbp)
movq -152(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_emit8.then21")).zip [7, 7, 3, 7, 4, 7, 3, 3, 3, 7, 7, 7, 3, 2]

-- wc_emit8, listing lines 1493–1493, at .Lwc_emit8.else14 + 139
block_spec wc_emit8_20 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("jmp .Lwc_emit8.else22")).zip [2]

-- wc_emit8, listing lines 1495–1498, at .Lwc_emit8.then21 + 0
block_spec wc_emit8_21 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -112(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

-- wc_emit8, listing lines 1500–1505, at .Lwc_emit8.else22 + 0
block_spec wc_emit8_22 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -112(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movq %rax, -160(%rbp)
movq $3, %rax
movq $7, %rcx")).zip [4, 7, 3, 7, 7, 7]

-- wc_emit8, listing lines 1507–1509, at .Lwc_emit8.else22 + 38
block_spec wc_emit8_23 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -168(%rbp)
movq -168(%rbp), %rax
movq $8, %rcx")).zip [7, 7, 7]

-- wc_emit8, listing lines 1511–1513, at .Lwc_emit8.else22 + 63
block_spec wc_emit8_24 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -176(%rbp)
movq -8(%rbp), %rax
movq -176(%rbp), %rcx")).zip [7, 4, 7]

-- wc_emit8, listing lines 1515–1528, at .Lwc_emit8.else22 + 84
block_spec wc_emit8_25 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -184(%rbp)
movq -184(%rbp), %rax
movzbl %al, %eax
movq %rax, -192(%rbp)
movq -160(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
sete %al
movzbl %al, %eax
movq %rax, -200(%rbp)
movq -200(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_emit8.then29")).zip [7, 7, 3, 7, 7, 7, 3, 3, 3, 7, 7, 7, 3, 2]

-- wc_emit8, listing lines 1529–1529, at .Lwc_emit8.else22 + 157
block_spec wc_emit8_26 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("jmp .Lwc_emit8.else30")).zip [2]

-- wc_emit8, listing lines 1531–1534, at .Lwc_emit8.then29 + 0
block_spec wc_emit8_27 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -160(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]

-- wc_emit8, listing lines 1536–1541, at .Lwc_emit8.else30 + 0
block_spec wc_emit8_28 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -160(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movq %rax, -208(%rbp)
movq $4, %rax
movq $7, %rcx")).zip [7, 7, 3, 7, 7, 7]

-- wc_emit8, listing lines 1543–1545, at .Lwc_emit8.else30 + 41
block_spec wc_emit8_29 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -216(%rbp)
movq -216(%rbp), %rax
movq $8, %rcx")).zip [7, 7, 7]

-- wc_emit8, listing lines 1547–1549, at .Lwc_emit8.else30 + 66
block_spec wc_emit8_30 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -224(%rbp)
movq -8(%rbp), %rax
movq -224(%rbp), %rcx")).zip [7, 4, 7]

-- wc_emit8, listing lines 1551–1564, at .Lwc_emit8.else30 + 87
block_spec wc_emit8_31 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -232(%rbp)
movq -232(%rbp), %rax
movzbl %al, %eax
movq %rax, -240(%rbp)
movq -208(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
sete %al
movzbl %al, %eax
movq %rax, -248(%rbp)
movq -248(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_emit8.then37")).zip [7, 7, 3, 7, 7, 7, 3, 3, 3, 7, 7, 7, 3, 2]

-- wc_emit8, listing lines 1565–1565, at .Lwc_emit8.else30 + 160
block_spec wc_emit8_32 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("jmp .Lwc_emit8.else38")).zip [2]

-- wc_emit8, listing lines 1567–1570, at .Lwc_emit8.then37 + 0
block_spec wc_emit8_33 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -208(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]

-- wc_emit8, listing lines 1572–1577, at .Lwc_emit8.else38 + 0
block_spec wc_emit8_34 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -208(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movq %rax, -256(%rbp)
movq $5, %rax
movq $7, %rcx")).zip [7, 7, 3, 7, 7, 7]

-- wc_emit8, listing lines 1579–1581, at .Lwc_emit8.else38 + 41
block_spec wc_emit8_35 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -264(%rbp)
movq -264(%rbp), %rax
movq $8, %rcx")).zip [7, 7, 7]

-- wc_emit8, listing lines 1583–1585, at .Lwc_emit8.else38 + 66
block_spec wc_emit8_36 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -272(%rbp)
movq -8(%rbp), %rax
movq -272(%rbp), %rcx")).zip [7, 4, 7]

-- wc_emit8, listing lines 1587–1600, at .Lwc_emit8.else38 + 87
block_spec wc_emit8_37 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -280(%rbp)
movq -280(%rbp), %rax
movzbl %al, %eax
movq %rax, -288(%rbp)
movq -256(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
sete %al
movzbl %al, %eax
movq %rax, -296(%rbp)
movq -296(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_emit8.then45")).zip [7, 7, 3, 7, 7, 7, 3, 3, 3, 7, 7, 7, 3, 2]

-- wc_emit8, listing lines 1601–1601, at .Lwc_emit8.else38 + 160
block_spec wc_emit8_38 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("jmp .Lwc_emit8.else46")).zip [2]

-- wc_emit8, listing lines 1603–1606, at .Lwc_emit8.then45 + 0
block_spec wc_emit8_39 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -256(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]

-- wc_emit8, listing lines 1608–1613, at .Lwc_emit8.else46 + 0
block_spec wc_emit8_40 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -256(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movq %rax, -304(%rbp)
movq $6, %rax
movq $7, %rcx")).zip [7, 7, 3, 7, 7, 7]

-- wc_emit8, listing lines 1615–1617, at .Lwc_emit8.else46 + 41
block_spec wc_emit8_41 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -312(%rbp)
movq -312(%rbp), %rax
movq $8, %rcx")).zip [7, 7, 7]

-- wc_emit8, listing lines 1619–1621, at .Lwc_emit8.else46 + 66
block_spec wc_emit8_42 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -320(%rbp)
movq -8(%rbp), %rax
movq -320(%rbp), %rcx")).zip [7, 4, 7]

-- wc_emit8, listing lines 1623–1636, at .Lwc_emit8.else46 + 87
block_spec wc_emit8_43 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -328(%rbp)
movq -328(%rbp), %rax
movzbl %al, %eax
movq %rax, -336(%rbp)
movq -304(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
sete %al
movzbl %al, %eax
movq %rax, -344(%rbp)
movq -344(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_emit8.then53")).zip [7, 7, 3, 7, 7, 7, 3, 3, 3, 7, 7, 7, 3, 2]

-- wc_emit8, listing lines 1637–1637, at .Lwc_emit8.else46 + 160
block_spec wc_emit8_44 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("jmp .Lwc_emit8.else54")).zip [2]

-- wc_emit8, listing lines 1639–1642, at .Lwc_emit8.then53 + 0
block_spec wc_emit8_45 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -304(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]

-- wc_emit8, listing lines 1644–1649, at .Lwc_emit8.else54 + 0
block_spec wc_emit8_46 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -304(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movq %rax, -352(%rbp)
movq $7, %rax
movq $7, %rcx")).zip [7, 7, 3, 7, 7, 7]

-- wc_emit8, listing lines 1651–1653, at .Lwc_emit8.else54 + 41
block_spec wc_emit8_47 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -360(%rbp)
movq -360(%rbp), %rax
movq $8, %rcx")).zip [7, 7, 7]

-- wc_emit8, listing lines 1655–1657, at .Lwc_emit8.else54 + 66
block_spec wc_emit8_48 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -368(%rbp)
movq -8(%rbp), %rax
movq -368(%rbp), %rcx")).zip [7, 4, 7]

-- wc_emit8, listing lines 1659–1672, at .Lwc_emit8.else54 + 87
block_spec wc_emit8_49 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq %rax, -376(%rbp)
movq -376(%rbp), %rax
movzbl %al, %eax
movq %rax, -384(%rbp)
movq -352(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
sete %al
movzbl %al, %eax
movq %rax, -392(%rbp)
movq -392(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_emit8.then61")).zip [7, 7, 3, 7, 7, 7, 3, 3, 3, 7, 7, 7, 3, 2]

-- wc_emit8, listing lines 1673–1673, at .Lwc_emit8.else54 + 160
block_spec wc_emit8_50 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("jmp .Lwc_emit8.else62")).zip [2]

-- wc_emit8, listing lines 1675–1678, at .Lwc_emit8.then61 + 0
block_spec wc_emit8_51 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -352(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]

-- wc_emit8, listing lines 1680–1687, at .Lwc_emit8.else62 + 0
block_spec wc_emit8_52 (-400) 16 ⟨-400, [(.rbp, 0)]⟩ (parse("movq -352(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movq %rax, -400(%rbp)
movq -400(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 7, 3, 7, 7, 3, 1, 1]

-- wc_emit8, listing lines 1689–1696, at .Lwc_emit8.stk + 0
block_spec wc_emit8_53 (-400) 16 ⟨0, [(.rax, -400), (.rbp, 0)]⟩ (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $400, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]

-- wc_emit8, listing lines 1698–1704, at .Lwc_emit8.x16 + 0
block_spec wc_emit8_54 (-400) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lwc_emit8.chk")).zip [2, 2, 1, 1, 1, 1, 5]

-- wc_printL, listing lines 1710–1711, at wc_printL + 0
block_spec wc_printL_0 (-120) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]

-- wc_printL, listing lines 1713–1713, at .Lwc_printL.chk + 0
block_spec wc_printL_1 (-120) 16 ⟨0, [(.rbp, 0)]⟩ (parse("leaq -112(%rsp), %rax")).zip [5]

-- wc_printL, listing lines 1715–1716, at .Lwc_printL.chk + 14
block_spec wc_printL_2 (-120) 16 ⟨0, [(.rax, -112), (.rbp, 0)]⟩ (parse("cmpq %r11, %rax
jb .Lwc_printL.stk")).zip [3, 6]

-- wc_printL, listing lines 1717–1722, at .Lwc_printL.chk + 23
block_spec wc_printL_3 (-120) 16 ⟨0, [(.rax, -112), (.rbp, 0)]⟩ (parse("subq $112, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)
movq %rdx, -24(%rbp)
movq %rcx, -32(%rbp)
movq %r8, -40(%rbp)")).zip [4, 4, 4, 4, 4, 4]

-- wc_printL, listing lines 1724–1725, at .Lwc_printL.entry + 0
block_spec wc_printL_4 (-120) 16 ⟨-112, [(.rax, -112), (.rbp, 0)]⟩ (parse("movq -24(%rbp), %rax
movq $8, %rcx")).zip [4, 7]

-- wc_printL, listing lines 1727–1739, at .Lwc_printL.entry + 15
block_spec wc_printL_5 (-120) 16 ⟨-112, [(.rbp, 0)]⟩ (parse("movq %rax, -48(%rbp)
movq -16(%rbp), %rax
movq -48(%rbp), %rcx
addq %rcx, %rax
movq %rax, -56(%rbp)
movq -56(%rbp), %rax
movl %eax, %eax
movq %rax, -64(%rbp)
movq -8(%rbp), %rax
movq -64(%rbp), %rcx
addq %rcx, %rax
movq %rax, -72(%rbp)
movq -72(%rbp), %rcx")).zip [4, 4, 4, 3, 4, 4, 2, 4, 4, 4, 3, 4, 4]

-- wc_printL, listing lines 1741–1744, at .Lwc_printL.entry + 66
block_spec wc_printL_6 (-120) 16 ⟨-112, [(.rbp, 0)]⟩ (parse("movq %rax, -80(%rbp)
movq -80(%rbp), %rdi
movq -40(%rbp), %rsi
call wc_emit8")).zip [4, 4, 4, 5]

-- wc_printL, listing lines 1746–1750, at .Lwc_printL.x17 + 0
block_spec wc_printL_7 (-120) 16 ⟨-112, [(.rbp, 0)]⟩ (parse("movq %rax, -88(%rbp)
movq -32(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lwc_printL.then6")).zip [4, 4, 7, 3, 2]

-- wc_printL, listing lines 1751–1751, at .Lwc_printL.x17 + 20
block_spec wc_printL_8 (-120) 16 ⟨-112, [(.rbp, 0)]⟩ (parse("jmp .Lwc_printL.else7")).zip [2]

-- wc_printL, listing lines 1753–1756, at .Lwc_printL.then6 + 0
block_spec wc_printL_9 (-120) 16 ⟨-112, [(.rbp, 0)]⟩ (parse("movq -88(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 3, 1, 1]

-- wc_printL, listing lines 1758–1767, at .Lwc_printL.else7 + 0
block_spec wc_printL_10 (-120) 16 ⟨-112, [(.rbp, 0)]⟩ (parse("movq -32(%rbp), %rax
movq $1, %rcx
subq %rcx, %rax
movl $0, %edx
cmovb %rdx, %rax
movq %rax, -96(%rbp)
movq -24(%rbp), %rax
movq $1, %rcx
addq %rcx, %rax
jb .Lwc_printL.ovf")).zip [4, 7, 3, 5, 4, 4, 4, 7, 3, 2]

-- wc_printL, listing lines 1768–1776, at .Lwc_printL.else7 + 43
block_spec wc_printL_11 (-120) 16 ⟨-112, [(.rbp, 0)]⟩ (parse("movq %rax, -104(%rbp)
movq -8(%rbp), %rdi
movq -16(%rbp), %rsi
movq -104(%rbp), %rdx
movq -96(%rbp), %rcx
movq -88(%rbp), %r8
movq %rbp, %rsp
popq %rbp
jmp wc_printL")).zip [4, 4, 4, 4, 4, 4, 3, 1, 5]

-- wc_printL, listing lines 1778–1779, at .Lwc_printL.ovf + 0
block_spec wc_printL_12 (-120) 16 ⟨-112, [(.rbp, 0)]⟩ (parse("movl $1, %edi
call scc_rt_abort")).zip [5, 5]

-- wc_printL, listing lines 1782–1789, at .Lwc_printL.stk + 0
block_spec wc_printL_13 (-120) 16 ⟨0, [(.rax, -112), (.rbp, 0)]⟩ (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $112, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]

-- wc_printL, listing lines 1791–1797, at .Lwc_printL.x18 + 0
block_spec wc_printL_14 (-120) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lwc_printL.chk")).zip [2, 2, 1, 1, 1, 1, 5]

-- wc_rodata, listing lines 1803–1804, at wc_rodata + 0
block_spec wc_rodata_0 (-56) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]

-- wc_rodata, listing lines 1806–1806, at .Lwc_rodata.chk + 0
block_spec wc_rodata_1 (-56) 16 ⟨0, [(.rbp, 0)]⟩ (parse("leaq -32(%rsp), %rax")).zip [5]

-- wc_rodata, listing lines 1808–1809, at .Lwc_rodata.chk + 14
block_spec wc_rodata_2 (-56) 16 ⟨0, [(.rax, -32), (.rbp, 0)]⟩ (parse("cmpq %r11, %rax
jb .Lwc_rodata.stk")).zip [3, 2]

-- wc_rodata, listing lines 1810–1810, at .Lwc_rodata.chk + 19
block_spec wc_rodata_3 (-56) 16 ⟨0, [(.rax, -32), (.rbp, 0)]⟩ (parse("subq $32, %rsp")).zip [4]

-- wc_rodata, listing lines 1812–1814, at .Lwc_rodata.entry + 0
block_spec wc_rodata_4 (-56) 16 ⟨-32, [(.rax, -32), (.rbp, 0)]⟩ (parse("movq $257, %rdi
movq $2, %rsi
call scc_rt_alloc")).zip [7, 7, 5]

-- wc_rodata, listing lines 1816–1817, at .Lwc_rodata.x19 + 0
block_spec wc_rodata_5 (-56) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -8(%rbp)
movq -8(%rbp), %rcx")).zip [4, 4]

-- wc_rodata, listing lines 1819–1821, at .Lwc_rodata.x19 + 11
block_spec wc_rodata_6 (-56) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq -8(%rbp), %rcx
movabsq $8583909746840200520, %rax")).zip [4, 4, 10]

-- wc_rodata, listing lines 1823–1823, at .Lwc_rodata.x19 + 32
block_spec wc_rodata_7 (-56) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx")).zip [4]

-- wc_rodata, listing lines 1825–1827, at .Lwc_rodata.x19 + 40
block_spec wc_rodata_8 (-56) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq %rax, -24(%rbp)
movq -8(%rbp), %rcx
movabsq $44634501743, %rax")).zip [4, 4, 10]

-- wc_rodata, listing lines 1830–1836, at .Lwc_rodata.x19 + 62
block_spec wc_rodata_9 (-56) 16 ⟨-32, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
movq $0, %rdx
movq $2, %rcx
movq $13, %rsi
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 7, 7, 7, 3, 1, 1]

-- wc_rodata, listing lines 1838–1845, at .Lwc_rodata.stk + 0
block_spec wc_rodata_10 (-56) 16 ⟨0, [(.rax, -32), (.rbp, 0)]⟩ (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $32, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]

-- wc_rodata, listing lines 1847–1853, at .Lwc_rodata.x20 + 0
block_spec wc_rodata_11 (-56) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lwc_rodata.chk")).zip [2, 2, 1, 1, 1, 1, 5]

-- wc_worker, listing lines 1859–1860, at wc_worker + 0
block_spec wc_worker_0 (-88) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]

-- wc_worker, listing lines 1862–1862, at .Lwc_worker.chk + 0
block_spec wc_worker_1 (-88) 16 ⟨0, [(.rbp, 0)]⟩ (parse("leaq -80(%rsp), %rax")).zip [5]

-- wc_worker, listing lines 1864–1865, at .Lwc_worker.chk + 14
block_spec wc_worker_2 (-88) 16 ⟨0, [(.rax, -80), (.rbp, 0)]⟩ (parse("cmpq %r11, %rax
jb .Lwc_worker.stk")).zip [3, 6]

-- wc_worker, listing lines 1866–1872, at .Lwc_worker.chk + 23
block_spec wc_worker_3 (-88) 16 ⟨0, [(.rax, -80), (.rbp, 0)]⟩ (parse("subq $80, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)
movq %rdx, -24(%rbp)
movq %rcx, -32(%rbp)
movq %r8, -40(%rbp)
movq %r9, -48(%rbp)")).zip [4, 4, 4, 4, 4, 4, 4]

-- wc_worker, listing lines 1874–1882, at .Lwc_worker.entry + 0
block_spec wc_worker_4 (-88) 16 ⟨-80, [(.rax, -80), (.rbp, 0)]⟩ (parse("movq -16(%rbp), %rax
movl %eax, %eax
movq %rax, -56(%rbp)
movq -8(%rbp), %rax
movq -56(%rbp), %rcx
addq %rcx, %rax
movq %rax, -64(%rbp)
movq -24(%rbp), %rax
movq $8, %rcx")).zip [4, 2, 4, 4, 4, 3, 4, 4, 7]

-- wc_worker, listing lines 1884–1895, at .Lwc_worker.entry + 40
block_spec wc_worker_5 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq %rax, -72(%rbp)
movq -32(%rbp), %rdx
movq -72(%rbp), %rsi
movq -32(%rbp), %rax
movq -72(%rbp), %rcx
cmpq %rcx, %rax
movq %rsi, %rax
cmovb %rdx, %rax
movq %rax, -80(%rbp)
movq -64(%rbp), %rdi
movq -80(%rbp), %rsi
call scc_rt_print")).zip [4, 4, 4, 4, 4, 3, 3, 4, 4, 4, 4, 5]

-- wc_worker, listing lines 1897–1898, at .Lwc_worker.x21 + 0
block_spec wc_worker_6 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -40(%rbp), %rcx
movq $1, %rax")).zip [4, 7]

-- wc_worker, listing lines 1900–1901, at .Lwc_worker.x21 + 14
block_spec wc_worker_7 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -48(%rbp), %rdi
call scc_rt_unpark")).zip [4, 5]

-- wc_worker, listing lines 1903–1905, at .Lwc_worker.x22 + 0
block_spec wc_worker_8 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

-- wc_worker, listing lines 1907–1914, at .Lwc_worker.stk + 0
block_spec wc_worker_9 (-88) 16 ⟨0, [(.rax, -80), (.rbp, 0)]⟩ (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $80, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]

-- wc_worker, listing lines 1916–1922, at .Lwc_worker.x23 + 0
block_spec wc_worker_10 (-88) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lwc_worker.chk")).zip [2, 2, 1, 1, 1, 1, 5]

-- wc_waitLoop, listing lines 1928–1929, at wc_waitLoop + 0
block_spec wc_waitLoop_0 (-56) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]

-- wc_waitLoop, listing lines 1931–1931, at .Lwc_waitLoop.chk + 0
block_spec wc_waitLoop_1 (-56) 16 ⟨0, [(.rbp, 0)]⟩ (parse("leaq -16(%rsp), %rax")).zip [5]

-- wc_waitLoop, listing lines 1933–1934, at .Lwc_waitLoop.chk + 14
block_spec wc_waitLoop_2 (-56) 16 ⟨0, [(.rax, -16), (.rbp, 0)]⟩ (parse("cmpq %r11, %rax
jb .Lwc_waitLoop.stk")).zip [3, 2]

-- wc_waitLoop, listing lines 1935–1936, at .Lwc_waitLoop.chk + 19
block_spec wc_waitLoop_3 (-56) 16 ⟨0, [(.rax, -16), (.rbp, 0)]⟩ (parse("subq $16, %rsp
movq %rdi, -8(%rbp)")).zip [4, 4]

-- wc_waitLoop, listing lines 1938–1938, at .Lwc_waitLoop.entry + 0
block_spec wc_waitLoop_4 (-56) 16 ⟨-16, [(.rax, -16), (.rbp, 0)]⟩ (parse("movq -8(%rbp), %rcx")).zip [4]

-- wc_waitLoop, listing lines 1940–1944, at .Lwc_waitLoop.entry + 7
block_spec wc_waitLoop_5 (-56) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_waitLoop.then1")).zip [4, 4, 7, 3, 2]

-- wc_waitLoop, listing lines 1945–1945, at .Lwc_waitLoop.entry + 27
block_spec wc_waitLoop_6 (-56) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("jmp .Lwc_waitLoop.else2")).zip [2]

-- wc_waitLoop, listing lines 1947–1950, at .Lwc_waitLoop.then1 + 0
block_spec wc_waitLoop_7 (-56) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq $0, %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]

-- wc_waitLoop, listing lines 1952–1952, at .Lwc_waitLoop.else2 + 0
block_spec wc_waitLoop_8 (-56) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("call scc_rt_park")).zip [5]

-- wc_waitLoop, listing lines 1954–1957, at .Lwc_waitLoop.x24 + 0
block_spec wc_waitLoop_9 (-56) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rdi
movq %rbp, %rsp
popq %rbp
jmp wc_waitLoop")).zip [4, 3, 1, 2]

-- wc_waitLoop, listing lines 1959–1966, at .Lwc_waitLoop.stk + 0
block_spec wc_waitLoop_10 (-56) 16 ⟨0, [(.rax, -16), (.rbp, 0)]⟩ (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $16, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]

-- wc_waitLoop, listing lines 1968–1974, at .Lwc_waitLoop.x25 + 0
block_spec wc_waitLoop_11 (-56) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lwc_waitLoop.chk")).zip [2, 2, 1, 1, 1, 1, 2]

-- wc_main, listing lines 1980–1981, at wc_main + 0
block_spec wc_main_0 (-88) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp")).zip [1, 3]

-- wc_main, listing lines 1983–1983, at .Lwc_main.chk + 0
block_spec wc_main_1 (-88) 16 ⟨0, [(.rbp, 0)]⟩ (parse("leaq -80(%rsp), %rax")).zip [5]

-- wc_main, listing lines 1985–1986, at .Lwc_main.chk + 14
block_spec wc_main_2 (-88) 16 ⟨0, [(.rax, -80), (.rbp, 0)]⟩ (parse("cmpq %r11, %rax
jb .Lwc_main.stk")).zip [3, 6]

-- wc_main, listing lines 1987–1992, at .Lwc_main.chk + 23
block_spec wc_main_3 (-88) 16 ⟨0, [(.rax, -80), (.rbp, 0)]⟩ (parse("subq $80, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)
movq %rdx, -24(%rbp)
movq %rcx, -32(%rbp)
movq %r8, -40(%rbp)")).zip [4, 4, 4, 4, 4, 4]

-- wc_main, listing lines 1994–1996, at .Lwc_main.entry + 0
block_spec wc_main_4 (-88) 16 ⟨-80, [(.rax, -80), (.rbp, 0)]⟩ (parse("movq $256, %rdi
movq $1, %rsi
call scc_rt_alloc")).zip [7, 7, 5]

-- wc_main, listing lines 1998–2000, at .Lwc_main.x26 + 0
block_spec wc_main_5 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq %rax, -48(%rbp)
movq -48(%rbp), %rcx
movq $0, %rax")).zip [4, 4, 7]

-- wc_main, listing lines 2003–2003, at .Lwc_main.x26 + 18
block_spec wc_main_6 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("call scc_rt_thread_reserve")).zip [5]

-- wc_main, listing lines 2005–2008, at .Lwc_main.x27 + 0
block_spec wc_main_7 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq %rax, -56(%rbp)
movq $12585731, %rdi
movq $1, %rsi
call scc_rt_alloc_tcb")).zip [4, 7, 7, 5]

-- wc_main, listing lines 2010–2012, at .Lwc_main.x28 + 0
block_spec wc_main_8 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq %rax, -64(%rbp)
movq -64(%rbp), %rcx
movq -56(%rbp), %rax")).zip [4, 4, 4]

-- wc_main, listing lines 2014–2015, at .Lwc_main.x28 + 16
block_spec wc_main_9 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rcx
movq -8(%rbp), %rax")).zip [4, 4]

-- wc_main, listing lines 2017–2018, at .Lwc_main.x28 + 28
block_spec wc_main_10 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rcx
movq -16(%rbp), %rax")).zip [4, 4]

-- wc_main, listing lines 2020–2021, at .Lwc_main.x28 + 40
block_spec wc_main_11 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rcx
movq -24(%rbp), %rax")).zip [4, 4]

-- wc_main, listing lines 2023–2024, at .Lwc_main.x28 + 52
block_spec wc_main_12 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rcx
movq -32(%rbp), %rax")).zip [4, 4]

-- wc_main, listing lines 2026–2027, at .Lwc_main.x28 + 64
block_spec wc_main_13 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rcx
movq -48(%rbp), %rax")).zip [4, 4]

-- wc_main, listing lines 2029–2030, at .Lwc_main.x28 + 76
block_spec wc_main_14 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rcx
movq -40(%rbp), %rax")).zip [4, 4]

-- wc_main, listing lines 2032–2033, at .Lwc_main.x28 + 88
block_spec wc_main_15 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %rdi
call scc_rt_thread_init")).zip [4, 5]

-- wc_main, listing lines 2035–2035, at .Lwc_main.x29 + 0
block_spec wc_main_16 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq %rax, -72(%rbp)")).zip [4]

-- wc_main, listing lines 2037–2040, at .Lwc_main.x29 + 7
block_spec wc_main_17 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -64(%rbp), %r12
movq -72(%rbp), %rsi
movq -64(%rbp), %r8
movl $855808, %edi")).zip [4, 4, 4, 5]

-- wc_main, listing lines 2043–2043, at .Lwc_main.x29 + 29
block_spec wc_main_18 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movl $56, %eax")).zip [5]

-- wc_main, listing lines 2046–2046, at .Lwc_main.x29 + 39
block_spec wc_main_19 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("jne .Lwc_main.x30")).zip [2]

-- wc_main, listing lines 2048–2049, at .Lwc_main.x29 + 43
block_spec wc_main_20 (-88) 16 ⟨-80, []⟩ (parse("movq %r12, %rdi
call scc_rt_thr_worker")).zip [3, 5]

-- wc_main, listing lines 2052–2056, at .Lwc_main.x30 + 0
block_spec wc_main_21 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq %rax, -80(%rbp)
movq -80(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
jl .Lwc_main.spawnfail5")).zip [4, 4, 7, 3, 2]

-- wc_main, listing lines 2057–2057, at .Lwc_main.x30 + 20
block_spec wc_main_22 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("jmp .Lwc_main.spawned6")).zip [2]

-- wc_main, listing lines 2059–2060, at .Lwc_main.spawnfail5 + 0
block_spec wc_main_23 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq $5, %rdi
call scc_rt_abort")).zip [7, 5]

-- wc_main, listing lines 2064–2067, at .Lwc_main.spawned6 + 0
block_spec wc_main_24 (-88) 16 ⟨-80, [(.rbp, 0)]⟩ (parse("movq -48(%rbp), %rdi
movq %rbp, %rsp
popq %rbp
jmp wc_waitLoop")).zip [4, 3, 1, 5]

-- wc_main, listing lines 2069–2076, at .Lwc_main.stk + 0
block_spec wc_main_25 (-88) 16 ⟨0, [(.rax, -80), (.rbp, 0)]⟩ (parse("pushq %rdi
pushq %rsi
pushq %rdx
pushq %rcx
pushq %r8
pushq %r9
movl $80, %edi
call scc_rt_morestack")).zip [1, 1, 1, 1, 2, 2, 5, 5]

-- wc_main, listing lines 2078–2084, at .Lwc_main.x32 + 0
block_spec wc_main_26 (-88) 16 ⟨-48, [(.rbp, 0)]⟩ (parse("popq %r9
popq %r8
popq %rcx
popq %rdx
popq %rsi
popq %rdi
jmp .Lwc_main.chk")).zip [2, 2, 1, 1, 1, 1, 5]

-- scc_rt_morestack, listing lines 2089–2093, at scc_rt_morestack + 0
block_spec scc_rt_morestack_0 (-8) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
movq %rdi, %rsi
movq %rbp, %rdi
call scc_rt_grow")).zip [1, 3, 3, 3, 5]

-- scc_rt_morestack, listing lines 2094–2094, at scc_rt_morestack + 15
block_spec scc_rt_morestack_1 (-8) 16 ⟨0, [(.rbp, 0)]⟩ (parse("addq %rax, %rbp")).zip [3]

-- scc_rt_morestack, listing lines 2096–2098, at scc_rt_morestack + 21
block_spec scc_rt_morestack_2 (-8) 16 ⟨0, []⟩ (parse("movq %rdx, %rdi
movq %rcx, %rsi
call scc_rt_stack_release")).zip [3, 3, 5]

-- scc_rt_morestack, listing lines 2099–2100, at scc_rt_morestack + 32
block_spec scc_rt_morestack_3 (-8) 16 ⟨0, []⟩ (parse("popq %rbp
ret")).zip [1, 1]

end Spike.Lib.X64.Hello
