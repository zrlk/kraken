import Scc.Cert.Rt.CodeA64
import Scc.Test.RtA64AbortTest

/-!
# Every block of `hello1.w`'s AArch64 code at its place

The table of places of the `block_spec` blocks of `hello1.w`'s AArch64 listing
(`Spike/Gen/genblocks_a64.py`'s block data for `hello1.w`), grouped per function in program order, checked against the program scc emits by one
`kernel_rfl` (`blocksIn`, `Scc/Cert/Rt/CodeA64.lean`): every block is code
at its label and offset in every valid layout of the program
(`codeAt_of_blocksIn`). Generated (the seed of `scc --cert`).
-/

namespace Scc.Test.RtA64BlocksHello1

open Kraken Kraken.Promising.AArch64 Kraken.AArch64.Parser Scc.Cert.Rt.A64 Scc.Test.RtA64Abort

/-- The blocks of `_start`. -/
def hello1T_start : List Grp := [
  ⟨"_start", [(0, parseAArch64("b scc_rt_start")) /- _start_0 -/]⟩
]

/-- The blocks of `scc_rt_start`. -/
def hello1T_scc_rt_start : List Grp := [
  ⟨"scc_rt_start", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")) /- scc_rt_start_0 -/]⟩,
  ⟨".L0_scc_rt_start.0_entry", [(2, parseAArch64("str x9, [sp]
movz x0, #13
ldr x1, [sp]
movz x2, #0
movz x3, #8
movz x8, #134")) /- scc_rt_start_1 -/,
    (9, parseAArch64("str x0, [sp, #8]
movz x0, #2307
movz x1, #1
bl scc_rt_alloc_tcb")) /- scc_rt_start_2 -/]⟩,
  ⟨".L0_scc_rt_start.sp2", [(0, parseAArch64("str x0, [sp, #16]
ldr x0, [sp, #16]
bl scc_rt_thread_init")) /- scc_rt_start_3 -/]⟩,
  ⟨".L0_scc_rt_start.sp3", [(0, parseAArch64("str x0, [sp, #24]
ldr x9, [sp, #24]
ldr x10, [sp, #16]
ldr x0, [sp, #16]")) /- scc_rt_start_4 -/,
    (6, parseAArch64("movz x29, #0
bl scc_rt_main")) /- scc_rt_start_5 -/]⟩,
  ⟨".L0_scc_rt_start.halt4", [(0, parseAArch64("b .L0_scc_rt_start.halt4")) /- scc_rt_start_6 -/]⟩
]

/-- The blocks of `scc_rt_main`. -/
def hello1T_scc_rt_main : List Grp := [
  ⟨".L1_scc_rt_main.stack_check", [(0, parseAArch64("sub x9, sp, #80
mrs x10, tpidr_el0")) /- scc_rt_main_0 -/,
    (3, parseAArch64("subs xzr, x9, x10
b.lo .L1_scc_rt_main.stack_grow")) /- scc_rt_main_1 -/,
    (5, parseAArch64("add sp, x9, #0
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
str x0, [sp]")) /- scc_rt_main_2 -/]⟩,
  ⟨".L1_scc_rt_main.0_entry", [(0, parseAArch64("bl wc_rodata")) /- scc_rt_main_3 -/]⟩,
  ⟨".L1_scc_rt_main.sp0", [(0, parseAArch64("str x0, [sp, #8]
str x1, [sp, #16]
str x2, [sp, #24]
str x3, [sp, #32]
ldr x0, [sp, #8]
ldr x1, [sp, #16]
ldr x2, [sp, #24]
ldr x3, [sp, #32]
ldr x4, [sp]
bl wc_main")) /- scc_rt_main_4 -/]⟩,
  ⟨".L1_scc_rt_main.sp1", [(0, parseAArch64("str x0, [sp, #40]
ldr x0, [sp, #40]
movz x8, #94")) /- scc_rt_main_5 -/,
    (4, parseAArch64("str x0, [sp, #48]")) /- scc_rt_main_6 -/]⟩,
  ⟨".L1_scc_rt_main.halt3", [(0, parseAArch64("b .L1_scc_rt_main.halt3")) /- scc_rt_main_7 -/]⟩,
  ⟨".L1_scc_rt_main.stack_grow", [(0, parseAArch64("sub sp, sp, #80
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
bl scc_rt_morestack")) /- scc_rt_main_8 -/]⟩,
  ⟨".L1_scc_rt_main.sp_check", [(0, parseAArch64("ldr x0, [sp]
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
b .L1_scc_rt_main.stack_check")) /- scc_rt_main_9 -/]⟩
]

/-- The blocks of `scc_rt_alloc`. -/
def hello1T_scc_rt_alloc : List Grp := [
  ⟨"scc_rt_alloc", [(0, parseAArch64("sub sp, sp, #160
str x29, [sp, #144]
str x30, [sp, #152]
add x29, sp, #144
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]")) /- scc_rt_alloc_0 -/]⟩,
  ⟨".L2_scc_rt_alloc.0_entry", [(0, parseAArch64("ldr x9, [sp, #8]
movz x10, #4096, lsl #16
subs xzr, x9, x10
b.hs .L2_scc_rt_alloc.4_full")) /- scc_rt_alloc_1 -/,
    (4, parseAArch64("b .L2_scc_rt_alloc.1_cnt")) /- scc_rt_alloc_2 -/]⟩,
  ⟨".L2_scc_rt_alloc.1_cnt", [(2, parseAArch64("str x9, [sp, #24]
ldr x9, [sp, #16]
ldr x10, [sp, #24]")) /- scc_rt_alloc_3 -/,
    (6, parseAArch64("str x11, [sp, #32]
ldr x9, [sp, #32]
ldr x10, [sp, #16]
add x9, x9, x10
str x9, [sp, #40]
ldr x9, [sp, #40]
movz x10, #64, lsl #16
subs xzr, x9, x10
b.hi .L2_scc_rt_alloc.2_slow")) /- scc_rt_alloc_4 -/,
    (15, parseAArch64("b .L2_scc_rt_alloc.5_ok")) /- scc_rt_alloc_5 -/]⟩,
  ⟨".L2_scc_rt_alloc.2_slow", [(0, parseAArch64("ldr x9, [sp, #32]
movz x10, #64, lsl #16
subs xzr, x9, x10
b.hi .L2_scc_rt_alloc.3_spin")) /- scc_rt_alloc_6 -/,
    (4, parseAArch64("b .L2_scc_rt_alloc.4_full")) /- scc_rt_alloc_7 -/]⟩,
  ⟨".L2_scc_rt_alloc.3_spin", [(0, parseAArch64("b .L2_scc_rt_alloc.3_spin")) /- scc_rt_alloc_8 -/]⟩,
  ⟨".L2_scc_rt_alloc.4_full", [(0, parseAArch64("movz x0, #2
bl scc_rt_abort")) /- scc_rt_alloc_9 -/]⟩,
  ⟨".L2_scc_rt_alloc.halt8", [(0, parseAArch64("b .L2_scc_rt_alloc.halt8")) /- scc_rt_alloc_10 -/]⟩,
  ⟨".L2_scc_rt_alloc.5_ok", [(0, parseAArch64("ldr x9, [sp]
movz x10, #22
lsrv x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #48]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #56]")) /- scc_rt_alloc_11 -/,
    (10, parseAArch64("str x9, [sp, #64]
ldr x9, [sp, #32]
movz x10, #4
lslv x9, x9, x10
str x9, [sp, #72]
ldr x9, [sp, #64]
ldr x10, [sp, #72]
add x9, x9, x10
str x9, [sp, #80]
ldr x9, [sp, #8]
ldr x10, [sp, #56]
madd x9, x9, x10, xzr
str x9, [sp, #88]
ldr x9, [sp, #88]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #96]
ldr x9, [sp, #8]
movz x10, #36
lslv x9, x9, x10
str x9, [sp, #104]
ldr x9, [sp]
ldr x10, [sp, #104]
orr x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #80]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #120]
ldr x9, [sp, #112]
ldr x10, [sp, #120]")) /- scc_rt_alloc_12 -/,
    (42, parseAArch64("ldr x9, [sp, #80]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #128]
ldr x9, [sp, #128]
movz x10, #8
add x9, x9, x10
str x9, [sp, #136]
ldr x0, [sp, #136]
ldr x29, [sp, #144]
ldr x30, [sp, #152]
add sp, sp, #160
ret")) /- scc_rt_alloc_13 -/]⟩
]

/-- The blocks of `scc_rt_alloc_tcb`. -/
def hello1T_scc_rt_alloc_tcb : List Grp := [
  ⟨"scc_rt_alloc_tcb", [(0, parseAArch64("sub sp, sp, #192
str x29, [sp, #176]
str x30, [sp, #184]
add x29, sp, #176
str x0, [sp]
str x1, [sp, #8]")) /- scc_rt_alloc_tcb_0 -/]⟩,
  ⟨".L3_scc_rt_alloc_tcb.0_entry", [(0, parseAArch64("ldr x9, [sp, #8]
movz x10, #4096, lsl #16
subs xzr, x9, x10
b.hs .L3_scc_rt_alloc_tcb.2_full")) /- scc_rt_alloc_tcb_1 -/,
    (4, parseAArch64("b .L3_scc_rt_alloc_tcb.1_len")) /- scc_rt_alloc_tcb_2 -/]⟩,
  ⟨".L3_scc_rt_alloc_tcb.1_len", [(0, parseAArch64("ldr x9, [sp]
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
str x9, [sp, #72]")) /- scc_rt_alloc_tcb_3 -/,
    (34, parseAArch64("str x9, [sp, #80]
ldr x9, [sp, #72]
ldr x10, [sp, #80]")) /- scc_rt_alloc_tcb_4 -/,
    (38, parseAArch64("str x11, [sp, #88]
ldr x9, [sp, #88]
ldr x10, [sp, #72]
add x9, x9, x10
str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #2, lsl #16
subs xzr, x9, x10
b.hi .L3_scc_rt_alloc_tcb.2_full")) /- scc_rt_alloc_tcb_5 -/,
    (47, parseAArch64("b .L3_scc_rt_alloc_tcb.3_ok")) /- scc_rt_alloc_tcb_6 -/]⟩,
  ⟨".L3_scc_rt_alloc_tcb.2_full", [(0, parseAArch64("movz x0, #5
bl scc_rt_abort")) /- scc_rt_alloc_tcb_7 -/]⟩,
  ⟨".L3_scc_rt_alloc_tcb.halt14", [(0, parseAArch64("b .L3_scc_rt_alloc_tcb.halt14")) /- scc_rt_alloc_tcb_8 -/]⟩,
  ⟨".L3_scc_rt_alloc_tcb.3_ok", [(2, parseAArch64("str x9, [sp, #104]
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
ldr x10, [sp, #152]")) /- scc_rt_alloc_tcb_9 -/,
    (30, parseAArch64("ldr x9, [sp, #112]
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
ret")) /- scc_rt_alloc_tcb_10 -/]⟩
]

/-- The blocks of `scc_rt_thread_reserve`. -/
def hello1T_scc_rt_thread_reserve : List Grp := [
  ⟨"scc_rt_thread_reserve", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")) /- scc_rt_thread_reserve_0 -/]⟩,
  ⟨".L4_scc_rt_thread_reserve.0_entry", [(2, parseAArch64("str x9, [sp]
movz x9, #1
ldr x10, [sp]")) /- scc_rt_thread_reserve_1 -/,
    (6, parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #1023
subs xzr, x9, x10
b.hi .L4_scc_rt_thread_reserve.1_full")) /- scc_rt_thread_reserve_2 -/,
    (15, parseAArch64("b .L4_scc_rt_thread_reserve.2_ok")) /- scc_rt_thread_reserve_3 -/]⟩,
  ⟨".L4_scc_rt_thread_reserve.1_full", [(0, parseAArch64("movz x0, #5
bl scc_rt_abort")) /- scc_rt_thread_reserve_4 -/]⟩,
  ⟨".L4_scc_rt_thread_reserve.halt5", [(0, parseAArch64("b .L4_scc_rt_thread_reserve.halt5")) /- scc_rt_thread_reserve_5 -/]⟩,
  ⟨".L4_scc_rt_thread_reserve.2_ok", [(0, parseAArch64("ldr x0, [sp, #16]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")) /- scc_rt_thread_reserve_6 -/]⟩
]

/-- The blocks of `scc_rt_thread_init`. -/
def hello1T_scc_rt_thread_init : List Grp := [
  ⟨"scc_rt_thread_init", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]")) /- scc_rt_thread_init_0 -/]⟩,
  ⟨".L5_scc_rt_thread_init.0_entry", [(0, parseAArch64("movz x0, #16384
bl scc_rt_stack_take")) /- scc_rt_thread_init_1 -/]⟩,
  ⟨".L5_scc_rt_thread_init.sp0", [(0, parseAArch64("str x0, [sp, #8]
ldr x9, [sp, #8]
movz x10, #4096
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #8]
movz x10, #16384
add x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp]
ldr x10, [sp]")) /- scc_rt_thread_init_2 -/,
    (12, parseAArch64("ldr x9, [sp, #16]
ldr x10, [sp]")) /- scc_rt_thread_init_3 -/,
    (15, parseAArch64("movz x9, #0
ldr x10, [sp]")) /- scc_rt_thread_init_4 -/,
    (18, parseAArch64("movz x9, #0
ldr x10, [sp]")) /- scc_rt_thread_init_5 -/,
    (21, parseAArch64("ldr x9, [sp, #8]
ldr x10, [sp]")) /- scc_rt_thread_init_6 -/,
    (24, parseAArch64("ldr x9, [sp, #24]
ldr x10, [sp]")) /- scc_rt_thread_init_7 -/,
    (27, parseAArch64("ldr x0, [sp, #24]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")) /- scc_rt_thread_init_8 -/]⟩
]

/-- The blocks of `scc_rt_stack_take`. -/
def hello1T_scc_rt_stack_take : List Grp := [
  ⟨"scc_rt_stack_take", [(0, parseAArch64("sub sp, sp, #208
str x29, [sp, #192]
str x30, [sp, #200]
add x29, sp, #192
str x0, [sp]")) /- scc_rt_stack_take_0 -/]⟩,
  ⟨".L6_scc_rt_stack_take.0_entry", [(0, parseAArch64("movz x9, #16384
str x9, [sp, #8]
movz x9, #0
str x9, [sp, #16]
movz x9, #32768
str x9, [sp, #24]
movz x9, #0
str x9, [sp, #32]
b .L6_scc_rt_stack_take.1_cls5")) /- scc_rt_stack_take_1 -/]⟩,
  ⟨".L6_scc_rt_stack_take.1_cls5", [(0, parseAArch64("ldr x9, [sp, #8]
ldr x10, [sp]
subs xzr, x9, x10
b.lo .L6_scc_rt_stack_take.2_clsnext6")) /- scc_rt_stack_take_2 -/,
    (4, parseAArch64("b .L6_scc_rt_stack_take.3_clsdone7")) /- scc_rt_stack_take_3 -/]⟩,
  ⟨".L6_scc_rt_stack_take.2_clsnext6", [(0, parseAArch64("ldr x9, [sp, #24]
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
b .L6_scc_rt_stack_take.1_cls5")) /- scc_rt_stack_take_4 -/]⟩,
  ⟨".L6_scc_rt_stack_take.3_clsdone7", [(2, parseAArch64("str x9, [sp, #48]
ldr x9, [sp, #48]
ldr x10, [sp, #32]
add x9, x9, x10
str x9, [sp, #56]")) /- scc_rt_stack_take_5 -/,
    (9, parseAArch64("str x9, [sp, #64]
ldr x9, [sp, #64]
ldr x10, [sp, #16]
add x9, x9, x10
str x9, [sp, #72]")) /- scc_rt_stack_take_6 -/,
    (16, parseAArch64("str x9, [sp, #80]
b .L6_scc_rt_stack_take.4_spin14")) /- scc_rt_stack_take_7 -/]⟩,
  ⟨".L6_scc_rt_stack_take.4_spin14", [(0, parseAArch64("movz x9, #1
ldr x10, [sp, #80]")) /- scc_rt_stack_take_8 -/,
    (3, parseAArch64("str x11, [sp, #88]
ldr x9, [sp, #88]
movz x10, #0
subs xzr, x9, x10
b.eq .L6_scc_rt_stack_take.5_locked15")) /- scc_rt_stack_take_9 -/,
    (8, parseAArch64("b .L6_scc_rt_stack_take.4_spin14")) /- scc_rt_stack_take_10 -/]⟩,
  ⟨".L6_scc_rt_stack_take.5_locked15", [(0, parseAArch64("ldr x10, [sp, #56]")) /- scc_rt_stack_take_11 -/,
    (2, parseAArch64("str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #0
subs xzr, x9, x10
b.eq .L6_scc_rt_stack_take.7_bump")) /- scc_rt_stack_take_12 -/,
    (7, parseAArch64("b .L6_scc_rt_stack_take.6_pop")) /- scc_rt_stack_take_13 -/]⟩,
  ⟨".L6_scc_rt_stack_take.6_pop", [(0, parseAArch64("ldr x9, [sp, #96]
movz x10, #1
sub x9, x9, x10
str x9, [sp, #104]
ldr x9, [sp, #104]
ldr x10, [sp, #56]")) /- scc_rt_stack_take_14 -/,
    (7, parseAArch64("ldr x9, [sp, #104]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #72]
ldr x10, [sp, #112]
add x9, x9, x10
str x9, [sp, #120]
ldr x10, [sp, #120]")) /- scc_rt_stack_take_15 -/,
    (17, parseAArch64("str x9, [sp, #128]")) /- scc_rt_stack_take_16 -/,
    (20, parseAArch64("str x9, [sp, #136]
movz x9, #0
ldr x10, [sp, #136]")) /- scc_rt_stack_take_17 -/,
    (24, parseAArch64("b .L6_scc_rt_stack_take.10_taken")) /- scc_rt_stack_take_18 -/]⟩,
  ⟨".L6_scc_rt_stack_take.7_bump", [(2, parseAArch64("str x9, [sp, #144]
movz x9, #0
ldr x10, [sp, #144]")) /- scc_rt_stack_take_19 -/,
    (8, parseAArch64("str x9, [sp, #152]
ldr x9, [sp]
ldr x10, [sp, #152]")) /- scc_rt_stack_take_20 -/,
    (12, parseAArch64("str x11, [sp, #160]
ldr x9, [sp, #160]
ldr x10, [sp]
add x9, x9, x10
str x9, [sp, #168]
ldr x9, [sp, #168]
movz x10, #8192, lsl #16
subs xzr, x9, x10
b.hi .L6_scc_rt_stack_take.8_full")) /- scc_rt_stack_take_21 -/,
    (21, parseAArch64("b .L6_scc_rt_stack_take.9_ok")) /- scc_rt_stack_take_22 -/]⟩,
  ⟨".L6_scc_rt_stack_take.8_full", [(0, parseAArch64("movz x0, #3
bl scc_rt_abort")) /- scc_rt_stack_take_23 -/]⟩,
  ⟨".L6_scc_rt_stack_take.halt37", [(0, parseAArch64("b .L6_scc_rt_stack_take.halt37")) /- scc_rt_stack_take_24 -/]⟩,
  ⟨".L6_scc_rt_stack_take.9_ok", [(2, parseAArch64("str x9, [sp, #176]
ldr x9, [sp, #176]
ldr x10, [sp, #160]
add x9, x9, x10
str x9, [sp, #128]
b .L6_scc_rt_stack_take.10_taken")) /- scc_rt_stack_take_25 -/]⟩,
  ⟨".L6_scc_rt_stack_take.10_taken", [(0, parseAArch64("ldr x0, [sp, #128]
ldr x1, [sp]")) /- scc_rt_stack_take_26 -/]⟩,
  ⟨"scc_rt_take_site", [(1, parseAArch64("ldr x0, [sp, #128]
ldr x29, [sp, #192]
ldr x30, [sp, #200]
add sp, sp, #208
ret")) /- scc_rt_stack_take_27 -/]⟩
]

/-- The blocks of `scc_rt_stack_release`. -/
def hello1T_scc_rt_stack_release : List Grp := [
  ⟨"scc_rt_stack_release", [(0, parseAArch64("sub sp, sp, #160
str x29, [sp, #144]
str x30, [sp, #152]
add x29, sp, #144
str x0, [sp]
str x1, [sp, #8]")) /- scc_rt_stack_release_0 -/]⟩,
  ⟨".L7_scc_rt_stack_release.0_entry", [(0, parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]")) /- scc_rt_stack_release_1 -/]⟩,
  ⟨"scc_rt_release_site", [(1, parseAArch64("movz x9, #16384
str x9, [sp, #16]
movz x9, #0
str x9, [sp, #24]
movz x9, #32768
str x9, [sp, #32]
movz x9, #0
str x9, [sp, #40]
b .L7_scc_rt_stack_release.1_cls4")) /- scc_rt_stack_release_2 -/]⟩,
  ⟨".L7_scc_rt_stack_release.1_cls4", [(0, parseAArch64("ldr x9, [sp, #16]
ldr x10, [sp, #8]
subs xzr, x9, x10
b.lo .L7_scc_rt_stack_release.2_clsnext5")) /- scc_rt_stack_release_3 -/,
    (4, parseAArch64("b .L7_scc_rt_stack_release.3_clsdone6")) /- scc_rt_stack_release_4 -/]⟩,
  ⟨".L7_scc_rt_stack_release.2_clsnext5", [(0, parseAArch64("ldr x9, [sp, #32]
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
b .L7_scc_rt_stack_release.1_cls4")) /- scc_rt_stack_release_5 -/]⟩,
  ⟨".L7_scc_rt_stack_release.3_clsdone6", [(2, parseAArch64("str x9, [sp, #56]
ldr x9, [sp, #56]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #64]")) /- scc_rt_stack_release_6 -/,
    (9, parseAArch64("str x9, [sp, #72]
ldr x9, [sp, #72]
ldr x10, [sp, #24]
add x9, x9, x10
str x9, [sp, #80]")) /- scc_rt_stack_release_7 -/,
    (16, parseAArch64("str x9, [sp, #88]
b .L7_scc_rt_stack_release.4_spin13")) /- scc_rt_stack_release_8 -/]⟩,
  ⟨".L7_scc_rt_stack_release.4_spin13", [(0, parseAArch64("movz x9, #1
ldr x10, [sp, #88]")) /- scc_rt_stack_release_9 -/,
    (3, parseAArch64("str x11, [sp, #96]
ldr x9, [sp, #96]
movz x10, #0
subs xzr, x9, x10
b.eq .L7_scc_rt_stack_release.5_locked14")) /- scc_rt_stack_release_10 -/,
    (8, parseAArch64("b .L7_scc_rt_stack_release.4_spin13")) /- scc_rt_stack_release_11 -/]⟩,
  ⟨".L7_scc_rt_stack_release.5_locked14", [(0, parseAArch64("ldr x10, [sp, #64]")) /- scc_rt_stack_release_12 -/,
    (2, parseAArch64("str x9, [sp, #104]
ldr x9, [sp, #104]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #80]
ldr x10, [sp, #112]
add x9, x9, x10
str x9, [sp, #120]
ldr x9, [sp]
ldr x10, [sp, #120]")) /- scc_rt_stack_release_13 -/,
    (14, parseAArch64("ldr x9, [sp, #104]
movz x10, #1
add x9, x9, x10
str x9, [sp, #128]
ldr x9, [sp, #128]
ldr x10, [sp, #64]")) /- scc_rt_stack_release_14 -/,
    (23, parseAArch64("str x9, [sp, #136]
movz x9, #0
ldr x10, [sp, #136]")) /- scc_rt_stack_release_15 -/,
    (27, parseAArch64("ldr x29, [sp, #144]
ldr x30, [sp, #152]
add sp, sp, #160
ret")) /- scc_rt_stack_release_16 -/]⟩
]

/-- The blocks of `scc_rt_grow`. -/
def hello1T_scc_rt_grow : List Grp := [
  ⟨"scc_rt_grow", [(0, parseAArch64("sub sp, sp, #368
str x29, [sp, #352]
str x30, [sp, #360]
add x29, sp, #352
str x0, [sp]
str x1, [sp, #8]")) /- scc_rt_grow_0 -/]⟩,
  ⟨".L8_scc_rt_grow.0_entry", [(0, parseAArch64("mrs x9, tpidr_el0
str x9, [sp, #16]
ldr x10, [sp, #16]")) /- scc_rt_grow_1 -/,
    (4, parseAArch64("str x9, [sp, #24]
ldr x10, [sp, #16]")) /- scc_rt_grow_2 -/,
    (7, parseAArch64("str x9, [sp, #32]
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
b .L8_scc_rt_grow.1_dbl")) /- scc_rt_grow_3 -/]⟩,
  ⟨".L8_scc_rt_grow.1_dbl", [(0, parseAArch64("ldr x9, [sp, #72]
ldr x10, [sp, #64]
subs xzr, x9, x10
b.lo .L8_scc_rt_grow.2_dbl2")) /- scc_rt_grow_4 -/,
    (4, parseAArch64("b .L8_scc_rt_grow.3_cap")) /- scc_rt_grow_5 -/]⟩,
  ⟨".L8_scc_rt_grow.2_dbl2", [(0, parseAArch64("ldr x9, [sp, #72]
movz x10, #1
lslv x9, x9, x10
str x9, [sp, #72]
b .L8_scc_rt_grow.1_dbl")) /- scc_rt_grow_6 -/]⟩,
  ⟨".L8_scc_rt_grow.3_cap", [(0, parseAArch64("ldr x9, [sp, #72]
movz x10, #1024, lsl #16
subs xzr, x9, x10
b.hi .L8_scc_rt_grow.4_full")) /- scc_rt_grow_7 -/,
    (4, parseAArch64("b .L8_scc_rt_grow.5_take")) /- scc_rt_grow_8 -/]⟩,
  ⟨".L8_scc_rt_grow.4_full", [(0, parseAArch64("movz x0, #3
bl scc_rt_abort")) /- scc_rt_grow_9 -/]⟩,
  ⟨".L8_scc_rt_grow.halt14", [(0, parseAArch64("b .L8_scc_rt_grow.halt14")) /- scc_rt_grow_10 -/]⟩,
  ⟨".L8_scc_rt_grow.5_take", [(0, parseAArch64("ldr x0, [sp, #72]
bl scc_rt_stack_take")) /- scc_rt_grow_11 -/]⟩,
  ⟨".L8_scc_rt_grow.sp15", [(0, parseAArch64("str x0, [sp, #80]
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
b .L8_scc_rt_grow.6_copy")) /- scc_rt_grow_12 -/]⟩,
  ⟨".L8_scc_rt_grow.6_copy", [(0, parseAArch64("ldr x9, [sp, #104]
ldr x10, [sp, #32]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.8_walk0")) /- scc_rt_grow_13 -/,
    (4, parseAArch64("b .L8_scc_rt_grow.7_copy1")) /- scc_rt_grow_14 -/]⟩,
  ⟨".L8_scc_rt_grow.7_copy1", [(0, parseAArch64("ldr x10, [sp, #104]")) /- scc_rt_grow_15 -/,
    (2, parseAArch64("str x9, [sp, #112]
ldr x9, [sp, #104]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #120]
ldr x9, [sp, #112]
ldr x10, [sp, #120]")) /- scc_rt_grow_16 -/,
    (10, parseAArch64("ldr x9, [sp, #104]
movz x10, #8
add x9, x9, x10
str x9, [sp, #104]
b .L8_scc_rt_grow.6_copy")) /- scc_rt_grow_17 -/]⟩,
  ⟨".L8_scc_rt_grow.8_walk0", [(0, parseAArch64("ldr x9, [sp]
str x9, [sp, #128]")) /- scc_rt_grow_18 -/,
    (4, parseAArch64("str x9, [sp, #136]
ldr x10, [sp, #136]")) /- scc_rt_grow_19 -/,
    (7, parseAArch64("str x9, [sp, #144]
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
b .L8_scc_rt_grow.9_walk")) /- scc_rt_grow_20 -/]⟩,
  ⟨".L8_scc_rt_grow.9_walk", [(0, parseAArch64("ldr x10, [sp, #128]")) /- scc_rt_grow_21 -/,
    (2, parseAArch64("str x9, [sp, #176]
ldr x9, [sp, #176]
ldr x10, [sp, #24]
subs xzr, x9, x10
b.lo .L8_scc_rt_grow.24_done")) /- scc_rt_grow_22 -/,
    (7, parseAArch64("b .L8_scc_rt_grow.10_walk1")) /- scc_rt_grow_23 -/]⟩,
  ⟨".L8_scc_rt_grow.10_walk1", [(0, parseAArch64("ldr x9, [sp, #176]
ldr x10, [sp, #32]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.24_done")) /- scc_rt_grow_24 -/,
    (4, parseAArch64("b .L8_scc_rt_grow.11_walk2")) /- scc_rt_grow_25 -/]⟩,
  ⟨".L8_scc_rt_grow.11_walk2", [(0, parseAArch64("ldr x9, [sp, #128]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #184]
ldr x9, [sp, #176]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #192]
ldr x9, [sp, #192]
ldr x10, [sp, #184]")) /- scc_rt_grow_26 -/,
    (11, parseAArch64("ldr x10, [sp, #128]")) /- scc_rt_grow_27 -/,
    (13, parseAArch64("str x9, [sp, #200]
movz x9, #0
str x9, [sp, #208]
ldr x9, [sp, #144]
str x9, [sp, #216]
b .L8_scc_rt_grow.12_bs")) /- scc_rt_grow_28 -/]⟩,
  ⟨".L8_scc_rt_grow.12_bs", [(0, parseAArch64("ldr x9, [sp, #208]
ldr x10, [sp, #216]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.23_next")) /- scc_rt_grow_29 -/,
    (4, parseAArch64("b .L8_scc_rt_grow.13_bs1")) /- scc_rt_grow_30 -/]⟩,
  ⟨".L8_scc_rt_grow.13_bs1", [(0, parseAArch64("ldr x9, [sp, #208]
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
ldr x10, [sp, #248]")) /- scc_rt_grow_31 -/,
    (22, parseAArch64("str x9, [sp, #256]
ldr x9, [sp, #256]
ldr x10, [sp, #200]
subs xzr, x9, x10
b.eq .L8_scc_rt_grow.17_found")) /- scc_rt_grow_32 -/,
    (27, parseAArch64("b .L8_scc_rt_grow.14_bs2")) /- scc_rt_grow_33 -/]⟩,
  ⟨".L8_scc_rt_grow.14_bs2", [(0, parseAArch64("ldr x9, [sp, #256]
ldr x10, [sp, #200]
subs xzr, x9, x10
b.lo .L8_scc_rt_grow.15_bslo")) /- scc_rt_grow_34 -/,
    (4, parseAArch64("b .L8_scc_rt_grow.16_bshi")) /- scc_rt_grow_35 -/]⟩,
  ⟨".L8_scc_rt_grow.15_bslo", [(0, parseAArch64("ldr x9, [sp, #232]
movz x10, #1
add x9, x9, x10
str x9, [sp, #208]
b .L8_scc_rt_grow.12_bs")) /- scc_rt_grow_36 -/]⟩,
  ⟨".L8_scc_rt_grow.16_bshi", [(0, parseAArch64("ldr x9, [sp, #232]
str x9, [sp, #216]
b .L8_scc_rt_grow.12_bs")) /- scc_rt_grow_37 -/]⟩,
  ⟨".L8_scc_rt_grow.17_found", [(0, parseAArch64("ldr x10, [sp, #248]")) /- scc_rt_grow_38 -/,
    (2, parseAArch64("str x9, [sp, #264]
ldr x10, [sp, #248]")) /- scc_rt_grow_39 -/,
    (5, parseAArch64("str x9, [sp, #272]
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
b .L8_scc_rt_grow.18_fix")) /- scc_rt_grow_40 -/]⟩,
  ⟨".L8_scc_rt_grow.18_fix", [(0, parseAArch64("ldr x9, [sp, #288]
ldr x10, [sp, #264]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.23_next")) /- scc_rt_grow_41 -/,
    (4, parseAArch64("b .L8_scc_rt_grow.19_fix1")) /- scc_rt_grow_42 -/]⟩,
  ⟨".L8_scc_rt_grow.19_fix1", [(0, parseAArch64("ldr x10, [sp, #280]")) /- scc_rt_grow_43 -/,
    (2, parseAArch64("str x9, [sp, #296]
ldr x9, [sp, #176]
ldr x10, [sp, #296]
add x9, x9, x10
str x9, [sp, #304]
ldr x10, [sp, #304]")) /- scc_rt_grow_44 -/,
    (9, parseAArch64("str x9, [sp, #312]
ldr x9, [sp, #312]
ldr x10, [sp, #24]
subs xzr, x9, x10
b.lo .L8_scc_rt_grow.22_skip")) /- scc_rt_grow_45 -/,
    (14, parseAArch64("b .L8_scc_rt_grow.20_fix2")) /- scc_rt_grow_46 -/]⟩,
  ⟨".L8_scc_rt_grow.20_fix2", [(0, parseAArch64("ldr x9, [sp, #312]
ldr x10, [sp, #32]
subs xzr, x9, x10
b.hs .L8_scc_rt_grow.22_skip")) /- scc_rt_grow_47 -/,
    (4, parseAArch64("b .L8_scc_rt_grow.21_fix3")) /- scc_rt_grow_48 -/]⟩,
  ⟨".L8_scc_rt_grow.21_fix3", [(0, parseAArch64("ldr x9, [sp, #304]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #320]
ldr x9, [sp, #312]
ldr x10, [sp, #96]
add x9, x9, x10
str x9, [sp, #328]
ldr x9, [sp, #328]
ldr x10, [sp, #320]")) /- scc_rt_grow_49 -/,
    (11, parseAArch64("b .L8_scc_rt_grow.22_skip")) /- scc_rt_grow_50 -/]⟩,
  ⟨".L8_scc_rt_grow.22_skip", [(0, parseAArch64("ldr x9, [sp, #288]
movz x10, #1
add x9, x9, x10
str x9, [sp, #288]
ldr x9, [sp, #280]
movz x10, #8
add x9, x9, x10
str x9, [sp, #280]
b .L8_scc_rt_grow.18_fix")) /- scc_rt_grow_51 -/]⟩,
  ⟨".L8_scc_rt_grow.23_next", [(0, parseAArch64("ldr x9, [sp, #176]
str x9, [sp, #128]
b .L8_scc_rt_grow.9_walk")) /- scc_rt_grow_52 -/]⟩,
  ⟨".L8_scc_rt_grow.24_done", [(0, parseAArch64("ldr x9, [sp, #80]
ldr x10, [sp, #16]")) /- scc_rt_grow_53 -/,
    (3, parseAArch64("ldr x9, [sp, #88]
ldr x10, [sp, #16]")) /- scc_rt_grow_54 -/,
    (6, parseAArch64("ldr x9, [sp, #80]
movz x10, #4096
add x9, x9, x10
str x9, [sp, #336]
ldr x9, [sp, #336]
ldr x10, [sp, #16]")) /- scc_rt_grow_55 -/,
    (13, parseAArch64("ldr x0, [sp, #96]
ldr x1, [sp, #24]
ldr x2, [sp, #40]
ldr x29, [sp, #352]
ldr x30, [sp, #360]
add sp, sp, #368
ret")) /- scc_rt_grow_56 -/]⟩
]

/-- The blocks of `scc_rt_print`. -/
def hello1T_scc_rt_print : List Grp := [
  ⟨"scc_rt_print", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]
str x1, [sp, #8]")) /- scc_rt_print_0 -/]⟩,
  ⟨".L9_scc_rt_print.0_entry", [(0, parseAArch64("b .L9_scc_rt_print.1_loop")) /- scc_rt_print_1 -/]⟩,
  ⟨".L9_scc_rt_print.1_loop", [(0, parseAArch64("ldr x9, [sp, #8]
movz x10, #0
subs xzr, x9, x10
b.eq .L9_scc_rt_print.7_done")) /- scc_rt_print_2 -/,
    (4, parseAArch64("b .L9_scc_rt_print.2_write")) /- scc_rt_print_3 -/]⟩,
  ⟨".L9_scc_rt_print.2_write", [(1, parseAArch64("movz x0, #1
ldr x1, [sp]
ldr x2, [sp, #8]
movz x8, #64")) /- scc_rt_print_4 -/,
    (6, parseAArch64("str x0, [sp, #16]
ldr x9, [sp, #16]
movz x10, #65532
movk x10, #65535, lsl #16
movk x10, #65535, lsl #32
movk x10, #65535, lsl #48
subs xzr, x9, x10
b.eq .L9_scc_rt_print.1_loop")) /- scc_rt_print_5 -/,
    (14, parseAArch64("b .L9_scc_rt_print.3_chk2")) /- scc_rt_print_6 -/]⟩,
  ⟨".L9_scc_rt_print.3_chk2", [(0, parseAArch64("ldr x9, [sp, #16]
movz x10, #65525
movk x10, #65535, lsl #16
movk x10, #65535, lsl #32
movk x10, #65535, lsl #48
subs xzr, x9, x10
b.eq .L9_scc_rt_print.1_loop")) /- scc_rt_print_7 -/,
    (7, parseAArch64("b .L9_scc_rt_print.4_chk3")) /- scc_rt_print_8 -/]⟩,
  ⟨".L9_scc_rt_print.4_chk3", [(0, parseAArch64("ldr x9, [sp, #16]
movz x10, #0
subs xzr, x9, x10
b.le .L9_scc_rt_print.6_fail")) /- scc_rt_print_9 -/,
    (4, parseAArch64("b .L9_scc_rt_print.5_adv")) /- scc_rt_print_10 -/]⟩,
  ⟨".L9_scc_rt_print.5_adv", [(0, parseAArch64("ldr x9, [sp]
ldr x10, [sp, #16]
add x9, x9, x10
str x9, [sp]
ldr x9, [sp, #8]
ldr x10, [sp, #16]
sub x9, x9, x10
str x9, [sp, #8]
b .L9_scc_rt_print.1_loop")) /- scc_rt_print_11 -/]⟩,
  ⟨".L9_scc_rt_print.6_fail", [(0, parseAArch64("movz x0, #4
bl scc_rt_abort")) /- scc_rt_print_12 -/]⟩,
  ⟨".L9_scc_rt_print.halt11", [(0, parseAArch64("b .L9_scc_rt_print.halt11")) /- scc_rt_print_13 -/]⟩,
  ⟨".L9_scc_rt_print.7_done", [(0, parseAArch64("ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")) /- scc_rt_print_14 -/]⟩
]

/-- The blocks of `scc_rt_park`. -/
def hello1T_scc_rt_park : List Grp := [
  ⟨"scc_rt_park", [(0, parseAArch64("sub sp, sp, #64
str x29, [sp, #48]
str x30, [sp, #56]
add x29, sp, #48")) /- scc_rt_park_0 -/]⟩,
  ⟨".L10_scc_rt_park.0_entry", [(0, parseAArch64("mrs x9, tpidr_el0
str x9, [sp]
movz x9, #0
ldr x10, [sp]
add x10, x10, #16")) /- scc_rt_park_1 -/,
    (6, parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
subs xzr, x9, x10
b.eq .L10_scc_rt_park.2_done")) /- scc_rt_park_2 -/,
    (11, parseAArch64("b .L10_scc_rt_park.1_wait")) /- scc_rt_park_3 -/]⟩,
  ⟨".L10_scc_rt_park.1_wait", [(0, parseAArch64("ldr x9, [sp]
movz x10, #16
add x9, x9, x10
str x9, [sp, #16]
ldr x0, [sp, #16]
movz x1, #128
movz x2, #0
movz x3, #0
movz x4, #0
movz x5, #0
movz x8, #98")) /- scc_rt_park_4 -/,
    (12, parseAArch64("str x0, [sp, #24]
movz x9, #0
ldr x10, [sp]
add x10, x10, #16")) /- scc_rt_park_5 -/,
    (17, parseAArch64("str x11, [sp, #32]
ldr x29, [sp, #48]
ldr x30, [sp, #56]
add sp, sp, #64
ret")) /- scc_rt_park_6 -/]⟩,
  ⟨".L10_scc_rt_park.2_done", [(0, parseAArch64("ldr x29, [sp, #48]
ldr x30, [sp, #56]
add sp, sp, #64
ret")) /- scc_rt_park_7 -/]⟩
]

/-- The blocks of `scc_rt_unpark`. -/
def hello1T_scc_rt_unpark : List Grp := [
  ⟨"scc_rt_unpark", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]")) /- scc_rt_unpark_0 -/]⟩,
  ⟨".L11_scc_rt_unpark.0_entry", [(0, parseAArch64("movz x9, #1
ldr x10, [sp]
add x10, x10, #16")) /- scc_rt_unpark_1 -/,
    (4, parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #0
subs xzr, x9, x10
b.eq .L11_scc_rt_unpark.1_wake")) /- scc_rt_unpark_2 -/,
    (9, parseAArch64("b .L11_scc_rt_unpark.2_done")) /- scc_rt_unpark_3 -/]⟩,
  ⟨".L11_scc_rt_unpark.1_wake", [(0, parseAArch64("ldr x9, [sp]
movz x10, #16
add x9, x9, x10
str x9, [sp, #16]
ldr x0, [sp, #16]
movz x1, #129
movz x2, #1
movz x3, #0
movz x4, #0
movz x5, #0
movz x8, #98")) /- scc_rt_unpark_4 -/,
    (12, parseAArch64("str x0, [sp, #24]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")) /- scc_rt_unpark_5 -/]⟩,
  ⟨".L11_scc_rt_unpark.2_done", [(0, parseAArch64("ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")) /- scc_rt_unpark_6 -/]⟩
]

/-- The blocks of `scc_rt_abort`. -/
def hello1T_scc_rt_abort : List Grp := [
  ⟨"scc_rt_abort", [(0, parseAArch64("sub sp, sp, #32
str x29, [sp, #16]
str x30, [sp, #24]
add x29, sp, #16
str x0, [sp]")) /- scc_rt_abort_0 -/]⟩,
  ⟨".L12_scc_rt_abort.0_entry", [(0, parseAArch64("ldr x9, [sp]
movz x10, #1
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.1_is0")) /- scc_rt_abort_1 -/,
    (4, parseAArch64("b .L12_scc_rt_abort.2_next1")) /- scc_rt_abort_2 -/]⟩,
  ⟨".L12_scc_rt_abort.1_is0", [(0, parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_overflow")) /- scc_rt_abort_3 -/]⟩,
  ⟨".L12_scc_rt_abort.2_next1", [(0, parseAArch64("ldr x9, [sp]
movz x10, #2
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.3_is2")) /- scc_rt_abort_4 -/,
    (4, parseAArch64("b .L12_scc_rt_abort.4_next3")) /- scc_rt_abort_5 -/]⟩,
  ⟨".L12_scc_rt_abort.3_is2", [(0, parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_heap")) /- scc_rt_abort_6 -/]⟩,
  ⟨".L12_scc_rt_abort.4_next3", [(0, parseAArch64("ldr x9, [sp]
movz x10, #3
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.5_is4")) /- scc_rt_abort_7 -/,
    (4, parseAArch64("b .L12_scc_rt_abort.6_next5")) /- scc_rt_abort_8 -/]⟩,
  ⟨".L12_scc_rt_abort.5_is4", [(0, parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_stack")) /- scc_rt_abort_9 -/]⟩,
  ⟨".L12_scc_rt_abort.6_next5", [(0, parseAArch64("ldr x9, [sp]
movz x10, #4
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.7_is6")) /- scc_rt_abort_10 -/,
    (4, parseAArch64("b .L12_scc_rt_abort.8_next7")) /- scc_rt_abort_11 -/]⟩,
  ⟨".L12_scc_rt_abort.7_is6", [(0, parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_write")) /- scc_rt_abort_12 -/]⟩,
  ⟨".L12_scc_rt_abort.8_next7", [(0, parseAArch64("ldr x9, [sp]
movz x10, #5
subs xzr, x9, x10
b.eq .L12_scc_rt_abort.9_is8")) /- scc_rt_abort_13 -/,
    (4, parseAArch64("b .L12_scc_rt_abort.10_next9")) /- scc_rt_abort_14 -/]⟩,
  ⟨".L12_scc_rt_abort.9_is8", [(0, parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
b scc_rt_abort_threads")) /- scc_rt_abort_15 -/]⟩,
  ⟨".L12_scc_rt_abort.halt10", [(0, parseAArch64("b .L12_scc_rt_abort.halt10")) /- scc_rt_abort_16 -/]⟩
]

/-- The blocks of `scc_rt_abort_overflow`. -/
def hello1T_scc_rt_abort_overflow : List Grp := [
  ⟨"scc_rt_abort_overflow", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")) /- scc_rt_abort_overflow_0 -/]⟩,
  ⟨".L13_scc_rt_abort_overflow.0_entry", [(2, parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #34
movz x8, #64")) /- scc_rt_abort_overflow_1 -/,
    (8, parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")) /- scc_rt_abort_overflow_2 -/]⟩,
  ⟨"scc_rt_abort_overflow_exit", [(1, parseAArch64("str x0, [sp, #16]")) /- scc_rt_abort_overflow_3 -/]⟩,
  ⟨".L13_scc_rt_abort_overflow.halt3", [(0, parseAArch64("b .L13_scc_rt_abort_overflow.halt3")) /- scc_rt_abort_overflow_4 -/]⟩
]

/-- The blocks of `scc_rt_abort_heap`. -/
def hello1T_scc_rt_abort_heap : List Grp := [
  ⟨"scc_rt_abort_heap", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")) /- scc_rt_abort_heap_0 -/]⟩,
  ⟨".L14_scc_rt_abort_heap.0_entry", [(2, parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #35
movz x8, #64")) /- scc_rt_abort_heap_1 -/,
    (8, parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")) /- scc_rt_abort_heap_2 -/]⟩,
  ⟨"scc_rt_abort_heap_exit", [(1, parseAArch64("str x0, [sp, #16]")) /- scc_rt_abort_heap_3 -/]⟩,
  ⟨".L14_scc_rt_abort_heap.halt3", [(0, parseAArch64("b .L14_scc_rt_abort_heap.halt3")) /- scc_rt_abort_heap_4 -/]⟩
]

/-- The blocks of `scc_rt_abort_stack`. -/
def hello1T_scc_rt_abort_stack : List Grp := [
  ⟨"scc_rt_abort_stack", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")) /- scc_rt_abort_stack_0 -/]⟩,
  ⟨".L15_scc_rt_abort_stack.0_entry", [(2, parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #25
movz x8, #64")) /- scc_rt_abort_stack_1 -/,
    (8, parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")) /- scc_rt_abort_stack_2 -/]⟩,
  ⟨"scc_rt_abort_stack_exit", [(1, parseAArch64("str x0, [sp, #16]")) /- scc_rt_abort_stack_3 -/]⟩,
  ⟨".L15_scc_rt_abort_stack.halt3", [(0, parseAArch64("b .L15_scc_rt_abort_stack.halt3")) /- scc_rt_abort_stack_4 -/]⟩
]

/-- The blocks of `scc_rt_abort_write`. -/
def hello1T_scc_rt_abort_write : List Grp := [
  ⟨"scc_rt_abort_write", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")) /- scc_rt_abort_write_0 -/]⟩,
  ⟨".L16_scc_rt_abort_write.0_entry", [(2, parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #44
movz x8, #64")) /- scc_rt_abort_write_1 -/,
    (8, parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")) /- scc_rt_abort_write_2 -/]⟩,
  ⟨"scc_rt_abort_write_exit", [(1, parseAArch64("str x0, [sp, #16]")) /- scc_rt_abort_write_3 -/]⟩,
  ⟨".L16_scc_rt_abort_write.halt3", [(0, parseAArch64("b .L16_scc_rt_abort_write.halt3")) /- scc_rt_abort_write_4 -/]⟩
]

/-- The blocks of `scc_rt_abort_threads`. -/
def hello1T_scc_rt_abort_threads : List Grp := [
  ⟨"scc_rt_abort_threads", [(0, parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")) /- scc_rt_abort_threads_0 -/]⟩,
  ⟨".L17_scc_rt_abort_threads.0_entry", [(2, parseAArch64("str x9, [sp]
movz x0, #2
ldr x1, [sp]
movz x2, #35
movz x8, #64")) /- scc_rt_abort_threads_1 -/,
    (8, parseAArch64("str x0, [sp, #8]
movz x0, #101
movz x8, #94")) /- scc_rt_abort_threads_2 -/]⟩,
  ⟨"scc_rt_abort_threads_exit", [(1, parseAArch64("str x0, [sp, #16]")) /- scc_rt_abort_threads_3 -/]⟩,
  ⟨".L17_scc_rt_abort_threads.halt3", [(0, parseAArch64("b .L17_scc_rt_abort_threads.halt3")) /- scc_rt_abort_threads_4 -/]⟩
]

/-- The blocks of `wc_rodata`. -/
def hello1T_wc_rodata : List Grp := [
  ⟨".L18_wc_rodata.stack_check", [(0, parseAArch64("sub x9, sp, #48
mrs x10, tpidr_el0")) /- wc_rodata_0 -/,
    (3, parseAArch64("subs xzr, x9, x10
b.lo .L18_wc_rodata.stack_grow")) /- wc_rodata_1 -/,
    (5, parseAArch64("add sp, x9, #0
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")) /- wc_rodata_2 -/]⟩,
  ⟨".L18_wc_rodata.0_entry", [(0, parseAArch64("movz x0, #257
movz x1, #2
movz x2, #3
bl scc_rt_alloc")) /- wc_rodata_3 -/]⟩,
  ⟨".L18_wc_rodata.sp0", [(0, parseAArch64("str x0, [sp]
ldr x10, [sp]")) /- wc_rodata_4 -/,
    (3, parseAArch64("str x9, [sp, #8]
movz x9, #25928
movk x9, #27756, lsl #16
movk x9, #11375, lsl #32
movk x9, #30496, lsl #48
ldr x10, [sp]")) /- wc_rodata_5 -/,
    (10, parseAArch64("ldr x10, [sp]")) /- wc_rodata_6 -/,
    (12, parseAArch64("str x9, [sp, #16]
movz x9, #29295
movk x9, #25708, lsl #16
movk x9, #10, lsl #32
ldr x10, [sp]")) /- wc_rodata_7 -/,
    (18, parseAArch64("ldr x0, [sp]
movz x1, #0
movz x2, #2
movz x3, #13
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")) /- wc_rodata_8 -/]⟩,
  ⟨".L18_wc_rodata.stack_grow", [(0, parseAArch64("sub sp, sp, #80
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
bl scc_rt_morestack")) /- wc_rodata_9 -/]⟩,
  ⟨".L18_wc_rodata.sp_check", [(0, parseAArch64("ldr x0, [sp]
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
b .L18_wc_rodata.stack_check")) /- wc_rodata_10 -/]⟩
]

/-- The blocks of `wc_main`. -/
def hello1T_wc_main : List Grp := [
  ⟨".L19_wc_main.stack_check", [(0, parseAArch64("sub x9, sp, #96
mrs x10, tpidr_el0")) /- wc_main_0 -/,
    (3, parseAArch64("subs xzr, x9, x10
b.lo .L19_wc_main.stack_grow")) /- wc_main_1 -/,
    (5, parseAArch64("add sp, x9, #0
str x29, [sp, #80]
str x30, [sp, #88]
add x29, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]")) /- wc_main_2 -/]⟩,
  ⟨".L19_wc_main.0_entry", [(0, parseAArch64("ldr x9, [sp, #8]
ubfm x9, x9, #0, #31
str x9, [sp, #40]
ldr x9, [sp]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #16]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #56]
ldr x9, [sp, #24]
ldr x10, [sp, #56]
subs xzr, x9, x10
ldr x11, [sp, #24]
ldr x12, [sp, #56]
csel x9, x11, x12, lo
str x9, [sp, #64]
ldr x0, [sp, #48]
ldr x1, [sp, #64]
bl scc_rt_print")) /- wc_main_3 -/]⟩,
  ⟨".L19_wc_main.sp4", [(0, parseAArch64("movz x0, #0
ldr x29, [sp, #80]
ldr x30, [sp, #88]
add sp, sp, #96
ret")) /- wc_main_4 -/]⟩,
  ⟨".L19_wc_main.stack_grow", [(0, parseAArch64("sub sp, sp, #80
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
bl scc_rt_morestack")) /- wc_main_5 -/]⟩,
  ⟨".L19_wc_main.sp_check", [(0, parseAArch64("ldr x0, [sp]
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
b .L19_wc_main.stack_check")) /- wc_main_6 -/]⟩
]

/-- The blocks of `scc_rt_morestack`. -/
def hello1T_scc_rt_morestack : List Grp := [
  ⟨"scc_rt_morestack", [(0, parseAArch64("sub sp, sp, #16
str x29, [sp]
str x30, [sp, #8]
add x29, sp, #0
orr x1, xzr, x0
orr x0, xzr, x29
bl scc_rt_grow")) /- scc_rt_morestack_0 -/,
    (7, parseAArch64("add x29, x29, x0")) /- scc_rt_morestack_1 -/,
    (9, parseAArch64("orr x0, xzr, x1
orr x1, xzr, x2
bl scc_rt_stack_release")) /- scc_rt_morestack_2 -/,
    (12, parseAArch64("ldr x29, [sp]
ldr x30, [sp, #8]
add sp, sp, #16
ret")) /- scc_rt_morestack_3 -/]⟩
]

/-- All the blocks of the program. -/
def hello1T : List Grp :=
  hello1T_start ++
  hello1T_scc_rt_start ++
  hello1T_scc_rt_main ++
  hello1T_scc_rt_alloc ++
  hello1T_scc_rt_alloc_tcb ++
  hello1T_scc_rt_thread_reserve ++
  hello1T_scc_rt_thread_init ++
  hello1T_scc_rt_stack_take ++
  hello1T_scc_rt_stack_release ++
  hello1T_scc_rt_grow ++
  hello1T_scc_rt_print ++
  hello1T_scc_rt_park ++
  hello1T_scc_rt_unpark ++
  hello1T_scc_rt_abort ++
  hello1T_scc_rt_abort_overflow ++
  hello1T_scc_rt_abort_heap ++
  hello1T_scc_rt_abort_stack ++
  hello1T_scc_rt_abort_write ++
  hello1T_scc_rt_abort_threads ++
  hello1T_wc_rodata ++
  hello1T_wc_main ++
  hello1T_scc_rt_morestack

theorem hello1T_in : blocksIn hello1Prog hello1T := by kernel_rfl

/-- A block of the table is code at its place. -/
example {exe : Executable} [Executable.ValidLayout exe] (hp : Lays exe hello1Prog) {st : State}
    (he : st.exe = exe) (hend : st.endPc = endOf exe hello1Prog) :
    Spike.Lib.A64.CodeAt st ((_root_.Executable.labels exe).label "_start" + Int64.ofNat (4 * 0))
      (parseAArch64("b scc_rt_start")) :=
  codeAt_of_blocksIn (g := ⟨"_start", [(0, parseAArch64("b scc_rt_start"))]⟩) hp he hend hello1T_in
    (by unfold hello1T; (repeat refine List.mem_append_left _ ?_); exact List.mem_singleton_self _)
    (List.mem_singleton_self _)

end Scc.Test.RtA64BlocksHello1
