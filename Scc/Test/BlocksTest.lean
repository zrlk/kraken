import Scc.Cert.Blocks

/-!
# Block data

`Scc.Cert.Blocks` on two small listings in the form scc writes, one per
architecture: a frame, a conditional branch whose target's offsets are the
meet of both edges, a call, a system call (`sys`: `exit_group`, its number
set in the same straight-line code), and stack switches, after which the
offsets restart at 0 in a region of their own (`switch`). x64 blocks carry
their instructions' sizes (here GNU `as`'s, `x64Sizes`) and every block its
address, the label before it plus a byte offset. `blocks.sh` runs
`scc --blocks` on every test program.
-/

namespace Scc.Test.Blocks
open Scc.Cert.Blocks

def x64Listing : String := "\t.text
\t.type f, @function
f:
\tpushq %rbp
\tmovq %rsp, %rbp
\tsubq $16, %rsp
\tmovq %rdi, -8(%rbp)
\tcmpq $0, %rdi
\tje .Lf.1
\tmovq -8(%rbp), %rax
\tcall g
.Lf.1:
\tleaq -16(%rbp), %rcx
\tmovq %rax, (%rcx)
\tmovl $231, %eax
\tsyscall
\tmovq %rdi, %rsp
\tpushq %rax
\tandq $-16, %rsp
\tpushq %rax
\tret
"

/-- The sizes GNU `as` gives `x64Listing`'s instructions, in text order. -/
def x64Sizes : List Nat := [1, 3, 4, 4, 4, 2, 4, 5, 4, 3, 5, 2, 3, 1, 4, 1, 1]

/--
info: -- f, listing lines 4–9, at f + 0
block_spec f_0 (-24) 16 ⟨8, []⟩ (parse("pushq %rbp
movq %rsp, %rbp
subq $16, %rsp
movq %rdi, -8(%rbp)
cmpq $0, %rdi
je .Lf.1")).zip [1, 3, 4, 4, 4, 2]

-- f, listing lines 10–11, at f + 18
block_spec f_1 (-24) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("movq -8(%rbp), %rax
call g")).zip [4, 5]

-- f, listing lines 13–15, at .Lf.1 + 0
block_spec f_2 (-24) 16 ⟨-16, [(.rbp, 0)]⟩ (parse("leaq -16(%rbp), %rcx
movq %rax, (%rcx)
movl $231, %eax")).zip [4, 3, 5]

-- f, listing lines 18–18, at .Lf.1 + 17
block_spec f_3 (-8) 0 ⟨0, []⟩ (parse("pushq %rax")).zip [1]

-- f, listing lines 20–21, at .Lf.1 + 22
block_spec f_4 (-8) 0 ⟨0, []⟩ (parse("pushq %rax
ret")).zip [1, 1]
-/
#guard_msgs in
#eval IO.println (blocks .x64 x64Listing x64Sizes)

/-- x64 block data needs the sizes, and as many as there are instructions. -/
example : blocks .x64 x64Listing = "error: x64 block data needs the instruction sizes" := by
  decide +kernel

/-- info: error: the size table ends before listing line 9 -/
#guard_msgs in
#eval IO.println (blocks .x64 x64Listing (x64Sizes.take 5))

/-- info: error: the size table has more entries than the listing has instructions -/
#guard_msgs in
#eval IO.println (blocks .x64 x64Listing (some (x64Sizes ++ [1])))

/-- The node counts of a listing. -/
def nodesOf (arch : Scc.Arch) (asm : String) : List (String × Nat) :=
  match analyse (isaOf arch) asm with
  | .ok r => r.nodes.toList
  | .error _ => []

/-- info: [("runtime: sys", 1), ("runtime: switch", 2)] -/
#guard_msgs in
#eval nodesOf .x64 x64Listing

def a64Listing : String := "\t.text
_start:
\tsub sp, sp, #32
\tstr x30, [sp, #24]
\tadd x9, sp, #8
\tcbz x0, .L1
\tldr x1, [sp, #8]
\tbl g
.L1:
\tmovz x8, #93
\tsvc #0
\tadd sp, x0, #0
\tstr x1, [sp]
\tret
"

/--
info: -- _start, listing lines 3–6, at _start + 0
block_spec _start_0 (-24) 0 ⟨0, []⟩ parseAArch64("sub sp, sp, #32
str x30, [sp, #24]
add x9, sp, #8
cbz x0, .L1")

-- _start, listing lines 7–8, at _start + 16
block_spec _start_1 (-24) 0 ⟨-32, [(.X9, -24)]⟩ parseAArch64("ldr x1, [sp, #8]
bl g")

-- _start, listing lines 10–10, at .L1 + 0
block_spec _start_2 (-24) 0 ⟨-32, []⟩ parseAArch64("movz x8, #93")

-- _start, listing lines 13–14, at .L1 + 12
block_spec _start_3 (0) 8 ⟨0, []⟩ parseAArch64("str x1, [sp]
ret")
-/
#guard_msgs in
#eval IO.println (blocks .arm a64Listing)

/-- info: [("runtime: sys", 1), ("runtime: switch", 1)] -/
#guard_msgs in
#eval nodesOf .arm a64Listing

/-- The code check tables of a listing (AArch64), for the program `pProg`. -/
def codeOf (asm : String) : String :=
  match analyse (isaOf .arm) asm >>= (renderCode · "p") with
  | .ok s => s
  | .error m => s!"error: {m}"

/--
info: /-- The blocks of `_start`. -/
def pT_start : List Grp := [
  ⟨"_start", [(0, parseAArch64("sub sp, sp, #32
str x30, [sp, #24]
add x9, sp, #8
cbz x0, .L1")) /- _start_0 -/,
    (4, parseAArch64("ldr x1, [sp, #8]
bl g")) /- _start_1 -/]⟩,
  ⟨".L1", [(0, parseAArch64("movz x8, #93")) /- _start_2 -/,
    (3, parseAArch64("str x1, [sp]
ret")) /- _start_3 -/]⟩
]

/-- All the blocks of the program. -/
def pT : List Grp :=
  pT_start

theorem pT_in : blocksIn pProg pT := by kernel_rfl
-/
#guard_msgs in
#eval IO.println (codeOf a64Listing)

/-- A directive between a label and a block: its offset would be wrong. -/
def a64Dir : String := "\t.text
_start:
\t.p2align 2
\tmovz x8, #93
"

/-- info: error: _start: an assembler directive between _start and listing line 4 -/
#guard_msgs in
#eval IO.println (codeOf a64Dir)

/-- A system call whose number is set before a label: its node must take
the number from the label's invariant. -/
def a64AfterLabel : String := "\t.text
_start:
\tmovz x8, #93
.L1:
\tsvc #0
"

/-- info: [("runtime: sys, number after a label", 1)] -/
#guard_msgs in
#eval nodesOf .arm a64AfterLabel

/-- The thread-pointer load (`fsld_nd`) and a `ud2` after a call that does
not return (`dead_nd`). -/
def x64Nodes : String := "\t.text
\t.type f, @function
f:
\tmovq %fs:-8, %rax
\tcall scc_rt_abort
\tud2
"

/-- info: [("runtime: thread pointer", 1), ("runtime: dead", 1)] -/
#guard_msgs in
#eval nodesOf .x64 x64Nodes

end Scc.Test.Blocks
