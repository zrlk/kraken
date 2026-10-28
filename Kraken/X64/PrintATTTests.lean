module

/-
  Round-trip tests for the AT&T printer: `parse (toATT p) = .ok p` for programs
  `p` produced by `parse`.
-/

import Kraken.X64.Parser
meta import Kraken.X64.Parser
import Kraken.X64.PrintATT
meta import Kraken.X64.PrintATT

open Kraken.X64 Kraken.X64.Parser

/-- `s` parses, and printing the result then re-parsing gives the same program. -/
def roundtrips (s : String) : Bool :=
  match parse s with
  | .ok p => match parse (toATT p) with
    | .ok p' => p' == p
    | .error _ => false
  | .error _ => false

/-- One line per `Operation`/`AvxOperation` constructor and operand form. -/
def corpus : List String := [
  -- data movement, all widths and operand kinds
  "movq $42, %rax", "movl $-1, %r9d", "movw %ax, %r15w", "movb %ah, %sil",
  "movabsq $0xFFFFFFFFFFFFFFFF, %rdx", "movq $-9223372036854775808, %rdx",
  "movq sym, %rax", "movq $sym+8, %rax", "movq sym-4(%rax), %rcx", "addq 16, %rax", "pushq sym",
  "movq 8(%rsp), %rax", "movq %rax, -16(%rbp,%rcx,8)",
  "movb $1, (%eax)", "movl %eax, 4(%r8d,%r9d,2)", "movq (%rax,%rbx), %rcx",
  "movq 8(%rip), %rax", "movsx %al, %ecx", "movzx %bx, %rdx", "movsbq %al, %rax",
  "movzwl %cx, %edx", "movsbl (%rsp), %ecx", "movzwq 8(%rax), %rdx", "movslq (%rax), %rbx",
  "movsxd %eax, %rbx", "pushq %rbx", "pushq $7", "pushw (%rsp)", "popq %rax", "popq 8(%rsp)",
  "sete %al", "setnz 3(%rsp)", "setb %dh", "setae %bl", "seta %cl", "setbe %al",
  "setl %al", "setle %al", "seto %al", "setno %al", "sets %al", "setns %al",
  "setp %al", "setnp %al", "setge %al", "setg %al",
  "cmovz %rax, %rbx", "cmovl (%rsp), %ecx", "cmovge %rax, %rbx", "cmovg (%rsp), %ecx",
  -- arithmetic
  "leaq 8(%rax,%rbx,4), %rcx", "leal (%eax), %ecx", "lea sym(%rip), %rax",
  "addq $1, %rax", "addb %al, (%rsp)", "adcl (%rsp), %eax", "adcx %rax, %rbx",
  "adox (%rsp), %ecx", "incq %rax", "incb (%rsp)", "decw %ax", "negl %eax",
  "subq %rax, %rbx", "sbbb $1, %al", "cmpq $0, (%rsp)", "cmpl %eax, %ebx",
  "mulq %rbx", "mulb (%rsp)", "mulx %rax, %rbx, %rcx", "mulxl (%rsp), %eax, %ebx",
  "imulq %rbx", "imulw %ax, %bx", "imulq (%rsp), %rbx", "imulq $3, %rax, %rbx",
  "imull $-3, (%rsp), %eax",
  -- bitwise
  "testq $1, %rax", "testb %al, (%rsp)", "andq %rax, %rbx", "notq %rax",
  "orw $5, %ax", "xorl %eax, %eax",
  "shlq %rax", "shlq $3, %rax", "shlb %cl, (%rsp)", "salq $1, %rax",
  "shrw $2, %ax", "sarl %cl, %eax", "shldq $4, %rax, %rbx", "shrd %cl, %ax, (%rsp)",
  "rolq $1, %rax", "rorb %cl, %al", "rclq $1, %rax", "rcrl %cl, (%rsp)",
  "bswap %eax", "bswapq %rax",
  -- control flow
  "foo:\n  jmp foo", "je foo", "jne .L1", "jb foo", "jae foo", "ja foo", "jbe foo",
  "jl foo", "jle foo", "call foo", "call %rax", "jmp %rax",
  "jmp 8(%rax)", "call (%rsp)", "jmp *%rax", "jmp *8(%rdi)", "call *(%rsp)", "ret", "nop", "nop 5", ".align 16", ".align 16, 0x90",
  "a:\nb: ret\n\nc:",
  -- AVX
  "movups %xmm0, %xmm1", "vmovups (%rsp), %ymm2", "vmovups %zmm31, 64(%rsp)",
  "movaps %xmm3, %xmm4", "addps (%rax), %xmm5", "subps %xmm6, %xmm7",
  "mulps %xmm6, %xmm7", "mulps 16(%rsp), %xmm1", "xorps %xmm0, %xmm0", "xorps mask(%rip), %xmm2",
  -- a memory operand without a base, and a difference of labels
  "lea -0x40(,%ecx,4), %rcx", "movq 8(,%rax,8), %rbx", "a:\nb:\n  subq $b-a, %rcx",
  -- data
  ".byte 0, 0x80, 255", ".short 7", ".long -1", ".quad 0xFFFFFFFFFFFFFFFF", ".quad sym",
  ".quad sym+8", "a:\nb:\n  .long b-a", ".LJT:\n  .long .Lcase0 - .LJT\n  .long .Lcase1-.LJT", ".zero 4",
  ".space 0x10", "counter:\n  .zero 4"
]

/-- info: [] -/
#guard_msgs in
#eval corpus.filter (!roundtrips ·)

-- Data words keep their symbolic value.
#guard match parse ".LJT:\n  .long .Lcase0 - .LJT\n  .quad 5" with
  | .ok p => p == [.label ".LJT", .word .W32 (.sub (.label ".Lcase0") (.label ".LJT")),
      .word .W64 (.int64 5)]
  | .error _ => false

-- `.zero n` and `.space n` are `n` zero bytes; they print as `.byte`.
#guard match parse ".zero 3\n.space 2" with
  | .ok p => p == [.byteArray ⟨#[0, 0, 0]⟩, .byteArray ⟨#[0, 0]⟩]
  | .error _ => false
#guard match parse ".zero 0" with
  | .ok _ => false
  | .error _ => true

#guard ["cmove %ax, %bx", "cmovzl %eax, %ebx", "cmovnew %ax, %bx", "cmovnel %eax, %ebx", "cmovneq %rax, %rbx"].all roundtrips

-- Printed form is canonical AT&T.
#guard match parse "movq %rax, -16(%rbp,%rcx,8)\nfoo: imul $3, 8(%eax), %ebx\njne foo\nnop" with
  | .ok p => toATT p == "movq %rax, -16(%rbp,%rcx,8)\nfoo:\nimull $3, 8(%eax), %ebx\njne foo\nnop"
  | .error _ => false

-- Every program in the hardware test corpus round-trips.
#eval show IO Unit from do
  for f in ← System.FilePath.readDir "Kraken/X64/Test/asm" do
    if f.path.extension == some "S" then
      unless roundtrips (stripDirectives (← IO.FS.readFile f.path)) do
        throw <| .userError s!"{f.path} does not round-trip"
