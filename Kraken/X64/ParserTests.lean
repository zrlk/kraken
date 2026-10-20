/-
  Parser Tests - Extracted from Parser.lean
  Uses #guard_msgs to verify parser output against expected results.
-/

import Kraken.X64.Parser
import Kraken.X64.PrintIntel

section Tests
open Kraken.X64.Parser

open Instr Operand Reg

-- Test: Simple instruction
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.add ↑(low Reg64.rbx Width.W64) ↑↑(low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("addq %rax, %rbx")

-- Test: Immediate operand
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑42))] : List Directive
-/
#guard_msgs in
#check parse("movq $42, %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.imm 42) }]

-- Test: Memory operand with displacement
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none, disp := ↑8 }))] : List Directive
-/
#guard_msgs in
#check parse("movq 8(%rsp), %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsp .none 1 8) }]

-- Test: Memory operand with index and scale
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mov ↑(low Reg64.rax Width.W64)
        ↑↑{ base := some (RegOrRip.reg Reg64.rsi),
              idx := some { reg := Reg64.r15, scale := Width.W64 } }))] : List Directive
-/
#guard_msgs in
#check parse("movq (%rsi, %r15, 8), %rax")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .mov (.Reg (.low .rax .W64)) (.mem .rsi (some .r15) 8 0) }]

-- Test: Labeled instruction
/--
info: [Directive.label "loop",
  Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rcx Width.W64) ↑↑1))] : List Directive
-/
#guard_msgs in
#check parse("loop: addq $1, %rcx")
-- Expected: [.Label "loop", .Instr { address_size := .W64, operation_size := .W64, operation := .add (.Reg (.low .rcx .W64)) (.imm 1) }]

-- Test: Conditional jump
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List Directive
-/
#guard_msgs in
#check parse("jnz loop")
-- Expected: [.Instr { address_size := .W64, operation_size := .W64, operation := .jcc .nz "loop" }]

-- Test: Multi-line program
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑0)), Directive.label "loop",
  Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑1)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.cmp ↑(low Reg64.rax Width.W64) ↑↑10)),
  Directive.instr (regular Width.W64 Width.W64 (Operation.jcc CondCode.nz "loop"))] : List Directive
-/
#guard_msgs in
#check parse("
  movq $0, %rax
loop:
  addq $1, %rax
  cmpq $10, %rax
  jne loop
")

-- Test: Negative immediate
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.add ↑(low Reg64.rax Width.W64) ↑↑(-1)))] : List Directive
-/
#guard_msgs in
#check parse("addq $-1, %rax")

-- Test: Hex immediate
/--
info: [Directive.instr (regular Width.W64 Width.W64 (Operation.mov ↑(low Reg64.rax Width.W64) ↑↑255))] : List Directive
-/
#guard_msgs in
#check parse("movq $0xff, %rax")

-- Test: mulx instruction
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.mulx (low Reg64.r10 Width.W64) (low Reg64.r9 Width.W64) ↑(low Reg64.r8 Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("mulxq %r8, %r9, %r10")

-- Test: xor for zeroing
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.xor ↑(low Reg64.rax Width.W64) ↑↑(low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("xorq %rax, %rax")

-- Test: lea with complex addressing
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rbp), idx := some { reg := Reg64.rcx, scale := Width.W32 },
          disp := ↑16 }))] : List Directive
-/
#guard_msgs in
#check parse("leaq 16(%rbp, %rcx, 4), %rax")

/--
info: [Directive.instr
    (regular Width.W32 Width.W64
      (Operation.lea (low Reg64.rax Width.W64)
        { base := some (RegOrRip.reg Reg64.rbp), idx := some { reg := Reg64.rcx, scale := Width.W32 },
          disp := ↑16 }))] : List Directive
-/
#guard_msgs in
#check parse("leaq 16(%ebp, %ecx, 4), %rax")

section atomics

-- The herd7 x86_64 litmus dialect: AT&T with `(sym)` absolute addresses.

/--
info: [Directive.instr
    (regular Width.W64 Width.W32 (Operation.mov ↑{ base := none, idx := none, disp := ↑"x" } ↑↑1))] : List Directive
-/
#guard_msgs in
#check parse("movl $1,(x)")

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.mov ↑(low Reg64.rax Width.W32) ↑↑{ base := none, idx := none, disp := ↑"y" }))] : List Directive
-/
#guard_msgs in
#check parse("movl (y),%eax")

/--
info: [Directive.instr (regular Width.W64 Width.W64 Operation.mfence),
  Directive.instr (regular Width.W64 Width.W64 Operation.lfence),
  Directive.instr (regular Width.W64 Width.W64 Operation.sfence)] : List Directive
-/
#guard_msgs in
#check parse("
  mfence
  lfence
  sfence
")

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.xchg (low Reg64.rax Width.W32) ↑{ base := none, idx := none, disp := ↑"x" }))] : List Directive
-/
#guard_msgs in
#check parse("xchgl %eax,(x)")

-- Either operand order; the register comes first in the AST.
/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.xchg (low Reg64.rax Width.W64)
        ↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("xchgq (%rsp), %rax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.xchg (low Reg64.rcx Width.W32) ↑(low Reg64.rbx Width.W32)))] : List Directive
-/
#guard_msgs in
#check parse("xchg %ecx, %ebx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.xadd true (↑{ base := none, idx := none, disp := ↑"x" }) (low Reg64.rax Width.W32)))] : List Directive
-/
#guard_msgs in
#check parse("lock xaddl %eax,(x)")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.xadd false (↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none })
        (low Reg64.rax Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("xaddq %rax, (%rsp)")

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.cmpxchg true (↑{ base := none, idx := none, disp := ↑"x" })
        (low Reg64.rbx Width.W32)))] : List Directive
-/
#guard_msgs in
#check parse("lock cmpxchgl %ebx,(x)")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.cmpxchg false (↑(low Reg64.rcx Width.W64)) (low Reg64.rbx Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("cmpxchg %rbx, %rcx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.lockBin LockBinOp.add { base := none, idx := none, disp := ↑"x" } ↑↑1))] : List Directive
-/
#guard_msgs in
#check parse("lock addl $1,(x)")

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lockBin LockBinOp.sub { base := some (RegOrRip.reg Reg64.rdi), idx := none }
        ↑↑(low Reg64.rax Width.W64))),
  Directive.instr
    (regular Width.W64 Width.W64
      (Operation.lockUn LockUnOp.inc { base := some (RegOrRip.reg Reg64.rdi), idx := none })),
  Directive.instr
    (regular Width.W64 Width.W32
      (Operation.lockUn LockUnOp.not { base := some (RegOrRip.reg Reg64.rdi), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("
  lock subq %rax, (%rdi)
  lock incq (%rdi)
  lock notl (%rdi)
")

/-- error: line 1: expecting lockable instruction after `lock' -/
#guard_msgs in
#check parse("lock addl $1, %eax")

/-- error: line 1: expecting lockable instruction after `lock' -/
#guard_msgs in
#check parse("lock xaddl %eax, %ebx")

/-- error: line 1: expecting lockable instruction after `lock' -/
#guard_msgs in
#check parse("lock movl $1, (%rdi)")

/-- error: line 1: can't have two memory operands -/
#guard_msgs in
#check parse("xchgl (%rdi), (%rsi)")

-- `movnti`: the register gives the width; a suffix must agree with it.
/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.movnti { base := some (RegOrRip.reg Reg64.rdi), idx := none } (low Reg64.rax Width.W32))),
  Directive.instr
    (regular Width.W64 Width.W64
      (Operation.movnti
        { base := some (RegOrRip.reg Reg64.rsi), idx := some { reg := Reg64.rcx, scale := Width.W64 }, disp := ↑8 }
        (low Reg64.rbx Width.W64))),
  Directive.instr
    (regular Width.W64 Width.W32
      (Operation.movnti { base := none, idx := none, disp := ↑"x" } (low Reg64.rbx Width.W32)))] : List Directive
-/
#guard_msgs in
#check parse("
  movnti %eax, (%rdi)
  movntiq %rbx, 8(%rsi,%rcx,8)
  movntil %ebx,(x)
")

/-- error: line 1: type error: w64 != w32 -/
#guard_msgs in
#check parse("movntiq %eax, (%rdi)")

/-- error: line 1: movnti needs a 32- or 64-bit register -/
#guard_msgs in
#check parse("movnti %ax, (%rdi)")

/-- error: line 1: expected: '(' -/
#guard_msgs in
#check parse("movnti %eax, %ebx")

/-- error: line 1: expecting lockable instruction after `lock' -/
#guard_msgs in
#check parse("lock movnti %eax, (%rdi)")

end atomics

section error_reporting

/-- error: line 1: unknown register: unlikely -/
#guard_msgs in
#check parse("xorq %rax, %unlikely")

/--
error: line 1: type mismatch in memory addressing operands: base ({w1}) and index ({w2}) have different widths
-/
#guard_msgs in
#check parse("mov (%rax, %ebx)")

/-- error: line 1: can't have two memory operands -/
#guard_msgs in
#check parse("mov (%rax), (%rax)")

/-- error: line 1: high byte register cannot be used for an addrexpr -/
#guard_msgs in
#check parse("mov $2, (%ah)")

/-- error: line 1: unexpected end of input -/
#guard_msgs in
#check parse("addq %rax")

/-- error: line 1: unexpected end of input -/
#guard_msgs in
#check parse("xorq %rax, 1")

/-- error: line 1: unexpected end of input -/
#guard_msgs in
#check parse("addq")

/-- error: line 2: unexpected end of input -/
#guard_msgs in
#check parse("
  addq %rax
  cmpq $10, %rax
")

/-- error: line 1: type error: w64 != w32 -/
#guard_msgs in
#check parse("movq %eax, %rbx")

/-- error: line 1: invalid scale 3, must be 1, 2, 4, or 8 -/
#guard_msgs in
#check parse("movq (%rax, %rcx, 3), %rbx")

/-- error: line 1: unexpected trailing characters on line -/
#guard_msgs in
#check parse("movq %rax, %rbx garbage")

end error_reporting

section vector_moves

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W128
      (AvxOperation.movapd ↑(AvxReg.xmm RegMm.mm1)
        ↑{ base := some (RegOrRip.reg Reg64.rdi), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("movapd (%rdi), %xmm1")

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W128
      (AvxOperation.movdqa ↑{ base := some (RegOrRip.reg Reg64.rsp), idx := none, disp := ↑16 }
        ↑(AvxReg.xmm RegMm.mm2)))] : List Directive
-/
#guard_msgs in
#check parse("movdqa %xmm2, 16(%rsp)")

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W128
      (AvxOperation.movdqu ↑(AvxReg.xmm RegMm.mm3)
        ↑{ base := some (RegOrRip.reg Reg64.rdi),
            idx := some { reg := Reg64.rcx, scale := Width.W8 } }))] : List Directive
-/
#guard_msgs in
#check parse("movdqu (%rdi,%rcx,1), %xmm3")

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W256
      (AvxOperation.vmovapd ↑(AvxReg.ymm RegMm.mm4)
        ↑{ base := some (RegOrRip.reg Reg64.rdi), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("vmovapd (%rdi), %ymm4")

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W128
      (AvxOperation.vmovdqa ↑{ base := some (RegOrRip.reg Reg64.rsi), idx := none }
        ↑(AvxReg.xmm RegMm.mm5)))] : List Directive
-/
#guard_msgs in
#check parse("vmovdqa %xmm5, (%rsi)")

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W256
      (AvxOperation.vmovdqu ↑(AvxReg.ymm RegMm.mm6)
        ↑{ base := some (RegOrRip.reg Reg64.rsi), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("vmovdqu (%rsi), %ymm6")

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W128
      (AvxOperation.cmpxchg16b false { base := some (RegOrRip.reg Reg64.rdi), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("cmpxchg16b (%rdi)")

/--
info: [Directive.instr
    (avx Width.W64 AvxWidth.W128
      (AvxOperation.cmpxchg16b true
        { base := some (RegOrRip.reg Reg64.rsp), idx := none, disp := ↑16 }))] : List Directive
-/
#guard_msgs in
#check parse("lock cmpxchg16b 16(%rsp)")

/-- error: line 1: expecting lockable instruction after `lock' -/
#guard_msgs in
#check parse("lock movdqa (%rdi), %xmm1")

end vector_moves

section tzcnt

/--
info: [Directive.instr
    (regular Width.W64 Width.W64
      (Operation.tzcnt (low Reg64.rax Width.W64) ↑(low Reg64.rbx Width.W64)))] : List Directive
-/
#guard_msgs in
#check parse("tzcntq %rbx, %rax")

/--
info: [Directive.instr
    (regular Width.W64 Width.W32
      (Operation.tzcnt (low Reg64.rcx Width.W32)
        ↑{ base := some (RegOrRip.reg Reg64.rdi), idx := none }))] : List Directive
-/
#guard_msgs in
#check parse("tzcnt (%rdi), %ecx")

/--
info: [Directive.instr
    (regular Width.W64 Width.W16
      (Operation.tzcnt (low Reg64.rdx Width.W16) ↑(low Reg64.rsi Width.W16)))] : List Directive
-/
#guard_msgs in
#check parse("tzcntw %si, %dx")

/-- error: line 1: tzcnt has no 8-bit form -/
#guard_msgs in
#check parse("tzcnt %bl, %al")

/-- error: line 1: unsupported instruction: tzcntb -/
#guard_msgs in
#check parse("tzcntb %bl, %al")

-- The Intel printer: destination first, the memory operand sized.
/--
info: Except.ok ["tzcnt rax, rbx", "tzcnt ecx, DWORD PTR [rdi+0]", "tzcnt dx, si", "tzcnt r8, QWORD PTR [rdi+rcx*8+16]"]
-/
#guard_msgs in
#eval (Kraken.X64.Parser.parse
  "tzcntq %rbx, %rax\ntzcnt (%rdi), %ecx\ntzcntw %si, %dx\ntzcntq 16(%rdi,%rcx,8), %r8").map
  (·.map toString)

end tzcnt

section broken

-- TODO: Support absolute memory addressing (bare displacements) and add reliable integration tests for it.
-- Currently, the parser requires '(' after displacement, so this fails to parse with "expected: '('".
-- Also, testing this on real x86 is tricky because we need a guaranteed mapped addresses.
/-- error: line 1: expected: '(' -/
#guard_msgs in
#check parse("movq 1, %rax")

end broken

end Tests
