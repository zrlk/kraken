# Undefined flags: cf, pf, af, zf, sf, of

# Test: unsigned division (divq/divl/divw/divb, register and memory divisors).
# The operands come from the fuzzed registers: the divisor is forced odd (so
# nonzero) and the high half of the dividend below the divisor, so no divide
# error occurs.

movq %rcx, %r8
orq $1, %r8
movq %rbx, %rax
movq %r8, %rdx
shrq $1, %rdx
divq %r8
movq %rax, %r9
movq %rdx, %r10

movq %rsi, %rax
xorl %edx, %edx
movq %r8, -8(%rsp)
divq -8(%rsp)
movq %rax, %r11
movq %rdx, %r12

movl %ebx, %eax
movl %ecx, %r13d
orl $1, %r13d
movl %r13d, %edx
shrl $1, %edx
divl %r13d
movq %rax, %r14
movq %rdx, %r15

movl %esi, %eax
xorl %edx, %edx
movw %cx, %di
orw $1, %di
divw %di
movq %rax, %rbp

movzbl %bl, %eax
movb %cl, %dl
orb $1, %dl
divb %dl
