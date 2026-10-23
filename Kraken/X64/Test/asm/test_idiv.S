# Undefined flags: cf, pf, af, zf, sf, of

# Test: signed division (cqto/cltd/cwtd and idivq/idivl/idivw/idivb, register
# and memory divisors). The dividend is a sign-extended fuzzed register and the
# divisor is forced odd (so nonzero); a quotient overflow then needs the most
# negative dividend divided by -1.

movq %rcx, %r8
orq $1, %r8
movq %rbx, %rax
cqto
idivq %r8
movq %rax, %r9
movq %rdx, %r10

movq %rsi, %rax
cqto
movq %r8, -8(%rsp)
idivq -8(%rsp)
movq %rax, %r11
movq %rdx, %r12

movl %ebx, %eax
cltd
movl %ecx, %r13d
orl $1, %r13d
idivl %r13d
movq %rax, %r14
movq %rdx, %r15

movl %esi, %eax
cwtd
movw %cx, %di
orw $1, %di
idivw %di
movq %rax, %rbp

movsbw %bl, %ax
movb %cl, %dl
orb $1, %dl
idivb %dl
