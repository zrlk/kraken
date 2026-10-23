# Test: cqto/cltd/cwtd (the sign of rax fills rdx at the operand size) and
# popcnt at 64, 32 and 16 bits with register and memory sources. popcnt is last:
# it defines every status flag (ZF from the source, the others cleared).

movq %rbx, %rax
cqto
movq %rdx, %r8
movq %rcx, %rax
cltd
movq %rdx, %r9
movq %rsi, %rax
cwtd
movq %rdx, %r10

popcntq %rbx, %r11
popcntl %ecx, %r12d
popcntw %si, %r13w
movq %rdi, -8(%rsp)
popcntq -8(%rsp), %r14
xorl %r15d, %r15d
popcntq %r15, %r15
