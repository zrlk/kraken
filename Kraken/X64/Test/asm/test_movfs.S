# `%fs:`-relative moves. The test binary is static and links no C library, so
# the kernel leaves the %fs base at 0, which is also the model's initial
# `fsBase`: a `%fs:` operand then addresses the same bytes as the plain one.

movq $-1, %rax
movq %rax, -16(%rsp)
movl $0x12345678, %ebx
movl %ebx, %fs:-16(%rsp)
movq -16(%rsp), %rcx
movabsq $0x1122334455667788, %rdx
movq %rdx, %fs:-8(%rsp)
movq %fs:-8(%rsp), %rsi
movq $5, %r8
movq $-3, %fs:-56(%rsp,%r8,8)
movq -16(%rsp), %rdi
movb %fs:-8(%rsp), %r9b
