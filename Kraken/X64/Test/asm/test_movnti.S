# movnti (32- and 64-bit forms): an ordinary store on a single thread.
# The 32-bit form writes only 4 bytes.

movq $-1, %rax
movq %rax, -16(%rsp)
movl $0x12345678, %ebx
movnti %ebx, -16(%rsp)
movq -16(%rsp), %rcx
movabsq $0x1122334455667788, %rdx
movntiq %rdx, -8(%rsp)
sfence
movq -8(%rsp), %rsi
movntil %ebx, -8(%rsp)
mfence
movq -8(%rsp), %rdi
