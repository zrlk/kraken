# Test: VEX vmovapd, vmovdqa (aligned) and vmovdqu (unaligned), on xmm and
# ymm registers and memory operands. A VEX write clears the bits of the
# destination above the operation width.

# The stack is 256-byte aligned, so the 128 bytes below are 32-byte aligned.
subq $0x80, %rsp
movq $0x0102030405060708, %rax
movq %rax, 0(%rsp)
movq $0x1112131415161718, %rax
movq %rax, 8(%rsp)
movq $0x2122232425262728, %rax
movq %rax, 16(%rsp)
movq $0x3132333435363738, %rax
movq %rax, 24(%rsp)
movq $0x4142434445464748, %rax
movq %rax, 32(%rsp)
movq $0, 64(%rsp)
movq $0, 72(%rsp)
movq $0, 80(%rsp)
movq $0, 88(%rsp)
movq $0, 96(%rsp)
movq $0, 104(%rsp)
movq $0, 112(%rsp)
movq $0, 120(%rsp)

# Upper bits for the VEX.128 writes to clear.
vmovdqu 0(%rsp), %ymm3

vmovapd 0(%rsp), %ymm0          # VEX.256, 32-byte aligned
vmovdqa 16(%rsp), %xmm1         # VEX.128, 16-byte aligned
vmovdqu 3(%rsp), %ymm2          # unaligned
vmovdqa 0(%rsp), %xmm3          # clears bits 255:128 of ymm3
vmovapd %xmm1, %xmm4
vmovdqa %ymm2, %ymm5
vmovdqu %xmm0, %xmm6

vmovdqa %ymm0, 64(%rsp)
vmovapd %xmm1, 96(%rsp)
vmovdqu %xmm2, 105(%rsp)        # unaligned store, crossing into the next 16 bytes

movq 64(%rsp), %rbx
movq 72(%rsp), %rcx
movq 80(%rsp), %rdx
movq 88(%rsp), %rsi
movq 96(%rsp), %rdi
movq 104(%rsp), %r8
movq 112(%rsp), %r9
movq 120(%rsp), %r10

