# Test: legacy movapd, movdqa (aligned) and movdqu (unaligned), register and
# memory forms. A legacy write keeps the bits of the register above 128.

# The stack is 256-byte aligned, so the 64 bytes below are 16-byte aligned.
subq $0x40, %rsp
movq $0x1111111111111111, %rax
movq %rax, 0(%rsp)
movq $0x2222222222222222, %rax
movq %rax, 8(%rsp)
movq $0x3333333333333333, %rax
movq %rax, 16(%rsp)
movq $0x4444444444444444, %rax
movq %rax, 24(%rsp)
movq $0, 32(%rsp)
movq $0, 40(%rsp)
movq $0, 48(%rsp)
movq $0, 56(%rsp)

# Upper bits for the legacy writes to keep.
vmovups 0(%rsp), %ymm5

movapd 0(%rsp), %xmm0
movdqa 16(%rsp), %xmm1
movdqu 4(%rsp), %xmm2           # unaligned load
movdqa 0(%rsp), %xmm5           # keeps bits 255:128 of ymm5
movapd %xmm1, %xmm3
movdqa %xmm2, %xmm4
movdqu %xmm0, %xmm6

movdqa %xmm1, 32(%rsp)
movdqu %xmm0, 41(%rsp)          # unaligned store
movapd %xmm2, 0(%rsp)

movq 32(%rsp), %rbx
movq 40(%rsp), %rcx
movq 48(%rsp), %rdx
movq 56(%rsp), %rsi
movq 0(%rsp), %rdi
movq 8(%rsp), %r8

