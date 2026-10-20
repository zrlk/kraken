# mfence / lfence / sfence: no architectural effect on a single thread.

movq $1, %rax
movq %rax, -8(%rsp)
mfence
movq -8(%rsp), %rbx
addq $1, %rbx
sfence
movq %rbx, -8(%rsp)
lfence
movq -8(%rsp), %rcx
