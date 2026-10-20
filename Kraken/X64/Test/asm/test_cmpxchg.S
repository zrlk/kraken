# cmpxchg without lock: success and failure on memory, the register form,
# and the 32-bit form's write to eax.

# Success on memory: destination takes the source, rax keeps its value.
movq $5, %rax
movq $5, -8(%rsp)
movq $9, %rbx
cmpxchgq %rbx, -8(%rsp)     # mem = 9, rax = 5, ZF = 1
movq -8(%rsp), %rcx

# Failure on memory: rax takes the destination, memory is unchanged.
movq $6, %rax
movq $11, %rdx
cmpxchgq %rdx, -8(%rsp)     # mem = 9, rax = 9, ZF = 0
movq -8(%rsp), %rsi

# Register destination.
movq $9, %rax
movq $9, %rdi
movq $1, %r8
cmpxchgq %r8, %rdi          # rdi = 1

# 32-bit success: what happens to the upper half of rax.
movq $-1, %rax
movl $-1, -16(%rsp)
movl $3, %r9d
cmpxchgl %r9d, -16(%rsp)    # mem = 3; ZF = 1
movl -16(%rsp), %r10d
