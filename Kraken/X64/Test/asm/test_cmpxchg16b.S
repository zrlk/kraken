# Test: cmpxchg16b, locked and not, both outcomes, on a 16-byte aligned slot.
# Only ZF changes among the flags.

# The stack is 256-byte aligned, so the 32 bytes below are 16-byte aligned.
subq $0x20, %rsp
movq $1, 0(%rsp)
movq $2, 8(%rsp)
movq $5, 16(%rsp)
movq $6, 24(%rsp)

# Equal, locked: the slot takes rcx:rbx, ZF is set.
movq $1, %rax
movq $2, %rdx
movq $3, %rbx
movq $4, %rcx
lock cmpxchg16b 0(%rsp)
movq 0(%rsp), %rsi              # 3
movq 8(%rsp), %rdi              # 4
cmovz %rbx, %r8                 # 3: ZF set

# Unequal, locked: rdx:rax takes the slot, ZF is cleared.
movq $7, %rax
movq $8, %rdx
lock cmpxchg16b 0(%rsp)         # rax = 3, rdx = 4
movq %rax, %r9
movq %rdx, %r10
cmovnz %rbx, %r11               # 3: ZF clear

# Equal, unlocked.
movq $5, %rax
movq $6, %rdx
movq $9, %rbx
movq $10, %rcx
cmpxchg16b 16(%rsp)
movq 16(%rsp), %r12             # 9
movq 24(%rsp), %r13             # 10

# Unequal, unlocked: ends with ZF clear.
movq $0, %rax
cmpxchg16b 16(%rsp)             # rax = 9, rdx = 10
movq 16(%rsp), %r14             # 9
movq 24(%rsp), %r15             # 10
