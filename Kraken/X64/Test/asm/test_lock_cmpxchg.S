# lock cmpxchg: both outcomes on memory, with the comparison's flags.

movq $5, %rax
movq $5, -8(%rsp)
movq $9, %rbx
lock cmpxchgq %rbx, -8(%rsp)    # success: mem = 9, rax = 5
movq -8(%rsp), %rcx

movq $6, %rax
movq $11, %rdx
lock cmpxchgq %rdx, -8(%rsp)    # failure: mem = 9, rax = 9; flags from 6 - 9
movq -8(%rsp), %rsi
