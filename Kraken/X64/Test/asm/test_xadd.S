# xadd without lock: memory and register destinations, and the aliased form
# `xadd %r, %r` which leaves the sum (the source is written first).

movq $5, %rax
movq $7, -8(%rsp)
xaddq %rax, -8(%rsp)        # rax = 7, mem = 12
movq -8(%rsp), %rbx

movl $3, %ecx
movl $4, %edx
xaddl %ecx, %edx            # ecx = 4, edx = 7

movq $10, %rsi
xaddq %rsi, %rsi            # rsi = 20; flags from 10 + 10
