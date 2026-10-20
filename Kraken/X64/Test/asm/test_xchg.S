# xchg: register/memory in either operand order, register/register, and the
# 32-bit form zero-extending its register result. Flags are untouched.

movq $0x1111, %rax
movq $0x2222, -8(%rsp)
xchgq %rax, -8(%rsp)        # rax = 0x2222, mem = 0x1111
movq -8(%rsp), %rbx

movl $7, %ecx
movq $0x300000009, %rdx
xchgl %ecx, %edx            # ecx = 9, rdx = 7 (upper half cleared)

xchgq -8(%rsp), %rsi        # rsi = 0x1111, mem = 0
movq -8(%rsp), %rdi
