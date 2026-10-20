# lock xadd: the memory destination gets the sum, the register the old value,
# flags as for add (here CF and OF from the wrap).

movq $0x7fffffffffffffff, %rax
movq $1, -8(%rsp)
lock xaddq %rax, -8(%rsp)   # rax = 1, mem = 0x8000000000000000
movq -8(%rsp), %rbx

movl $0xffffffff, %ecx
movl $1, -16(%rsp)
lock xaddl %ecx, -16(%rsp)  # ecx = 1, mem = 0; CF = 1, ZF = 1
movl -16(%rsp), %edx
