# Undefined flags: af

# lock and / lock or / lock xor on memory.

movq $0xff0f, -8(%rsp)
lock andq $0x0ff0, -8(%rsp)     # 0x0f00
movq -8(%rsp), %rax

movq $0xf000, %rbx
lock orq %rbx, -8(%rsp)         # 0xff00
movq -8(%rsp), %rcx

movl $0xffffffff, -16(%rsp)
lock xorl $0xffffffff, -16(%rsp) # 0; ZF = 1
movl -16(%rsp), %edx
