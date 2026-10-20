# lock not (flags untouched) and lock neg (flags as for neg) on memory.

movq $0x00ff00ff, -8(%rsp)
lock notq -8(%rsp)              # 0xffffffffff00ff00
movq -8(%rsp), %rax

movq $5, -16(%rsp)
lock negq -16(%rsp)             # -5; CF = 1, SF = 1
movq -16(%rsp), %rbx

movl $0, -24(%rsp)
lock negl -24(%rsp)             # 0; CF = 0, ZF = 1
movl -24(%rsp), %ecx
