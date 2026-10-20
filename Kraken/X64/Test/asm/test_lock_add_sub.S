# lock add / lock sub on memory, with immediate and register sources.

movq $40, -8(%rsp)
lock addq $2, -8(%rsp)          # 42
movq -8(%rsp), %rax

movq $100, %rbx
lock subq %rbx, -8(%rsp)        # -58; CF = 1, SF = 1
movq -8(%rsp), %rcx

movl $1, -16(%rsp)
lock addl $-1, -16(%rsp)        # 0; ZF = 1, CF = 1
movl -16(%rsp), %edx
