# lock inc / lock dec on memory: CF is preserved from the previous operation.

movq $1, %rax
addq $-1, %rax                  # CF = 1
movq $0x7fffffffffffffff, %rsi
movq %rsi, -8(%rsp)
lock incq -8(%rsp)              # wraps: OF = 1, SF = 1, CF still 1
movq -8(%rsp), %rbx

movl $0, -16(%rsp)
lock decl -16(%rsp)             # -1; SF = 1, CF still 1
movl -16(%rsp), %ecx
