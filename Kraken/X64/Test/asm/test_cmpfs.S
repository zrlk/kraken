# `%fs:`-relative compares. The test binary is static and links no C library,
# so the kernel leaves the %fs base at 0, which is also the model's initial
# `fsBase`: a `%fs:` operand then addresses the same bytes as the plain one.
# The flags compared are those of the last `cmp`; the earlier ones are
# recorded with `setcc`.

movq $7, %rax
movq %rax, -16(%rsp)
movq $9, %rbx
cmpq %fs:-16(%rsp), %rbx
setb %cl
seta %dl
cmpq %rbx, %fs:-16(%rsp)
setl %sil
cmpq $7, %fs:-16(%rsp)
sete %dil
cmpl %fs:-16(%rsp), %eax
setne %r8b
movq $-1, %r9
movq %r9, -8(%rsp)
cmpq %fs:-8(%rsp), %rbx
