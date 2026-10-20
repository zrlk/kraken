# Undefined flags: of, sf, af, pf
# Test trailing zero count (BMI1): tzcntq, tzcntl, tzcntw, register and memory sources
#
# Expected final values:
#   rax: 64 (tzcntq of 0; CF set)
#   rbx: 63 (tzcntq of 0x8000000000000000)
#   rcx: 32 (tzcntl of 0, upper half cleared)
#   rdx: 0xFFFFFFFFFFFF0010 (tzcntw of 0 merges 16 into dx)
#   rsi: 4 (tzcntq of a memory word 0x30)
#   rdi: 0 (tzcntq of an odd value; ZF set, CF clear: the flags compared)

movq $0, %r8
tzcntq %r8, %rax

movabsq $0x8000000000000000, %r9
tzcntq %r9, %rbx

movq $-1, %rcx
movq $0xFFFFFFFF00000000, %r10
tzcntl %r10d, %ecx

movq $-1, %rdx
movq $0xFFFFFFFFFFFF0000, %r11
tzcntw %r11w, %dx

pushq $0x30
tzcntq (%rsp), %rsi
popq %r12

movq $0x2B, %r13
tzcntq %r13, %rdi
