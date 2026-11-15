; Kraken EFI stub: assembler routines of the x86-64 runtime (NASM syntax),
; the host side of scc's raw ABI (runtime_x64.h, runtime_x64.cc).
;
; Linked into the x64 image like entry.asm: export a routine with `global`,
; declare it in C++ with extern "C", and it is called like any other
; function.
;
; Calling conventions: C++ in the stub uses the Microsoft x64 convention
; (arguments in rcx, rdx, r8, r9, 32 bytes of shadow space; rbx, rbp, rdi,
; rsi, rsp, r12-r15 and xmm6-xmm15 callee-saved). A routine that a raw unit
; calls, through an SccKabi slot, or that is declared KRAKEN_SCC_ABI in C++,
; uses System V instead (arguments in rdi, rsi, rdx, rcx, r8, r9; no shadow
; space; rbx, rbp, rsp, r12-r15 callee-saved).
;
; Assembled with: nasm -f win64 (COFF for lld-link; see ../build.sh).

        bits    64
        default rel

        section .text
        global RuntimeEnterThread
        extern DebugSetActiveStatus

thread_gpr_block equ 160
thread_rax equ thread_gpr_block + 0
thread_rdx equ thread_gpr_block + 8 * 1
thread_rcx equ thread_gpr_block + 8 * 2
thread_rbx equ thread_gpr_block + 8 * 3
thread_rsi equ thread_gpr_block + 8 * 4
thread_rdi equ thread_gpr_block + 8 * 5
thread_rbp equ thread_gpr_block + 8 * 6
thread_rsp equ thread_gpr_block + 8 * 7
thread_r8 equ thread_gpr_block + 8 * 8
thread_r9 equ thread_gpr_block + 8 * 9
thread_r10 equ thread_gpr_block + 8 * 10
thread_r11 equ thread_gpr_block + 8 * 11
thread_r12 equ thread_gpr_block + 8 * 12
thread_r13 equ thread_gpr_block + 8 * 13
thread_r14 equ thread_gpr_block + 8 * 14
thread_r15 equ thread_gpr_block + 8 * 15
thread_rip equ 288
thread_rflags equ 296
thread_xsave equ 320

; fs should contain the thread record
; the stack is 8 bytes out of 16 byte alignment because of saved rip
RuntimeEnterThread:
  call DebugSetActiveStatus
  ; All components enabled in xcr0
  mov eax, -1
  mov edx, -1
  xrstor64 fs:[thread_xsave]
  mov rax, fs:[thread_rax]
  mov rdx, fs:[thread_rdx]
  mov rcx, fs:[thread_rcx]
  mov rbx, fs:[thread_rbx]
  mov rsi, fs:[thread_rsi]
  mov rdi, fs:[thread_rdi]
  mov rbp, fs:[thread_rbp]
  mov r8, fs:[thread_r8]
  mov r9, fs:[thread_r9]
  mov r10, fs:[thread_r10]
  mov r11, fs:[thread_r11]
  mov r12, fs:[thread_r12]
  mov r13, fs:[thread_r13]
  mov r14, fs:[thread_r14]
  mov r15, fs:[thread_r15]
  ; Vol 3 6.14.4 Stack-Switching in IA-32e Mode
  ; the interrupt stack frame is 16B aligned; the abi holds that
  ; the incoming stack will be 16B aligned, so we should be okay.
  push qword 0x10  ; SS
  push qword fs:[thread_rsp]
  push qword fs:[thread_rflags]
  push qword 0x08  ; CS
  push qword fs:[thread_rip]
  iretq
