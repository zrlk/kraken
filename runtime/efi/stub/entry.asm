; Kraken EFI stub: the final halt loop (x86-64, NASM syntax).
;
; kraken_halt never returns: it masks interrupts and halts, and jumps back
; if the CPU wakes (an NMI or SMI resumes after HLT). Called by stub_x64.cc (halt_forever)
; after ExitBootServices (or after giving up), when no firmware service may
; be used any more.
;
; Assembled with: nasm -f win64 (COFF for lld-link; see ../build.sh).

        bits    64
        default rel

        section .text

        global  kraken_halt
kraken_halt:
        cli
.loop:
        hlt
        jmp     .loop

; outb_wait port, immediate writes immediate to port and waits
; clobbers al
%macro outb_wait 2
  mov al, %2
  out %1, al
  xor al, al
  out 0x80, al  ; io_wait
%endmacro

        extern CpuEntryPoint
        extern gLongModeGDTP
        extern gLongModeIDTP
        extern DebugSetIdleStatus

; EnterRuntime(rcx: gCpus, rdx: CpuRecordSize)
        global EnterRuntime
EnterRuntime:
  cli
  cld

  ; Mask all PIC interrupts and remap vectors outside of the exception
  ; range. Otherwise we could mistake a spurious interrupt for an
  ; exception.

  outb_wait 0xA1, 0xFF  ; mask primary PIC interrupts
  outb_wait 0x21, 0xFF  ; mask secondary PIC interrupts
  outb_wait 0x20, 0x11  ; init primary PIC (ICW1_INIT | ICW1_ICW4)
  outb_wait 0xA0, 0x11  ; init secondary PIC
  outb_wait 0x21, 0x20  ; set primary PIC vector offset
  outb_wait 0xA1, 0x20  ; set secondary PIC vector offset
  outb_wait 0x21, 4     ; primary PIC -> secondary PIC
  outb_wait 0xA1, 2     ; secondary PIC cascade identity
  outb_wait 0x21, 0x01  ; primary PIC should use 8086 mode
  outb_wait 0xA1, 0x01  ; secondary PIC should use 8086 mode

  ; Turn on SSE and AVX support (and FXSAVE/FXRSTOR)

  mov rax, cr0
  and ax, 0xFFFB  ; clear CR0.EM (2)
  or ax, 2        ; set CR0.MP (1)
  mov cr0, rax

  mov rax, cr4
  or rax, 3 << 9   ; set CR4.OSFXSR and CR4.OSXMMEXCPT (10, 9)
  or rax, 1 << 18  ; set CR4.OSXSAVE (18)
  mov cr4, rax

  mov rsi, rcx    ; Save rcx.
  mov rdi, rdx    ; Save rdx.

  xor rcx, rcx
  xgetbv          ; Load xcr0
  or rax, 7       ; Enable avx, sse, x87
  xsetbv          ; Save xcr0

  ; Figure out which processor we are and load the relevant record.

  mov eax, 1      ; For cpuid.
  xor ecx, ecx    ; For cpuid.
  cpuid
  mov rcx, rsi    ; Restore rcx.
  mov rdx, rdi    ; Restore rdx.
  shr ebx, 24     ; Find (the actual) CPU id.

  mov rax, rdx
  xor rdx, rdx
  mul rbx
  add rcx, rax
  mov rsp, [rcx]    ; Set up stack.

  ; Set up the final GDT.
  mov rax, [gLongModeGDTP]
  lgdt [rax]

  ; There's no better way to do this in long mode.
  push 0x10        ; stack segment
  push qword [rcx] ; rsp
  pushf            ; rflags
  push 0x8         ; code segment
  mov rax, _PastIret
  push rax         ; rip mr. delicious
  iretq

_PastIret:
  mov ax, 0x10
  mov ds, ax
  mov es, ax
  mov fs, ax
  mov gs, ax

  mov ax, word [rcx + 8]
  ltr ax

  mov rax, [gLongModeIDTP]
  lidt [rax]

  call CpuEntryPoint

  ; It's useful to know when IdleLoopSti <= rip < IdleLoopEnd
global IdleLoopSti
global IdleLoopPostSti
global IdleLoopEnd
  ; We fall through to the idle loop here.
IdleLoopSti:
  call DebugSetIdleStatus
  sti
IdleLoopPostSti:
  hlt
  jmp IdleLoopPostSti
IdleLoopEnd:
  nop

  ; See 6.14.2 64-Bit Mode Stack Frame for alignment information.
  ; This might be not ideal.

  ; SS
  ; RSP
  ; RFLAGS
  ; CS
  ; RIP           <- Top of stack for iretq.
  ; Error code
  ; Vector number <- RSP
isr_stub:
  ; int 3
  mov rax, [rsp]
  mov rbx, [rsp + 8]
  mov rcx, 0xCAFEF00D
  mov rdx, cr2
  jmp $
  ; add rsp, 0x10
  ; iretq

extern InterruptStub

isr_standard_stub:
  ; my alignment calculation is off???
  sub rsp, 8
  push rax
  push rcx
  mov rcx, [rsp + 0x18] ; vector
  push rdx
  push r8
  push r9
  push r10
  push r11 ; stack is now 16B aligned
  sub rsp, 0x60
  movdqa [rsp], xmm0
  movdqa [rsp + 0x10], xmm1
  movdqa [rsp + 0x20], xmm2
  movdqa [rsp + 0x30], xmm3
  movdqa [rsp + 0x40], xmm4
  movdqa [rsp + 0x50], xmm5
  call InterruptStub
  movdqa xmm0, [rsp]
  movdqa xmm1, [rsp + 0x10]
  movdqa xmm2, [rsp + 0x20]
  movdqa xmm3, [rsp + 0x30]
  movdqa xmm4, [rsp + 0x40]
  movdqa xmm5, [rsp + 0x50]
  add rsp, 0x60
  pop r11
  pop r10
  pop r9
  pop r8
  pop rdx
  pop rcx
  pop rax
  add rsp, 0x10 ; pop vector qword
  iretq

%macro ISR_STANDARD 1
  global InitIsr%1
  InitIsr%1:
    push qword %1
    jmp isr_standard_stub
%endmacro

%macro ISR_NOERR 1
  global InitIsr%1
  InitIsr%1:
    ; cli              ; nb: this is not necessary for interrupt gates
    push qword 0
    push qword %1
    jmp isr_stub
%endmacro

%macro ISR_ERR 1
  global InitIsr%1
  InitIsr%1:
    ; cli              ; nb: this is not necessary for interrupt gates
    push qword %1
    jmp isr_stub
%endmacro

; Vectors 0-31 are reserved by the system.
; A fault saves RIP at the faulting instruction.
; A trap saves RIP at the following instruction.
; The NMI handler cannot nest. NMIs are blocked until the next iret.
%assign intnum 0
%rep 8
  ISR_NOERR intnum
  ; 0 #DE Divide Error - Fault
  ; 1 #DB Debug Exception - Fault/Trap
  ; 2     NMI - Interrupt
  ; 3 #BP Breakpoint - Trap (int3)
  ; 4 #OF Overflow - Trap (into)
  ; 5 #BR Bound - Fault (bound)
  ; 6 #UD Undefined - Fault
  ; 7 #NM Math coprocessor - Fault
%assign intnum intnum + 1
%endrep
  ISR_ERR 8        ; #DF Double Fault - Abort (err: 0)
  ISR_NOERR 9      ;     Coprocessor segment overrun
  ISR_ERR 10       ; #TS Invalid TSS - Fault
  ISR_ERR 11       ; #NP Segment not present - Fault
  ISR_ERR 12       ; #SS Stack segment fault - Fault
  ISR_ERR 13       ; #GP General protection fault - Fault
  ISR_ERR 14       ; #PF Page fault - Fault
  ISR_NOERR 15     ;     Mystery
  ISR_NOERR 16     ; #MF Math fault x87 - Fault
  ISR_ERR 17       ; #AC Alignment check - Fault (arr: 0)
  
  ISR_NOERR 18     ; 18 #MC Machine check - Abort
  ISR_NOERR 19     ; 19 #XM SIMD exception - Fault
  ISR_NOERR 20     ; 20 #VE Virtualization exception - Fault
  ISR_ERR 21       ; 21 #CP Control protection - Fault (CET indirect branch)

%assign intnum 22
%rep 10
  ; 22-31 are reserved.
  ISR_NOERR intnum
%assign intnum intnum + 1
%endrep

%assign intnum 32
%rep 224
  ; 32-255 are interrupts.
  ISR_STANDARD intnum
%assign intnum intnum + 1
%endrep
