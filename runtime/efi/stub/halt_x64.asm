; Kraken EFI stub: the final halt loop (x86-64, NASM syntax).
;
; kraken_halt never returns: it masks interrupts and halts, and jumps back
; if the CPU wakes (an NMI or SMI resumes after HLT). Called by stub.c
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
