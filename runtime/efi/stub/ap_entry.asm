[BITS 16]
[ORG 0x8000]
Bootstrap:
  cli
  cld
  jmp BootstrapPastData
BootstrapDebugCounter:
  dq 0                        ;  MUST BE BELOW 4GB (?)
BootstrapPagetableAddress:
  dq 0xDEADBEEFBAADF00D       ;  MUST BE BELOW 4GB (?)
BootstrapCpuCountAddress:
  dq 0
BootstrapKernelStartAddress:
  dq 0
BootstrapCpuRecordBase:
  dq 0
BootstrapCpuRecordSize:
  dq 0
ALIGN 16
StartupGDT:
  dd 0
  dd 0
  dd 0xFFFF
  dd 0xCF9A00
  dd 0xFFFF
  dd 0x8F9200
  dd 0x68
  dd 0xCF8900
ALIGN 4
  dw 0 ; address field needs to be aligned on a 4-byte boundary
StartupGDTP:
  dw StartupGDTP - StartupGDT - 1
  dd StartupGDT
  dd 0
  dd 0
ALIGN 4
StartupIDTP:
  dw 0
  dd 0
ALIGN 64
BootstrapPastData:
  lock add word [BootstrapDebugCounter], 1
  xor ax, ax
  mov ds, ax
  lgdt [StartupGDTP]
  lock add word [BootstrapDebugCounter], 0x10
  mov eax, cr0
  or eax, 1
  mov cr0, eax
  jmp 8:Bootstrap32
ALIGN 32
[BITS 32]
Bootstrap32:
  lock add dword [BootstrapDebugCounter], 0x100
  mov al, 0xFF
  out 0xA1, al  ; disable PIC
  out 0x21, al  ; disable PIC
  nop
  nop
  lidt [StartupIDTP]
  lock add dword [BootstrapDebugCounter], 0x1000
  mov eax, 10100000b
  mov cr4, eax
  mov edx, [BootstrapPagetableAddress]
  mov cr3, edx
  mov ecx, 0xC0000080  ; efer
  rdmsr
  or eax, 0x100  ; write LME
  wrmsr
  lock add dword [BootstrapDebugCounter], 0x10000
  mov ebx, cr0
  or ebx, 0x80000001  ; paging + protection
  mov cr0, ebx
  lock add dword [BootstrapDebugCounter], 0x100000
  lgdt [BootstrapLongModeGDTP]
  ; tu deviens responsable pour toujours de ce que tu as apprivoisé
  jmp 8:Bootstrap64
ALIGN 16
BootstrapLongModeGDT:
  dq 0
  dq 0x00209A0000000000 ; 64B code exec/read
  dq 0x0000920000000000 ; 64B data r/w
ALIGN 4
  dw 0  ; address field needs to be aligned on a 4-byte boundary
BootstrapLongModeGDTP:
  dw $ - BootstrapLongModeGDT - 1
  dd BootstrapLongModeGDT
ALIGN 64
[BITS 64]
Bootstrap64:
  lock add dword [BootstrapDebugCounter], 0x1000000
  mov ax, 0x10
  mov ds, ax
  mov es, ax
  mov fs, ax
  mov gs, ax
  mov ss, ax
  mov ecx, 0xCAFEFACE
  mov rdx, [BootstrapCpuCountAddress]
  lock inc qword [rdx]
  lock add dword [BootstrapDebugCounter], 0x10000000
  mov rax, 0xDEADBEEFBAADF00D
DropThroughToEnterKernel:
  mov rcx, [BootstrapCpuRecordBase]
  mov rdx, [BootstrapCpuRecordSize]
  mov rax, [BootstrapKernelStartAddress]
  jmp rax
