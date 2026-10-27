/*
 * Kraken EFI stub: prints one line, exits boot services, and hangs.
 *
 * Built as a PE32+ EFI application directly by clang + lld-link (see
 * ../build.sh); uses only the BSD-licensed gnu-efi headers under
 * third_party/gnu-efi/inc, no gnu-efi library code and no gnuefi/ glue.
 *
 * Protocol (UEFI 2.10, 7.4 ExitBootServices):
 *   - get the memory map (allocating a buffer with slack first);
 *   - call ExitBootServices with the map key;
 *   - on EFI_INVALID_PARAMETER the map changed: call GetMemoryMap again
 *     into the same buffer (no allocation, no console output: after a
 *     failed ExitBootServices only GetMemoryMap and ExitBootServices may
 *     be called) and retry.
 * After success no firmware service is used; the CPU halts with
 * interrupts masked, forever, in an assembler loop (x64: halt_x64.asm,
 * NASM syntax).
 *
 * Observable results: the banner on the firmware console before exit;
 * kraken_stub_state (below) for a debugger: 1 = boot services exited and
 * halted, 2 = gave up after a failed exit (also halted).
 */

#include <efi.h>

volatile UINT32 kraken_stub_state;
volatile EFI_STATUS kraken_stub_status;

#if defined(__x86_64__)
/* halt_x64.asm (NASM): cli, then hlt in a loop. */
extern __attribute__((noreturn)) void kraken_halt(void);
#define halt_forever kraken_halt
#elif defined(__aarch64__)
/* NASM has no AArch64 target: the a64 image keeps the inline loop. */
static __attribute__((noreturn)) void halt_forever(void) {
  __asm__ volatile("msr daifset, #0xf" ::: "memory");
  for (;;) __asm__ volatile("wfi" ::: "memory");
}
#else
#error "unsupported architecture"
#endif

static void say(EFI_SYSTEM_TABLE *st, CHAR16 *s) {
  if (st->ConOut) st->ConOut->OutputString(st->ConOut, s);
}

EFI_STATUS EFIAPI efi_main(EFI_HANDLE image, EFI_SYSTEM_TABLE *st) {
  EFI_BOOT_SERVICES *bs = st->BootServices;
  EFI_MEMORY_DESCRIPTOR *map = NULL;
  UINTN size = 0, key = 0, dsize = 0;
  UINT32 dver = 0;
  EFI_STATUS s;

  say(st, L"kraken efi stub: exiting boot services\r\n");

  /* Size the map, then allocate with slack for the descriptors the
     allocation itself (and anything else) may add. */
  s = bs->GetMemoryMap(&size, NULL, &key, &dsize, &dver);
  if (s != EFI_BUFFER_TOO_SMALL) {
    say(st, L"kraken efi stub: GetMemoryMap (size) failed\r\n");
    return EFI_ERROR(s) ? s : EFI_LOAD_ERROR;
  }
  UINTN cap = size + 16 * (dsize ? dsize : sizeof(EFI_MEMORY_DESCRIPTOR));
  s = bs->AllocatePool(EfiLoaderData, cap, (VOID **)&map);
  if (EFI_ERROR(s)) {
    say(st, L"kraken efi stub: AllocatePool failed\r\n");
    return s;
  }

  for (int tries = 0; tries < 8; tries++) {
    size = cap;
    s = bs->GetMemoryMap(&size, map, &key, &dsize, &dver);
    if (EFI_ERROR(s)) {
      kraken_stub_status = s;
      if (tries == 0) {
        say(st, L"kraken efi stub: GetMemoryMap failed\r\n");
        return s;
      }
      break; /* after a failed exit: no console, no return */
    }
    s = bs->ExitBootServices(image, key);
    if (s == EFI_SUCCESS) {
      kraken_stub_state = 1;
      halt_forever();
    }
    kraken_stub_status = s;
    if (s != EFI_INVALID_PARAMETER) break;
  }
  kraken_stub_state = 2;
  halt_forever();
  return EFI_ABORTED; /* not reached */
}
