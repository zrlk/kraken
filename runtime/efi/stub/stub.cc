/*
 * Kraken EFI stub: prints one line, exits boot services, and hangs.
 *
 * C++ (freestanding: no exceptions, no RTTI, no runtime library), built as a
 * PE32+ EFI application directly by clang + lld-link (see ../build.sh); uses
 * only the BSD-licensed gnu-efi headers under third_party/gnu-efi/inc, no
 * gnu-efi library code and no gnuefi/ glue.
 *
 * Protocol (UEFI 2.10, 7.4 ExitBootServices):
 *   - get the memory map (allocating a buffer with slack first);
 *   - call ExitBootServices with the map key;
 *   - on EFI_INVALID_PARAMETER the map changed: call GetMemoryMap again
 *     into the same buffer (no allocation, no console output: after a
 *     failed ExitBootServices only GetMemoryMap and ExitBootServices may
 *     be called) and retry.
 * After success no firmware service is used; the CPU halts with
 * interrupts masked, forever (halt_forever: stub_x64.cc, through entry.asm;
 * stub_a64.cc).
 *
 * This file is the ISA-independent part; stub_x64.cc and stub_a64.cc hold
 * the rest, and stub.h what they share.
 *
 * Observable results: the banner on the firmware console before exit;
 * kraken_stub_state (below) for a debugger: 1 = boot services exited and
 * halted, 2 = gave up after a failed exit (also halted).
 *
 * The entry point, the assembler routine and the variables a debugger reads
 * have C linkage, so their symbols keep their plain names.
 */

#include "stub.h"
#include "debug.h"

/* Byte loops: -ffreestanding keeps clang from turning them back into calls
   to memset and memcpy. */
extern "C" void* memset(void* dest, int c, size_t n) {
  auto* d = static_cast<unsigned char*>(dest);
  for (size_t i = 0; i < n; ++i) d[i] = static_cast<unsigned char>(c);
  return dest;
}

extern "C" void* memcpy(void* dest, const void* src, size_t n) {
  auto* d = static_cast<unsigned char*>(dest);
  auto* s = static_cast<const unsigned char*>(src);
  for (size_t i = 0; i < n; ++i) d[i] = s[i];
  return dest;
}

extern "C" {
volatile UINT32 kraken_stub_state;
volatile EFI_STATUS kraken_stub_status;
}

extern "C" EFI_STATUS EFIAPI efi_main(EFI_HANDLE image, EFI_SYSTEM_TABLE* st) {
  EFI_BOOT_SERVICES* bs = st->BootServices;
  EFI_STATUS s;

  /* First, so that a debugger can attach before any of the code below
     runs, however early it fails. */
#ifdef KRAKEN_DEBUG
  EFIConOut(st, u"kraken efi stub: waiting for debugger\r\n");
  debug_wait();
#endif

  s = InitVideo(st);
  if (EFI_ERROR(s)) {
    EFIConOut(st, u"No display!");
    return EFI_INVALID_PARAMETER;
  }

  // Check to see if we can draw characters.
  PlotCharacter(42, 32, 0x30B5, 0, 0x0000FF00);
  PlotCharacter(42 + 16, 32, 0x30B9, 0, 0x0000FF00);
  PlotCharacter(42 + 16 * 4, 32, 3267 + 219, 0, 0x0000FF00);
  DisplayString("framebuffer ok\n");
  
  uint64_t bootstrap_length;
  s = InitPlatform(st, &bootstrap_length);
  if (EFI_ERROR(s)) {
    EFIConOut(st, u"InitPlatform failed\r\n");
    kraken_stub_state = 3;
    halt_forever();
    return s;
  }

  EFIConOut(st, u"kraken efi stub: exiting boot services\r\n");

  UINTN size = 0, key = 0, dsize = 0;
  UINT32 dver = 0;
  // I've read that the extra descriptor slack here can be 2 or 16 entries.
  s = bs->GetMemoryMap(&size, nullptr, &key, &dsize, &dver);
  if (s != EFI_BUFFER_TOO_SMALL) {
    EFIConOut(st, u"kraken efi stub: GetMemoryMap (size) failed\r\n");
    return EFI_ERROR(s) ? s : EFI_LOAD_ERROR;
  }
  UINTN cap = size + 16 * (dsize ? dsize : sizeof(EFI_MEMORY_DESCRIPTOR));
  EFI_MEMORY_DESCRIPTOR* map = nullptr;
  s = bs->AllocatePool(EfiLoaderData, cap, reinterpret_cast<VOID**>(&map));
  if (EFI_ERROR(s)) {
    EFIConOut(st, u"kraken efi stub: AllocatePool failed\r\n");
    return s;
  }

  // Do a little dance to get the memory map and exit EFI. ExitBootServices only
  // works if `key` matches the exact memory map, and the key changes whenever
  // memory is freed or allocated. This might happen if there are still timer
  // callbacks and/or shutdown callbacks. We usually expect it to fail the first
  // time.
  for (int tries = 0; tries < 8; tries++) {
    size = cap;
    s = bs->GetMemoryMap(&size, map, &key, &dsize, &dver);
    if (EFI_ERROR(s)) {
      kraken_stub_status = s;
      if (tries == 0) {
        // You're allowed to call ExitBootServices (and GetMemoryMap) after a failed
        // ExitBootServices. You're *not* alowed to, e.g., print.
        EFIConOut(st, u"kraken efi stub: GetMemoryMap failed\r\n");
        return s;
      }
      break;  // Nothing else to do but halt.
    }
    s = InitMMU(map, size, dsize, bootstrap_length);
    if (EFI_ERROR(s)) {
      return s;
    }
    s = bs->ExitBootServices(image, key);
    if (s == EFI_SUCCESS) {
      // Everything's our fault now.
      kraken_stub_state = 1;
      Handoff();
      halt_forever();
    }
    kraken_stub_status = s;
    if (s != EFI_INVALID_PARAMETER) break;
  }
  kraken_stub_state = 2;
  halt_forever();
}
