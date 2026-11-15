/*
 * Kraken EFI stub: declarations shared by stub.cc (the ISA-independent
 * part) and stub_x64.cc / stub_a64.cc (one per ISA; build.sh compiles the
 * one for the image's ISA).
 */
#ifndef KRAKEN_EFI_STUB_H_
#define KRAKEN_EFI_STUB_H_

#include <efi.h>

#include "debug.h"

/* The C library functions the stub needs (stub.cc). clang may also emit
   calls to memset and memcpy itself, so they must exist. */
extern "C" void* memset(void* dest, int c, size_t n);
extern "C" void* memcpy(void* dest, const void* src, size_t n);

/* Per ISA (stub_x64.cc, stub_a64.cc). */
EFI_STATUS InitPlatform(EFI_SYSTEM_TABLE* system_table, uint64_t* bootstrap_length);
EFI_STATUS InitMMU(EFI_MEMORY_DESCRIPTOR* map, UINTN memory_map_size, UINTN descriptor_size, uint64_t bootstrap_length);
/* Masks interrupts and halts forever. */
[[noreturn]] void halt_forever();
/// Handoff from EFI.
[[noreturn]] void Handoff();

#endif  // KRAKEN_EFI_STUB_H_
