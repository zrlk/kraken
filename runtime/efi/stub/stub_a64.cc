/*
 * Kraken EFI stub, AArch64 part (see stub.cc): InitPlatform and the final
 * halt.
 */
#include "stub.h"

/* NASM has no AArch64 target: the halt loop is inline asm. */
void halt_forever() {
  __asm__ volatile("msr daifset, #0xf" ::: "memory");
  for (;;) __asm__ volatile("wfi" ::: "memory");
}

/* No MMU setup on AArch64 yet. */
EFI_STATUS InitMMU([[maybe_unused]] EFI_MEMORY_DESCRIPTOR* map,
                   [[maybe_unused]] UINTN memory_map_size,
                   [[maybe_unused]] UINTN descriptor_size,
                   [[maybe_unused]] uint64_t bootstrap_length) {
  return EFI_SUCCESS;
}

EFI_STATUS InitPlatform(EFI_SYSTEM_TABLE* st, uint64_t* bootstrap_length) {
  (void)st;
  *bootstrap_length = 0;
  return EFI_SUCCESS;
}

void Handoff() {
  halt_forever();
}