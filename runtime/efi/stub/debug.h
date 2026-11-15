/*
 * Kraken EFI stub: debugging aids, shared by every file of the stub. Text
 * and values on the firmware console (EFIConOut, DV), and in debug images
 * (DEBUG=1 build.sh: KRAKEN_DEBUG) the wait for a debugger at the start of
 * efi_main (debug_wait), which runtime/efi/gdb/kraken.py (kraken-attach)
 * finds by name.
 */
#ifndef KRAKEN_EFI_DEBUG_H_
#define KRAKEN_EFI_DEBUG_H_

#include <efi.h>

/* Text on the firmware console (debug.cc): a string, or v in hex. */
void EFIConOut(EFI_SYSTEM_TABLE* st, const char16_t* s);
void EFIConOut(EFI_SYSTEM_TABLE* system_table, uint64_t v);
void EFIConOut(EFI_SYSTEM_TABLE* st, const void* s);
void Panic(const char* msg);
#define KRAKEN_STR_(x) #x
#define KRAKEN_STR(x) KRAKEN_STR_(x) /* expands x first: the line number */
#define PANIC(msg) Panic(__FILE__ ":" KRAKEN_STR(__LINE__) ": " msg "\n")
EFI_STATUS InitVideo(EFI_SYSTEM_TABLE* system_table);
/* Draws code point c at (ox, oy); returns its width in pixels (8 or 16),
   or 0 if it does not fit on the screen. */
uint32_t PlotCharacter(uint32_t ox, uint32_t oy, uint32_t c, uint32_t fg,
                       uint32_t bg);
void DisplayString(const char* st);
/* The n bytes from st (NULs included), as DisplayString writes a string:
   to the serial port and the framebuffer. */
void DisplayChars(const char* st, uint64_t n);
void DisplayUint64(uint64_t v);
extern "C" void DebugSetIdleStatus();
extern "C" void DebugSetActiveStatus();

/* Prints "name: xVALUE"; needs an EFI_SYSTEM_TABLE* named system_table. */
#define DV(v)                               \
  {                                         \
    EFIConOut(system_table, u"" #v u": x"); \
    EFIConOut(system_table, v);             \
    EFIConOut(system_table, u"\r\n");       \
  }

/* The spin-loop hint. Always inlined, even at -O0 (debug images), and not
   in the per-ISA files: debug_wait must keep the PC inside itself while it
   spins, which kraken-attach (runtime/efi/gdb/kraken.py) relies on to find
   the stub. */
__attribute__((always_inline)) static inline void cpu_relax() {
#if defined(__x86_64__)
  __asm__ volatile("pause");
#elif defined(__aarch64__)
  __asm__ volatile("yield");
#else
#error "unsupported architecture"
#endif
}

/* Masks interrupts on this CPU (x64: cli; AArch64: all of DAIF, as
   halt_forever does). The memory clobber keeps the compiler from moving
   memory accesses across it, so that what follows runs with interrupts
   masked. */
__attribute__((always_inline)) static inline void disable_interrupts() {
#if defined(__x86_64__)
  __asm__ volatile("cli" ::: "memory");
#elif defined(__aarch64__)
  __asm__ volatile("msr daifset, #0xf" ::: "memory");
#else
#error "unsupported architecture"
#endif
}

#ifdef KRAKEN_DEBUG
/* Spins until a debugger clears kraken_debug_wait (debug.cc). */
void debug_wait();
#endif

#endif  // KRAKEN_EFI_DEBUG_H_
