/*
 * x86-64 helpers for the Kraken EFI stub (stub_x64.cc and any other x64
 * code): port I/O, the time-stamp counter, and CPUID (clang's <cpuid.h>:
 * __cpuid). Inline asm and builtins, since the stub has no MSVC intrinsics
 * (__inbyte, __outbyte, __rdtsc, __readcr0, __writecr0, __readcr3, __readmsr,
 * __writemsr).
 */
#ifndef KRAKEN_EFI_X64_H_
#define KRAKEN_EFI_X64_H_

#include <cpuid.h>      // clang's own header: __cpuid
#include <stddef.h>     // clang's own header: offsetof
#include <stdint.h>     // clang's own header
#include <x86intrin.h>  // clang's own header: _mm_pause, _wbinvd

static inline uint8_t inb(uint16_t port) {
  uint8_t v;
  __asm__ volatile("inb %w1, %b0" : "=a"(v) : "Nd"(port));
  return v;
}

static inline void outb(uint16_t port, uint8_t v) {
  __asm__ volatile("outb %b0, %w1" : : "a"(v), "Nd"(port));
}

static inline uint64_t rdtsc() { return __builtin_ia32_rdtsc(); }

// Control registers (MSVC: __readcr0, __writecr0, __readcr3). volatile: they
// change behind the compiler's back. Writing CR0 changes how memory behaves
// (paging, caching, write protection), hence the memory clobber.
static inline uint64_t readcr0() {
  uint64_t v;
  __asm__ volatile("mov %%cr0, %0" : "=r"(v));
  return v;
}

static inline void writecr0(uint64_t v) {
  __asm__ volatile("mov %0, %%cr0" : : "r"(v) : "memory");
}

// Flushes the TLB entry for the page holding p (MSVC: __invlpg).
static inline void invlpg(void* p) {
  __asm__ volatile("invlpg (%0)" : : "r"(p) : "memory");
}

static inline uint64_t readcr3() {
  uint64_t v;
  __asm__ volatile("mov %%cr3, %0" : "=r"(v));
  return v;
}

// Model-specific registers (MSVC: __readmsr, __writemsr): the MSR number in
// ECX, the value split across EDX:EAX. volatile, and a memory clobber on the
// write: MSRs change behind the compiler's back, and writing one (the APIC
// base, EFER, PAT) can change how memory behaves.
static inline uint64_t rdmsr(uint32_t msr) {
  uint32_t lo, hi;
  __asm__ volatile("rdmsr" : "=a"(lo), "=d"(hi) : "c"(msr));
  return (static_cast<uint64_t>(hi) << 32) | lo;
}

static inline void wrmsr(uint32_t msr, uint64_t v) {
  __asm__ volatile("wrmsr"
                   :
                   : "c"(msr), "a"(static_cast<uint32_t>(v)),
                     "d"(static_cast<uint32_t>(v >> 32))
                   : "memory");
}

// Reads the 64-bit value `offset` bytes from the GS base, as MSVC's
// __readgsqword (its signature, without the reserved leading underscores).
// With the GS base set to a CPU's own record (kGsBaseMSR, as CpuEntryPoint
// does), this reads a field of the current CPU's record.
// volatile and a memory clobber: the GS base changes behind the compiler's
// back (wrmsr), and the record may have been written through an ordinary
// pointer, which the compiler would otherwise not order before this read.
static inline uint64_t readgsqword(uint32_t offset) {
  uint64_t v;
  __asm__ volatile("movq %%gs:(%1), %0"
                   : "=r"(v)
                   : "r"(static_cast<uint64_t>(offset))
                   : "memory");
  return v;
}

// Writes the 64-bit `value` `offset` bytes from the GS base, as MSVC's
// __writegsqword (its signature, without the leading underscores): a field
// of the current CPU's record, as readgsqword reads it. volatile and a
// memory clobber, as there: the record may also be read through an ordinary
// pointer, which the compiler would otherwise not order after this write.
static inline void writegsqword(uint32_t offset, uint64_t value) {
  __asm__ volatile("movq %1, %%gs:(%0)"
                   :
                   : "r"(static_cast<uint64_t>(offset)), "r"(value)
                   : "memory");
}

constexpr int kApicBaseMsr = 0x1B;
constexpr uint64_t kApicBaseMsrEnable = 0x800;
constexpr uint32_t kLapicVersion = ((0x0030) >> 2);
constexpr uint32_t kLapicErrorStatus = ((0x280) >> 2);
constexpr uint32_t kLapicInterruptCommand0 = ((0x300) >> 2);
constexpr uint32_t kLapicInterruptCommand1 = ((0x310) >> 2);

struct __attribute__((packed)) LocalApicVersion {
  uint64_t version : 8;
  uint64_t zero_0 : 8;
  uint64_t max_lvt_entry : 8;
  uint64_t supports_eoi_broadcast_suppression : 1;
  uint64_t zero_1 : 7;
};

#pragma pack(push, 1)
struct InterruptDescriptor64 {
  uint16_t offset_1;  // offset bits 0..15
  uint16_t selector;  // a code segment selector in GDT or LDT
  uint8_t
      ist;  // bits 0..2 holds Interrupt Stack Table offset, rest of bits zero.
  uint8_t type_attributes;  // gate type, dpl, and p fields
  uint16_t offset_2;        // offset bits 16..31
  uint32_t offset_3;        // offset bits 32..63
  uint32_t zero;            // reserved
};

struct InterruptDescriptorTableRegister64 {
  uint16_t limit;
  uint64_t base;
};

struct TaskStateSegmentPointerPair {
  uint32_t low;
  uint32_t high;
};
struct TaskStateSegment {
  uint32_t zero_0;
  TaskStateSegmentPointerPair rsp[3];
  uint32_t zero_1;
  uint32_t zero_2;
  TaskStateSegmentPointerPair ist[7];
  uint32_t zero_3;
  uint32_t zero_4;
  uint16_t zero_5;
  uint16_t iopb;
};
static_assert(offsetof(TaskStateSegment, zero_3) == 0x5c);
static_assert(offsetof(TaskStateSegment, zero_1) == 0x1c);
#pragma pack(pop)

constexpr uint32_t kLapicSpuriousVector = ((0x0F0) >> 2);
constexpr uint32_t kLapicLvtTimer = ((0x320) >> 2);
/// @brief Performance counter interrupt on overflow or "ToPA PMI"
constexpr uint32_t kLapicLvtPerfCtr = ((0x340) >> 2);
/// @brief Interrupt signalled on LINT0
constexpr uint32_t kLapicLvtLint0 = ((0x350) >> 2);
/// @brief Interrupt signalled on LINT1
constexpr uint32_t kLapicLvtLint1 = ((0x360) >> 2);
/// @brief Internal LAPIC error
constexpr uint32_t kLapicLvtError = ((0x370) >> 2);
/// @brief Task priority.
constexpr uint32_t kLapicTaskPriority = ((0x80) >> 2);
/// @brief Logical destination register.
constexpr uint32_t kLapicLogicalDestination = ((0xd0) >> 2);
/// @brief Destination format register.
constexpr uint32_t kLapicDestinationFormat = ((0xe0) >> 2);
/// @brief End of interrupt register.
constexpr uint32_t kLapicEndOfInterrupt = ((0xB0) >> 2);
/// @brief Timer initial count.
constexpr uint32_t kLapicTimerInitialCount = ((0x380) >> 2);

constexpr uint32_t kLapicDisable = 0x10000;
constexpr uint32_t kLapicNmi = (4 << 8);
constexpr uint32_t kLapicSwEnable = 0x100;
constexpr uint32_t kLapicTimerDivide = ((0x3e0) >> 2);

constexpr uint32_t kGsBaseMSR = 0xC0000101;
constexpr uint32_t kKernelGsBaseMSR = 0xC0000102;
constexpr uint32_t kFsBaseMSR = 0xC0000100;

struct Cpu {
  /// The top of this cpu's kernel stack.
  uint64_t stack_top;
  /// This cpu's task state segment.
  uint16_t tss;
  /// The top of this cpu's interrupt stack.
  uint64_t isr_stack_top;
  /// The virtual address of this cpu's lapic.
  volatile uint32_t* lapic;
  /// Whether this cpu is the BSP.
  bool is_bsp;
  /// This cpu's lapic processor ID.
  uint32_t cpu_id;
  /// This cpu's lapic ID. Acts as the index into the gCpus table.
  uint32_t lapic_id;
  /// The current small alloc slab pointer.
  uint8_t* small_alloc_slab;
  /// One past the end of the small alloc slab.
  uint8_t* small_alloc_slab_limit;
  /// The current thread slab pointer. (TODO: this needs to be in a different virtual address range etc; this is a temporary hack.)
  uint8_t* thread_slab;
  /// One past the end of the thread slab.
  uint8_t* thread_slab_limit;
};

#endif  // KRAKEN_EFI_X64_H_
