/*
 * Kraken EFI stub, x86-64: the host side of scc's raw ABI (`scc --host raw`,
 * Scc/Lower/Raw.lean), which a raw unit such as Hello1Raw (stub_x64.cc)
 * expects of the kernel that enters it.
 *
 * A raw unit reaches its thread control block (TCB) through the %fs base,
 * and the kernel's routines through its own routine table (SccUnitKabi):
 * each routine's trampoline in the unit jumps through the table's routine
 * word for slot n, which the kernel fills when it loads the unit. The TCB
 * layout and the slot order are scc's (Scc/IR/Core.lean, namespace Tcb),
 * checked below by offset; they never change order.
 *
 * Calling convention: a raw unit is System V x86-64 code (arguments in %rdi,
 * %rsi, %rdx, %rcx, %r8, %r9; results in %rax, %rdx, ...). This stub is
 * built for the MinGW target, whose default is the Microsoft x64 convention,
 * so every routine put in an SccKabi table must be declared KRAKEN_SCC_ABI.
 */
#ifndef KRAKEN_EFI_RUNTIME_X64_H_
#define KRAKEN_EFI_RUNTIME_X64_H_

#include <stddef.h>  // clang's own header: offsetof
#include <stdint.h>  // clang's own header

#define KRAKEN_SCC_ABI __attribute__((sysv_abi))

/* The kernel routine table's slots (scc: `enum scc_kabi_slot`,
   Tcb.kabiSlots). What the repository states about a routine's arguments is
   noted; for the others scc's C prototypes are not in this repository. */
enum SccKabiSlot : uint32_t {
  kSccRtAlloc = 0,           // hello1.s: (257, 2, 3) -> pointer to the block
  kSccRtAllocTcb = 1,
  kSccRtPrint = 2,           // hello1.s: (pointer, length in bytes)
  kSccRtPark = 3,
  kSccRtUnpark = 4,
  kSccRtAbort = 5,
  kSccRtExitThread = 6,      // () after the thread stores exited := 1
  kSccRtExitProcess = 7,     // (status: scc_rt_main's result); no return
  kSccRtStackTake = 8,
  kSccRtStackRelease = 9,
  kSccRtGrow = 10,
  kSccRtThreadReserve = 11,  // -> the new thread's index (SccTcb::index)
  kSccRtThreadInit = 12,
  kSccRtSpawn = 13,          // (child TCB, stack top, entry, arg, words...)
                             // -> negative if the thread was not created
  kSccKabiSlotCount = 14,
};

/* The kernel's routines in slot order (scc: `struct scc_kabi`): one
   KRAKEN_SCC_ABI routine per slot, which the loader copies into each unit's
   table (FillUnitKabi). The slots hold addresses rather than one function
   type because the routines' signatures differ. */
struct SccKabi {
  const void* routine[kSccKabiSlotCount];
};
static_assert(sizeof(SccKabi) == 8 * kSccKabiSlotCount);

/* The routine table inside the unit (Scc/Emit/Kabi.lean). Each unit carries
   its own table and each trampoline reaches its slot RIP-relative
   (`jmp *scc_kabi_<n>(%rip)`, the label scc_kabi_<n> naming routine[n]), so
   no thread or interrupt path needs the TCB to find a routine.

   Layout: a section `.scc_kabi`, 4 KiB aligned and 4 KiB long, the first
   thing in the unit's writable segment: at the granule after `.rodata`,
   before `.data` (Scc/Test/elf/raw.ld). Word 0 is the magic "SCCKABI1" (the
   bytes S C C K A B I 1 in memory order), word 1 the number of slots the
   unit uses, both written by the compiler; words 2.. are the routine
   addresses in SccKabiSlot order, zero in the file.

   What the kernel does with a unit in this form: it finds the table at the
   start of the unit's writable segment; it refuses the unit unless word 0
   is the magic, word 1 is at least 1 and at most the number of slots it
   implements, and those slots' routine words are zero (CheckUnitKabi); it
   writes routine[0 .. slot_count) before the unit's
   first instruction (FillUnitKabi); it may then map the table's page
   read-only. Compiled code never writes the table. The TCB's kabi word is
   reserved: units in this form never read it. The kernel needs a writable
   copy of the table to fill it, so the loader copies the unit's writable
   segment out of the image (stub_x64.cc). */
constexpr uint64_t kSccUnitKabiMagic = 0x314942414b434353ull;  // "SCCKABI1"
constexpr uint64_t kSccUnitKabiAlign = 4096;
struct SccUnitKabi {
  uint64_t magic;       // kSccUnitKabiMagic
  uint64_t slot_count;  // slots the unit uses, at most kSccKabiSlotCount
  const void* routine[];
};
static_assert(offsetof(SccUnitKabi, slot_count) == 8);
static_assert(offsetof(SccUnitKabi, routine) == 16);
static_assert(16 + 8 * kSccKabiSlotCount <= kSccUnitKabiAlign);

/* Whether `table`, the first kSccUnitKabiAlign bytes of a unit's writable
   segment as in the file, is a routine table this kernel can fill: the
   magic, 1 to kSccKabiSlotCount slots, and those slots' routine words zero.
   If not, says why (DisplayString) and returns false. */
bool CheckUnitKabi(const SccUnitKabi* table);
/* Writes the kernel's routines into a table CheckUnitKabi accepted:
   routine[0 .. slot_count). */
void FillUnitKabi(SccUnitKabi* table);

/* Bytes of stack below stack_limit for the paths that run without a stack
   check (the abort routine; the grow routine and what it calls), scc's
   Tcb.headroom: stack_limit is stack_base + kSccTcbHeadroom. */
constexpr uint64_t kSccTcbHeadroom = 4096;

struct GprBlock {
  uint64_t rax;
  uint64_t rdx;
  uint64_t rcx;
  uint64_t rbx;
  uint64_t rsi;
  uint64_t rdi;
  uint64_t rbp;
  uint64_t rsp;
  uint64_t r8;
  uint64_t r9;
  uint64_t r10;
  uint64_t r11;
  uint64_t r12;
  uint64_t r13;
  uint64_t r14;
  uint64_t r15;
};

/* scc's Tcb.size and maxSpawnArgs (Scc/IR/Core.lean): compiled code uses the
   TCB's first kSccTcbFieldBytes bytes and, in a spawned thread, up to
   kSccMaxSpawnArgs scalar argument words right after them (Term.tcbLayout;
   pointer argument words go below the object header, at negative offsets).
   Nothing in compiled code touches the TCB beyond kSccTcbCompilerBytes. */
constexpr uint64_t kSccTcbFieldBytes = 104;
constexpr uint64_t kSccMaxSpawnArgs = 6;
constexpr uint64_t kSccTcbCompilerBytes = kSccTcbFieldBytes + 8 * kSccMaxSpawnArgs;

/* A thread's TCB (scc: Tcb). The %fs base holds its address; a raw unit's
   ThreadId is that address. Its first part is scc's (the fields, then the
   argument words); the rest is this kernel's: the saved registers and, last,
   the XSAVE area, whose size depends on the CPU and XCR0 (XsaveAreaBytes), so
   a TCB takes sizeof(SccTcb) + XsaveAreaBytes() bytes. The offsets here are
   repeated in runtime.asm (thread_*); keep the two in step. */
struct SccTcb {
  uint64_t self;         // the TCB's own address (%fs:0)
  uint64_t stack_limit;  // lowest address the stack may use (%fs:8)
  uint64_t permit;       // park permit, 0 or 1
  uint64_t exited;       // set to 1 (release store) when the thread finishes
  uint64_t stack_base;   // lowest address of the current stack range
  uint64_t stack_top;    // one past the highest address of that range
  uint64_t bad_mask;     // reserved for the loaded-value barrier; 0
  uint64_t index;        // 0 for the main thread
  uint64_t depth;        // unused; 0
  uint64_t alloc_blk;    // platform-owned; not used by any code yet (0)
  uint64_t rseq_desc;    // platform-owned; not used by any code yet (0)
  uint64_t ckpt;         // kernel-owned; not used by any code yet (0)
  const SccKabi* kabi;   // reserved: no unit reads it (SccUnitKabi); left
                         // null (%fs:96)
  uint64_t args[kSccMaxSpawnArgs];  // a spawned thread's scalar argument
                                    // words (%fs:104 + 8*i)
  uint64_t kernel_reserved;         // padding; free for the kernel
  union {                           // saved general-purpose registers
    uint64_t gpr[16];
    GprBlock gprs;
  };
  uint64_t rip;
  uint64_t rflags;
  alignas(64) uint8_t xsave[];      // XSAVE area (standard format),
                                    // XsaveAreaBytes() long
};
static_assert(offsetof(SccTcb, self) == 0);
static_assert(offsetof(SccTcb, stack_limit) == 8);
static_assert(offsetof(SccTcb, permit) == 16);
static_assert(offsetof(SccTcb, exited) == 24);
static_assert(offsetof(SccTcb, stack_base) == 32);
static_assert(offsetof(SccTcb, stack_top) == 40);
static_assert(offsetof(SccTcb, bad_mask) == 48);
static_assert(offsetof(SccTcb, index) == 56);
static_assert(offsetof(SccTcb, depth) == 64);
static_assert(offsetof(SccTcb, alloc_blk) == 72);
static_assert(offsetof(SccTcb, rseq_desc) == 80);
static_assert(offsetof(SccTcb, ckpt) == 88);
static_assert(offsetof(SccTcb, kabi) == 96);

static_assert(offsetof(SccTcb, args) == kSccTcbFieldBytes);
// The kernel's part must not overlap the argument words.
static_assert(offsetof(SccTcb, kernel_reserved) >= kSccTcbCompilerBytes);

// runtime.asm's thread_gpr_block, thread_rip, thread_rflags, thread_xsave.
static_assert(offsetof(SccTcb, gpr) == 160);
static_assert(offsetof(SccTcb, rip) == 288);
static_assert(offsetof(SccTcb, rflags) == 296);
static_assert(offsetof(SccTcb, xsave) == 320);
// XSAVE/XRSTOR fault on an area that is not 64-byte aligned, so a TCB must
// be too (AllocThread).
static_assert(offsetof(SccTcb, xsave) % 64 == 0);
static_assert(alignof(SccTcb) == 64);
static_assert(sizeof(SccTcb) == 320);

/* Bytes of the XSAVE area for the components enabled in XCR0 (CPUID leaf
   0xD, subleaf 0, EBX). */
uint64_t XsaveAreaBytes();

SccTcb* AllocThread(const void* entry);
void EnterThread(SccTcb* tcb);

#endif  // KRAKEN_EFI_RUNTIME_X64_H_
