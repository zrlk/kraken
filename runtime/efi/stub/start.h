/*
 * Kraken EFI stub: the start hand-over of scc's raw ABI. What the kernel
 * gives a raw unit when it enters it: the start block, and the function
 * package that describes one PCI function inside the start block's words.
 *
 * The x64 image (runtime_x64.cc) and the a64 image (stub_a64.cc) include
 * this header, so its layouts and offset checks are compiled with each
 * image, but nothing uses the definitions yet. No unit in this
 * repository reads a start block yet either: scc's entry routine
 * (scc_rt_main) takes the thread control block only and ignores the second
 * argument register. The layouts here are the ones the compiler's device
 * start will read, so the kernel side can be written and tested first.
 *
 * Not in this file, because they are not settled: the layout of a device
 * object (a device handle is its address, and only that is fixed), the way a
 * unit names the PCI functions it wants, interrupt lines, and device memory.
 *
 * Little-endian, 8-byte words. The layouts are the same on x86-64 and
 * AArch64; only the entry registers differ.
 */
#ifndef KRAKEN_EFI_START_H_
#define KRAKEN_EFI_START_H_

#include <stddef.h>  // clang's own header: offsetof
#include <stdint.h>  // clang's own header

/* ----------------------------------------------------------------------
 * Entry
 *
 * The kernel calls the unit's entry (scc_rt_main, the ELF entry point) like
 * an ordinary function that never returns:
 *
 *   x86-64 (System V): %rdi = the thread's TCB, %rsi = the start block;
 *     %rsp = 8 (mod 16) at the first instruction, %rbp = 0, the %fs base =
 *     the TCB.
 *   AArch64: x0 = the TCB, x1 = the start block.
 *
 * Rules for the kernel:
 * - Every unit gets a valid start block, also a unit that has no start
 *   argument: then n_words is 0. The register never holds garbage.
 * - The block stays mapped, readable and unchanged from entry until the
 *   program exits. Compiled code reads the words in place and never writes
 *   the block; the kernel may map it read-only.
 *
 * What a unit with a start argument does with the block: it stops (a trap
 * instruction) if the pointer is null, magic is not kSccStartMagic, version
 * is not kSccStartVersion, or n_words differs from the word count of its
 * compiled start type. It reads nothing else of the header.
 * -------------------------------------------------------------------- */

struct SccTcb;  // runtime_x64.h

// The convention raw units use. On x86-64 the stub is built for a target
// whose default is the Microsoft convention (runtime_x64.h).
#ifndef KRAKEN_SCC_ABI
#if defined(__x86_64__)
#define KRAKEN_SCC_ABI __attribute__((sysv_abi))
#else
#define KRAKEN_SCC_ABI
#endif
#endif

struct SccStartBlock;
typedef void (KRAKEN_SCC_ABI *SccRtMainFn)(SccTcb* self, const SccStartBlock* start);

/* ----------------------------------------------------------------------
 * The start block
 *
 * A 64-byte header, then the start argument's words. The words follow the
 * start type's layout: a product left to right, the function packages in
 * the order of the start type, each package's words in SccFnPkg's order.
 *
 * Compiled code relies on magic, version, n_words and on the words starting
 * at byte 64, and on nothing else. A change to any of these, or to the order
 * of the words, needs a new version number. The other header fields are the
 * kernel's own and may change without one.
 * -------------------------------------------------------------------- */

constexpr uint64_t kSccStartMagic = 0x3154525453434353ull;  // "SCCSTRT1"
constexpr uint64_t kSccStartVersion = 1;
constexpr uint64_t kSccStartHeaderBytes = 64;

struct SccStartBlock {
  alignas(64) uint64_t magic;  // kSccStartMagic
  uint64_t version;            // kSccStartVersion
  uint64_t n_words;            // the length of words[]; 0 without a start argument
  uint64_t devobj_lo;          // the kernel's device objects lie in [devobj_lo,
  uint64_t devobj_hi;          //   devobj_hi); compiled code does not read these
  uint64_t reserved[3];        // 0
  uint64_t words[];            // the start argument's words
};
static_assert(offsetof(SccStartBlock, magic) == 0);
static_assert(offsetof(SccStartBlock, version) == 8);
static_assert(offsetof(SccStartBlock, n_words) == 16);
static_assert(offsetof(SccStartBlock, devobj_lo) == 24);
static_assert(offsetof(SccStartBlock, devobj_hi) == 32);
static_assert(offsetof(SccStartBlock, reserved) == 40);
static_assert(offsetof(SccStartBlock, words) == kSccStartHeaderBytes);
static_assert(alignof(SccStartBlock) == 64);

/* ----------------------------------------------------------------------
 * A function package: one PCI function, as words of the start argument
 *
 * The word order below is agreed with the language side (WeakCore's planned
 * window types); it is not in a WeakCore release yet. When interrupt lines
 * are added they will follow cfg, and the 57 words here keep their places.
 *
 * What the kernel fills in, and vouches for (nothing checks it):
 * - dev: the address of the kernel's device object for this function.
 *   Non-zero. Device objects never move.
 * - bar[i][k]: piece k of memory BAR i. A piece is a window onto the BAR
 *   outside the MSI-X table and pending-bit array, which the kernel cuts
 *   out by exact byte ranges, so a BAR has at most three pieces. bar_off is
 *   the piece's offset within its BAR. A piece's base is a multiple of 8.
 * - A 64-bit BAR sits in the slot of its lower number. Its upper slot,
 *   absent BARs, port I/O BARs and unused pieces are {0, 0, 0}: an empty
 *   window with base 0.
 * - cfg: the function's 4096 bytes of configuration space (its ECAM page),
 *   read-only for the program. Its base is a multiple of 4096.
 * - For every window, base + len is less than 2^64. All windows of a start
 *   are pairwise disjoint, and windows of different devices do not overlap.
 * - Mappings: BAR pieces uncached, non-executable, readable and writable,
 *   prefetchable BARs included (never write-combining or write-back); the
 *   configuration window uncached, non-executable, read-only.
 * -------------------------------------------------------------------- */

typedef uint64_t SccDevHandle;  // the address of a device object

struct SccWindow {
  uint64_t base;  // virtual address of the first byte
  uint64_t len;   // length in bytes; 0 for an empty window
};

struct SccBarPiece {
  SccWindow w;
  uint64_t bar_off;  // offset of w.base within its BAR
};

constexpr uint64_t kSccPciBars = 6;
constexpr uint64_t kSccPiecesPerBar = 3;
constexpr uint64_t kSccCfgWindowBytes = 4096;
constexpr uint64_t kSccBarPieceAlign = 8;
constexpr uint64_t kSccCfgWindowAlign = 4096;

struct SccFnPkg {
  SccDevHandle dev;
  SccBarPiece bar[kSccPciBars][kSccPiecesPerBar];
  SccWindow cfg;
};
constexpr uint64_t kSccFnPkgWords = 57;
static_assert(sizeof(SccWindow) == 16);
static_assert(sizeof(SccBarPiece) == 24);
static_assert(offsetof(SccFnPkg, bar) == 8);
static_assert(offsetof(SccFnPkg, cfg) == 8 * (1 + 6 * 3 * 3));
static_assert(sizeof(SccFnPkg) == 8 * kSccFnPkgWords);
static_assert(alignof(SccFnPkg) == 8);

#endif  // KRAKEN_EFI_START_H_
