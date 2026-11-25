/*
 * Kraken EFI stub, x86-64: the host side of scc's raw ABI (runtime_x64.h).
 */
#include "runtime_x64.h"
#include "start.h"  // compiled for its layout checks; not used yet
#include "x64.h"
#include "debug.h"
#include "stub.h"  // halt_forever

/* scc's object header (Scc/Config.lean, ObjLayout; Scc/Lower/Obj.lean): the
   kind and the collector's bits, then the scalar word count n, the trace word
   count m and the element count len, for the default layout (the header
   between the regions, [trace][header][scalars]). */
constexpr unsigned kHeaderNShift = 3 + 5;
constexpr unsigned kHeaderNBits = 14;
constexpr unsigned kHeaderMShift = kHeaderNShift + kHeaderNBits;
constexpr unsigned kHeaderMBits = 14;
constexpr unsigned kHeaderLenShift = kHeaderMShift + kHeaderMBits;
constexpr unsigned kHeaderLenBits = 28;

/* scc_rt_alloc(h, k, u): an object of k elements with header h (length 0),
   as scc's allocator lays it out (Scc/Lower/Runtime.lean, allocF): the k*m
   trace words, the header h | k << len, then the k*n scalar words; the
   result is the base, the first scalar word. Bump-allocated from the current
   CPU's small_alloc_slab, never freed, and zeroed, as scc requires. Each
   object takes a multiple of 16 bytes, as scc's 16-byte cells do. u is the
   allocation's source units, which only scc's heap limit counts; the slab's
   limit is the limit here. Per CPU and not atomic: nothing else allocates
   from this CPU's slab. */
KRAKEN_SCC_ABI uint64_t SccRtAlloc(uint64_t h, uint64_t k, uint64_t u) {
  // TODO: small_alloc_slab is probably not right here.
  (void)u;
  if (k >= (uint64_t{1} << kHeaderLenBits)) {
    PANIC("scc_rt_alloc: too many elements");
  }
  uint64_t n = (h >> kHeaderNShift) & ((uint64_t{1} << kHeaderNBits) - 1);
  uint64_t m = (h >> kHeaderMShift) & ((uint64_t{1} << kHeaderMBits) - 1);
  uint64_t trace_bytes = 8 * k * m;
  uint64_t bytes = (8 * (1 + k * (n + m)) + 15) & ~uint64_t{15};
  uint64_t slab = readgsqword(offsetof(Cpu, small_alloc_slab));
  uint64_t limit = readgsqword(offsetof(Cpu, small_alloc_slab_limit));
  if (bytes > limit - slab) {
    PANIC("scc_rt_alloc: the small alloc slab is exhausted");
  }
  writegsqword(offsetof(Cpu, small_alloc_slab), slab + bytes);
  uint64_t* words = reinterpret_cast<uint64_t*>(slab);
  for (uint64_t i = 0; i < bytes / 8; ++i) words[i] = 0;
  words[trace_bytes / 8] = h | (k << kHeaderLenShift);
  return slab + trace_bytes + 8;
}

KRAKEN_SCC_ABI void SccRtAllocTcb() {
  PANIC("SccRtAllocTcb");
}

/* scc_rt_print(p, n): the n bytes from p, to the serial port and the screen
   (DisplayChars). On Linux, scc's write loop; there is no error to report
   here. */
KRAKEN_SCC_ABI void SccRtPrint(const uint8_t* p, uint64_t n) {
  DisplayChars(reinterpret_cast<const char*>(p), n);
}

KRAKEN_SCC_ABI void SccRtPark() {
  PANIC("SccRtPark");
}

KRAKEN_SCC_ABI void SccRtUnpark() {
  PANIC("SccRtUnpark");
}

KRAKEN_SCC_ABI void SccRtAbort() {
  PANIC("SccRtAbort");
}

KRAKEN_SCC_ABI void SccRtExitThread() {
  PANIC("SccRtExitThread");
}

/* scc_rt_exit_process(status): main's result (on Linux, exit_group, which
   keeps status mod 256). There is no process to return to: report the
   status and halt this CPU, with interrupts masked. */
[[noreturn]] KRAKEN_SCC_ABI void SccRtExitProcess(uint64_t status) {
  DisplayString("scc_rt_exit_process: status ");
  DisplayUint64(status);
  DisplayString("\n");
  DebugSetIdleStatus();
  halt_forever();
}

KRAKEN_SCC_ABI void SccRtStackTake() {
  PANIC("SccRtStackTake");
}

KRAKEN_SCC_ABI void SccRtStackRelease() {
  PANIC("SccRtStackRelease");
}

KRAKEN_SCC_ABI void SccRtGrow() {
  PANIC("SccRtGrow");
}

KRAKEN_SCC_ABI void SccRtThreadReserve() {
  PANIC("SccRtThreadReserve");
}

KRAKEN_SCC_ABI void SccRtThreadInit() {
  PANIC("SccRtThreadInit");
}

KRAKEN_SCC_ABI void SccRtSpawn() {
  PANIC("SccRtSpawn");
}

/* The kernel's routines, in SccKabiSlot order: what FillUnitKabi copies
   into each unit's table. */
#define KABI(f) reinterpret_cast<const void*>(&f)
const SccKabi gKabi = {{
    KABI(SccRtAlloc),        KABI(SccRtAllocTcb),     KABI(SccRtPrint),
    KABI(SccRtPark),         KABI(SccRtUnpark),       KABI(SccRtAbort),
    KABI(SccRtExitThread),   KABI(SccRtExitProcess),  KABI(SccRtStackTake),
    KABI(SccRtStackRelease), KABI(SccRtGrow),         KABI(SccRtThreadReserve),
    KABI(SccRtThreadInit),   KABI(SccRtSpawn),
}};
#undef KABI

bool CheckUnitKabi(const SccUnitKabi* table) {
  if (table->magic != kSccUnitKabiMagic) {
    DisplayString("raw unit refused: no routine table (magic SCCKABI1) at the "
                  "start of its writable segment\n");
    return false;
  }
  if (table->slot_count == 0 || table->slot_count > kSccKabiSlotCount) {
    DisplayString("raw unit refused: its routine table uses 0x");
    DisplayUint64(table->slot_count);
    DisplayString(" slots; this kernel has 1 to 0x");
    DisplayUint64(kSccKabiSlotCount);
    DisplayString("\n");
    return false;
  }
  for (uint64_t i = 0; i < table->slot_count; ++i) {
    if (table->routine[i] != nullptr) {
      DisplayString("raw unit refused: routine word 0x");
      DisplayUint64(i);
      DisplayString(" of its routine table is not zero in the file\n");
      return false;
    }
  }
  return true;
}

void FillUnitKabi(SccUnitKabi* table) {
  for (uint64_t i = 0; i < table->slot_count; ++i) {
    table->routine[i] = gKabi.routine[i];
  }
}

extern "C" void RuntimeEnterThread();

uint64_t XsaveAreaBytes() {
  uint32_t eax, ebx, ecx, edx;
  __cpuid_count(0xD, 0, eax, ebx, ecx, edx);
  return ebx;
}

/* The XSAVE image a new thread starts from (RuntimeEnterThread's xrstor64).
   With the header's XSTATE_BV (offset 512) zero, XRSTOR puts every enabled
   component in its initial state: for x87 that is FNINIT's (control word
   0x037F, all exceptions masked). MXCSR is the exception: XRSTOR loads it
   from the legacy area whenever SSE or AVX is requested, so it gets its
   reset value 0x1F80 there (all SSE exceptions masked; zero would unmask
   them). The rest of the area, the header's reserved bytes included, must be
   zero, or XRSTOR faults (Intel SDM vol. 1, 13.8). */
constexpr uint32_t kXsaveMxcsrDefault = 0x1F80;  // MXCSR's reset value
constexpr uint64_t kXsaveMxcsrOffset = 24;       // in the legacy (FXSAVE) area
constexpr uint64_t kXsaveLegacyAndHeaderBytes = 512 + 64;

static void InitXsave(uint8_t* area, uint64_t bytes) {
  // TODO: this should not be necessary if the thread slab is zeroed
  for (uint64_t i = 0; i < bytes; ++i) area[i] = 0;
  *reinterpret_cast<uint32_t*>(area + kXsaveMxcsrOffset) = kXsaveMxcsrDefault;
}

SccTcb* AllocThread(const void* entry) {
  // Each thread takes one slot of the CPU's thread slab: its TCB (with its
  // XSAVE area) at the bottom, then its stack, growing down from the top of
  // the slot.
  constexpr uint64_t kThreadSlotBytes = 0x4000;
  uint64_t xsave_bytes = XsaveAreaBytes();
  if (xsave_bytes < kXsaveLegacyAndHeaderBytes) {
    PANIC("XSAVE area smaller than its legacy area and header");
  }
  // 16-byte aligned, as scc's stack is.
  uint64_t tcb_bytes = (sizeof(SccTcb) + xsave_bytes + 15) & ~uint64_t{15};
  if (tcb_bytes + kSccTcbHeadroom >= kThreadSlotBytes) {
    PANIC("thread slot too small for the TCB and the stack headroom");
  }
  uint64_t thread_base = readgsqword(offsetof(Cpu, thread_slab));
  uint64_t thread_limit = readgsqword(offsetof(Cpu, thread_slab_limit));
  if (thread_base + kThreadSlotBytes > thread_limit) {
    PANIC("not enough room to alloc thread");
  }
  SccTcb* new_thread = (SccTcb*)thread_base;
  if (thread_base % alignof(SccTcb) != 0) {
    PANIC("would allocate a TCB that is not 64-byte aligned");
  }
  writegsqword(offsetof(Cpu, thread_slab), thread_base + kThreadSlotBytes);
  new_thread->self = reinterpret_cast<uint64_t>(new_thread);
  // scc's stack fields (Scc/IR/Core.lean, Tcb): the range is
  // [stack_base, stack_top), from just past the TCB to the top of the slot,
  // and stack_limit leaves kSccTcbHeadroom bytes above stack_base for the
  // paths that run without a stack check.
  new_thread->stack_base = thread_base + tcb_bytes;
  new_thread->stack_top = thread_base + kThreadSlotBytes;
  new_thread->stack_limit = new_thread->stack_base + kSccTcbHeadroom;
  new_thread->gprs.rsp = new_thread->stack_top;
  new_thread->index = 0;
  new_thread->kabi = nullptr;  // reserved (SccUnitKabi)
  new_thread->rip = reinterpret_cast<uint64_t>(entry);
  InitXsave(new_thread->xsave, xsave_bytes);
  return new_thread;
}

void EnterThread(SccTcb* tcb) {
  wrmsr(kFsBaseMSR, (uint64_t)tcb);
  tcb->rflags = 0x202;
  RuntimeEnterThread();
}
