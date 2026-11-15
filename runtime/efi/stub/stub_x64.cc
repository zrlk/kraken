/*
 * Kraken EFI stub, x86-64 part (see stub.cc): the AP startup code, port I/O,
 * TSC calibration (InitPlatform) and the final halt (entry.asm).
 */
#include "acpi.h"
#include "pci.h"
#include "stub.h"
#include "x64_mmu.h"
#include "x64.h"
#include "runtime_x64.h"
#include "debug.h"

/* entry.asm (NASM): cli, then hlt in a loop. */
extern "C" [[noreturn]] void kraken_halt();

void halt_forever() { kraken_halt(); }

extern "C" [[noreturn]] void EnterRuntime(uint64_t gcpus_addr, uint64_t cpu_record_size);

#if !defined(KRAKEN_AP_ENTRY)
#error "build with runtime/efi/build.sh: it defines the AP startup code's path"
#endif
__asm__(
    ".section .rdata,\"dr\"\n"
    ".p2align 4\n"
    ".globl ApBootstrap\n"
    "ApBootstrap:\n"
    ".incbin \"" KRAKEN_AP_ENTRY
    "\"\n"
    ".globl ApBootstrapEnd\n"
    "ApBootstrapEnd:\n"
    ".text\n");
extern "C" const uint8_t ApBootstrap[];
extern "C" const uint8_t ApBootstrapEnd[];

/* Scc/Test/elf/hello1rawx64/hello1, the ELF executable of `scc --host raw` for
   hello1.w (uncertified; see Scc/RELEASE.md), whose path build.sh passes:
   Hello1Raw to Hello1RawEnd, read-only, the file byte for byte. 16 KiB
   aligned (kHello1RawAlign), so its segments (at file offsets 0x10000 and
   0x20000, linked by Scc/Test/elf/raw.ld) stay 16 KiB aligned in the buffer
   and can be mapped in place. The offset in the image is aligned here; the
   load address is aligned by linking the x64 image with /align:16384
   (build.sh), whose section alignment edk2 honours when it places the image,
   and InitPlatform checks it (CheckHello1RawAligned). As with ApBootstrap,
   take the length as Hello1RawEnd - Hello1Raw where it is used. */
#if !defined(KRAKEN_HELLO1_RAW)
#error "build with runtime/efi/build.sh: it defines the raw hello1 executable's path"
#endif
__asm__(
    ".section .rdata,\"dr\"\n"
    ".p2align 14\n"  // kHello1RawAlign
    ".globl Hello1Raw\n"
    "Hello1Raw:\n"
    ".incbin \"" KRAKEN_HELLO1_RAW
    "\"\n"
    ".globl Hello1RawEnd\n"
    "Hello1RawEnd:\n"
    ".text\n");
extern "C" const uint8_t Hello1Raw[];
extern "C" const uint8_t Hello1RawEnd[];
constexpr uint64_t kHello1RawAlign = 16384;

// The entry point of Hello1Raw (scc_rt_main: raw.ld's ENTRY), as a pointer
// into the buffer, or nullptr if the ELF header or segments don't fit. The
// entry is e_entry, a virtual address; the PT_LOAD segment holding it maps it
// to its file offset (0x100b5 for the checked-in file). The buffer's segments
// keep their relative layout, so code there finds the rest of the unit where
// raw.ld put it, as long as it is mapped executable.
static const uint8_t* Hello1RawEntry() {
  const uint8_t* b = Hello1Raw;
  uint64_t size = Hello1RawEnd - Hello1Raw;
  auto u16 = [&](uint64_t o) { return *reinterpret_cast<const uint16_t*>(b + o); };
  auto u32 = [&](uint64_t o) { return *reinterpret_cast<const uint32_t*>(b + o); };
  auto u64 = [&](uint64_t o) { return *reinterpret_cast<const uint64_t*>(b + o); };
  if (size < 64 || u32(0) != 0x464C457F) return nullptr;  // "\x7fELF"
  uint64_t entry = u64(0x18), phoff = u64(0x20);
  uint16_t phentsize = u16(0x36), phnum = u16(0x38);
  for (uint16_t i = 0; i < phnum; ++i) {
    uint64_t ph = phoff + uint64_t{i} * phentsize;
    if (ph + 56 > size) return nullptr;
    if (u32(ph) != 1) continue;  // PT_LOAD
    uint64_t offset = u64(ph + 8), vaddr = u64(ph + 16), filesz = u64(ph + 32);
    if (entry >= vaddr && entry < vaddr + filesz && offset + filesz <= size)
      return b + offset + (entry - vaddr);
  }
  return nullptr;
}

// various of methods to read the tsc frequency. we need to know this because
// we need to be able to pause for precise amounts of time when eg initializing
// application processors. automation helpfully provided the cpuid variant after
// my old code didn't work, but then it turned out that was a different bug and
// qemu doesn't do the cpuid one anyway (?)
static uint64_t CpuidTicksPerSecond() {
  uint32_t max_leaf, ebx, ecx, edx;
  __cpuid(0, max_leaf, ebx, ecx, edx);
  if (max_leaf < 0x15) return 0;
  uint32_t denominator, numerator, crystal_hz;
  __cpuid(0x15, denominator, numerator, crystal_hz, edx);
  if (denominator == 0 || numerator == 0) return 0;
  if (crystal_hz != 0) {
    return static_cast<uint64_t>(crystal_hz) * numerator / denominator;
  }
  if (max_leaf < 0x16) return 0;
  uint32_t base_mhz;
  __cpuid(0x16, base_mhz, ebx, ecx, edx);
  return static_cast<uint64_t>(base_mhz & 0xFFFF) * 1000000;
}

// TSC ticks per second and per microsecond (CalibrateTicks).
uint64_t gTicksPerSecond = 0;
uint64_t gTicksPerUsec = 0;
uint64_t gTickSource = 0;

constexpr uint64_t kPitHz = 1193182;
// 11931 PIT clocks: 9.9993 ms.
constexpr uint16_t kPitCount = kPitHz / 100;
// Give up on the PIT after this many TSC ticks (at least 1 s for any TSC up
// to 10 GHz): firmware can clock-gate or disable the 8254.
constexpr uint64_t kPitTimeout = 10'000'000'000;

// A TSC slower than this means the PIT did not really count.
constexpr uint64_t kMinTicksPerSecond = 100'000'000;

// TSC ticks over kPitCount clocks of PIT channel 2, or 0 if the PIT is not
// counting: OUT already high after the count is loaded (no PIT: QEMU with
// pit=off reads it high), no terminal count within kPitTimeout, or an
// implausibly short interval.
static uint64_t MeasurePit() {
  // Channel 2's gate on, its speaker output off.
  outb(0x61, (inb(0x61) & 0xFD) | 1);
  // Channel 2, low then high byte, mode 0 (interrupt on terminal count),
  // binary. OUT goes low when the count is written and high when it reaches
  // zero; no gate edge is needed to start it. The PIT takes the two count
  // bytes back to back, without a delay between them.
  outb(0x43, 0xB0);
  outb(0x42, kPitCount & 0xFF);
  outb(0x42, kPitCount >> 8);
  uint64_t start = rdtsc();
  // OUT is bit 5 of port 0x61. In mode 0 it is low from the control word
  // on, so high here means the PIT is not counting.
  if ((inb(0x61) & 0x20) != 0) return 0;
  while ((inb(0x61) & 0x20) == 0) {
    if (rdtsc() - start > kPitTimeout) return 0;
  }
  uint64_t ticks = rdtsc() - start;
  if (ticks * kPitHz / kPitCount < kMinTicksPerSecond) return 0;
  return ticks;
}

// try cpuid first, then the pit, then finally efi Stall (since we can
// still touch boot services at this point)
void CalibrateTicks(EFI_BOOT_SERVICES* bs) {
  uint64_t cpuid_hz = CpuidTicksPerSecond();
  if (cpuid_hz >= kMinTicksPerSecond) {
    gTicksPerSecond = cpuid_hz;
    gTicksPerUsec = gTicksPerSecond / 1000000;
    return;
  }
  gTickSource = 1;
  uint64_t best = 0;
  EFI_TPL old_tpl = bs->RaiseTPL(TPL_HIGH_LEVEL);
  for (int i = 0; i < 3; i++) {
    uint64_t ticks = MeasurePit();
    if (ticks == 0) {
      best = 0;
      break;
    }
    if (best == 0 || ticks < best) best = ticks;
  }
  bs->RestoreTPL(old_tpl);
  if (best != 0) {
    gTicksPerSecond = best * kPitHz / kPitCount;
  } else {
    uint64_t start = rdtsc();
    bs->Stall(10000);  // 10 ms
    gTicksPerSecond = (rdtsc() - start) * 100;
    gTickSource = 2;
  }
  gTicksPerUsec = gTicksPerSecond / 1000000;
}

MADT* gMadt = nullptr;
DMAR* gDmar = nullptr;
MCFG* gMcfg = nullptr;

EFI_STATUS GetACPITables(EFI_SYSTEM_TABLE* system_table) {
  struct EfiGuid {
    uint32_t a;
    uint16_t b, c;
    uint8_t d[8];
    bool IsGuid(const EFI_GUID& guid) const {
      return a == guid.Data1 && b == guid.Data2 && c == guid.Data3;
    }
  };
  constexpr auto acpi20_guid = EfiGuid ACPI_20_TABLE_GUID;
  void* acpi20_rsdp = nullptr;
  for (UINTN i = 0; i < system_table->NumberOfTableEntries; ++i) {
    const auto& guid = system_table->ConfigurationTable[i].VendorGuid;
    if (acpi20_guid.IsGuid(guid)) {
      acpi20_rsdp = system_table->ConfigurationTable[i].VendorTable;
    }
  }
  DV(acpi20_rsdp);
  if (acpi20_rsdp == nullptr) {
    EFIConOut(system_table, "Can't find RSDP\r\n");
    return EFI_INVALID_PARAMETER;
  }
  const XSDP* xsdp = (const XSDP*)(acpi20_rsdp);
  const char* xsdp_raw = (const char*)xsdp;
  uint8_t checksum = 0;
  for (int i = 0; i < 20; ++i) checksum += xsdp_raw[i];
  if (checksum != 0) {
    EFIConOut(system_table, "xsdp checksum #1 bad\r\n");
    return EFI_INVALID_PARAMETER;
  }
  for (int i = 0; i < 16; ++i) checksum += xsdp_raw[i + 20];
  if (checksum != 0) {
    EFIConOut(system_table, "xsdp checksum #2 bad\r\n");
    return EFI_INVALID_PARAMETER;
  }
  uint64_t num_tables = (xsdp->xsdt->header.length - sizeof(SDTHeader)) / 8;
  for (uint64_t i = 0; i < num_tables; ++i) {
    const char* sig = xsdp->xsdt->sdt[i]->signature;
    if (FourCCMatch(sig, "APIC")) {
      gMadt = (MADT*)xsdp->xsdt->sdt[i];
    }
    if (FourCCMatch(sig, "DMAR")) {
      gDmar = (DMAR*)xsdp->xsdt->sdt[i];
    }
    if (FourCCMatch(sig, "MCFG")) {
      gMcfg = (MCFG*)xsdp->xsdt->sdt[i];
    }
  }
  if (gMadt == nullptr) {
    EFIConOut(system_table, u"missing madt\r\n");
    return EFI_INVALID_PARAMETER;
  }
  if (gMcfg == nullptr) {
    EFIConOut(system_table, u"missing mcfg\r\n");
    return EFI_INVALID_PARAMETER;
  }
  if (gDmar == nullptr) {
    EFIConOut(system_table, u"missing dmar\r\n");
    return EFI_INVALID_PARAMETER;
  }
  DV(gMadt);
  DV(gDmar);
  DV(gMcfg);
  return EFI_SUCCESS;
}

/* The start of the image, as loaded: the linker's symbol (lld-link). */
extern "C" const uint8_t __ImageBase[];

/* Code that uses 32-bit absolute addresses (jmp targets, for one) needs the
   whole image below 4 GB. build.sh links the image at a base below 4 GB,
   which EDK2-based firmware tries first, but firmware may still load it
   elsewhere: fail rather than run there. The image's size is SizeOfImage in
   its PE32+ header, which is loaded with it. */
// nb: we probably don't care about this anymore because we switched to
// passing in a vtable of runtime functions in the tcb
static EFI_STATUS CheckLoadedBelow4G(EFI_SYSTEM_TABLE* system_table) {
  uint64_t image_base = reinterpret_cast<uint64_t>(__ImageBase);
  uint32_t pe = *reinterpret_cast<const uint32_t*>(__ImageBase + 0x3C);
  /* PE signature (4) + COFF header (20), then SizeOfImage at 56. */
  uint32_t image_size =
      *reinterpret_cast<const uint32_t*>(__ImageBase + pe + 24 + 56);
  uint64_t image_end = image_base + image_size;
  DV(image_base);
  DV(image_end);
  if (image_end > 0x100000000ULL) {
    EFIConOut(system_table, u"the stub is loaded above 4 GB\r\n");
    return EFI_LOAD_ERROR;
  } else {
    EFIConOut(system_table, u"the stub is loaded at ");
    EFIConOut(system_table, image_base);
    EFIConOut(system_table, u"\r\n");
  }
  return EFI_SUCCESS;
}

/* The firmware picks the load address; Hello1Raw is aligned only if it kept
   the image's section alignment (see Hello1Raw). */
// nb: we care that the image is severely aligned because we use that to get
// access to the descriptor table for the program granule (by stuffing a pointer
// at the very end). as it turns out we have to break long procedures anyhow,
// since that would be a way to starve the collector, so everyone wins (loses)!
static EFI_STATUS CheckHello1RawAligned(EFI_SYSTEM_TABLE* system_table) {
  uint64_t hello1_raw = reinterpret_cast<uint64_t>(Hello1Raw);
  DV(hello1_raw);
  if (hello1_raw % kHello1RawAlign != 0) {
    EFIConOut(system_table, u"Hello1Raw is not 16 KiB aligned\r\n");
    return EFI_LOAD_ERROR;
  }
  return EFI_SUCCESS;
}

EFI_STATUS InitPlatform(EFI_SYSTEM_TABLE* system_table, uint64_t* bootstrap_length) {
  auto s4 = CheckLoadedBelow4G(system_table);
  if (EFI_ERROR(s4)) {
    return s4;
  }
  auto sa = CheckHello1RawAligned(system_table);
  if (EFI_ERROR(sa)) {
    return sa;
  }
  CalibrateTicks(system_table->BootServices);
  DV(gTicksPerSecond);
  DV(gTicksPerUsec);
  DV(gTickSource);
  auto s = GetACPITables(system_table);
  if (EFI_ERROR(s)) {
    return s;
  }
  *bootstrap_length = ApBootstrapEnd - ApBootstrap;
  return EFI_SUCCESS;
}

// These offsets are used in asm.
static_assert(offsetof(Cpu, stack_top) == 0);
static_assert(offsetof(Cpu, tss) == 8);

/// All known cpus, indexed by lapic ID.
// TODO: there can be several more of these now
Cpu gCpus[256];
volatile uint64_t gAwakeCpus;
volatile uint64_t* gBootstrapDebugCounter;

void SetupBootstrap() {
  auto root_page_table = GetRootPageTable();
  if ((uint64_t)root_page_table >= 0x100000000) {
    PANIC("root_page_table is out of range");
  }
  uint8_t* d = (uint8_t*)memcpy((void*)gApBootstrapAddress, &ApBootstrap,
                                &ApBootstrapEnd[0] - &ApBootstrap[0]);
  while (d < &ApBootstrapEnd[0]) {
    auto* d64 = (uint64_t*)d;
    if (*d64 == 0xDEADBEEFBAADF00D) {
      gBootstrapDebugCounter = (d64 - 1);
      *d64++ = (uint64_t)root_page_table;
      *d64++ = (uint64_t)&gAwakeCpus;
      *d64++ = (uint64_t)EnterRuntime;
      *d64++ = (uint64_t)&gCpus[0];
      *d64++ = (uint64_t)sizeof(gCpus[0]);
      return;
    }
    ++d;
  }
  PANIC("Could not find bootstrap code");
}

void MapRuntimeStartImage() {
}

uint8_t ConfigureBspLapic() {
  uint64_t lapic_base_phy = rdmsr(kApicBaseMsr);
  wrmsr(kApicBaseMsr, (lapic_base_phy & ~0xFFFFULL) | kApicBaseMsrEnable);
  auto lapic_vaddr = AllocateVirtualAddress(1);
  auto lapic_base =
      (volatile uint32_t*)Map4kPage(lapic_vaddr, lapic_base_phy, true, true);
  // auto lapic_version = lapic_base[kLapicVersion];
  // auto lapic_version_s = (LocalApicVersion*)&lapic_version;
  uint8_t bsp_id;
  uint32_t eax, ebx, ecx, edx;
  __cpuid(1, eax, ebx, ecx, edx);
  bsp_id = ebx >> 24;  // initial APIC ID: EBX bits 31:24
  gCpus[bsp_id].is_bsp = true;
  gCpus[bsp_id].lapic = lapic_base;
  return bsp_id;
}

extern "C" {
uint64_t* gCurrentGDT;
size_t gCurrentGDTSize;
uint64_t* gLongModeGDTP;
InterruptDescriptor64* gLongModeIDT;
uint64_t* gLongModeIDTP;
#define ISR_NN(f, n) f(InitIsr##n)
#define ISR_EXT_P(f, px) \
  ISR_NN(f, px##0)       \
  ISR_NN(f, px##1)       \
  ISR_NN(f, px##2)       \
  ISR_NN(f, px##3)       \
  ISR_NN(f, px##4)       \
  ISR_NN(f, px##5)       \
  ISR_NN(f, px##6)       \
  ISR_NN(f, px##7) ISR_NN(f, px##8) ISR_NN(f, px##9)
#define ISR_ALL(f) \
  ISR_NN(f, 0)     \
  ISR_NN(f, 1)     \
  ISR_NN(f, 2)     \
  ISR_NN(f, 3)     \
  ISR_NN(f, 4)     \
  ISR_NN(f, 5)     \
  ISR_NN(f, 6)     \
  ISR_NN(f, 7)     \
  ISR_NN(f, 8)     \
  ISR_NN(f, 9)     \
  ISR_EXT_P(f, 1)  \
  ISR_EXT_P(f, 2)  \
  ISR_EXT_P(f, 3)  \
  ISR_EXT_P(f, 4)  \
  ISR_EXT_P(f, 5)  \
  ISR_EXT_P(f, 6)  \
  ISR_EXT_P(f, 7)  \
  ISR_EXT_P(f, 8)  \
  ISR_EXT_P(f, 9)  \
  ISR_EXT_P(f, 10) \
  ISR_EXT_P(f, 11) \
  ISR_EXT_P(f, 12) \
  ISR_EXT_P(f, 13) \
  ISR_EXT_P(f, 14) \
  ISR_EXT_P(f, 15) \
  ISR_EXT_P(f, 16) \
  ISR_EXT_P(f, 17) \
  ISR_EXT_P(f, 18) \
  ISR_EXT_P(f, 19) \
  ISR_EXT_P(f, 20) \
  ISR_EXT_P(f, 21) \
  ISR_EXT_P(f, 22) \
  ISR_EXT_P(f, 23) \
  ISR_EXT_P(f, 24) \
  ISR_NN(f, 250)   \
  ISR_NN(f, 251) ISR_NN(f, 252) ISR_NN(f, 253) ISR_NN(f, 254) ISR_NN(f, 255)
#define ISR_DECL(n) extern uint64_t n;
ISR_ALL(ISR_DECL)
#define ISR_MKARR(n) &n,
};

uint64_t trips = 0;

extern "C" void InterruptStub(uint64_t vector) {
  if (vector == 32) {
    // lapic timer vector
    auto lapic_id = readgsqword(offsetof(Cpu, lapic_id));
    auto lapic = (uint32_t* volatile)readgsqword(offsetof(Cpu, lapic));
    // ever_tripped |= (1ULL << lapic_id);
    if (lapic_id == gCpus[0].lapic_id) {
      // DisplayString("lapic timer on proc 0 tripped: ");
      // DisplayUint64(trips++);
      // DisplayString("\n");
      // SV(&vector);
      // SV(&lapic);
      // DV(vector);
      // DV(trips++);
      // DV(ever_tripped);
      // DV(((uint64_t*)bfi::video_base)[318]);
    }
    lapic[kLapicTimerInitialCount] = 1;
    lapic[kLapicEndOfInterrupt] = 0;
  } else if (vector > 32) {
    for (;;) {
      auto lapic_id = readgsqword(offsetof(Cpu, lapic_id));
      DisplayString("Unexpected vector ");
      DisplayUint64(vector);
      DisplayString(" on lapic ");
      DisplayUint64(lapic_id);
      DisplayString("\n");
    }
  } else {
    for (;;) {
      //SV(vector);
      DisplayString("Unexpected vector ");
      DisplayUint64(vector);
      DisplayString("\n");
    }
  }
}

void SetupCommonTables() {
  auto table_page = AllocateVirtualAddress(1);
  auto table_phy = AllocatePages(1);
  void* tables = Map4kPage(table_page, table_phy, false, false);
  gCurrentGDT = (uint64_t*)tables;
  gCurrentGDT[0] = 0;
  gCurrentGDT[1] = 0x00209A0000000000ULL;
  gCurrentGDT[2] = 0x0000920000000000ULL;
  gCurrentGDTSize = 3;

  auto idt_page = AllocateVirtualAddress(1);
  auto idt_phy = AllocatePages(1);
  auto* idt_base =
      (InterruptDescriptor64*)Map4kPage(idt_page, idt_phy, false, false);
  void* all_isrs[] = {ISR_ALL(ISR_MKARR)};
  for (size_t i = 0; i < 256; ++i) {
    idt_base[i].offset_1 = (uint64_t)all_isrs[i] & 0xFFFF;
    idt_base[i].offset_2 = ((uint64_t)all_isrs[i] >> 16) & 0xFFFF;
    idt_base[i].offset_3 = ((uint64_t)all_isrs[i] >> 32);
    idt_base[i].ist = 1;                 // ist in tss
    idt_base[i].selector = 0x8;          // cs
    idt_base[i].type_attributes = 0x8E;  // present | interrupt gate
  }
  gLongModeIDT = idt_base;
}

void AllocEarlySlab(size_t pages, uint8_t** slab, uint8_t** slab_limit) {
  auto small_alloc_page = AllocateVirtualAddress(16);
  auto small_alloc_phy = AllocatePages(16);
  for (size_t s = 0; s < pages; ++s) {
    Map4kPage(small_alloc_page + s * 4096, small_alloc_phy + s * 4096, false,
              false);
  }
  *slab = (uint8_t*)small_alloc_page;
  *slab_limit = *slab + pages * 4096;
}

void SetupStacksAndTables(Cpu& cpu) {
  if (gCurrentGDTSize + 2 > 0x1000 / 8) {
    PANIC("GDT too big.");
  }
  constexpr size_t kStackPages = 0x10;
  auto stack_bottom = AllocateVirtualAddress(kStackPages);
  auto stack_phy = AllocatePages(kStackPages);
  for (size_t s = 0; s < kStackPages; ++s) {
    Map4kPage(stack_bottom + s * 4096, stack_phy + s * 4096, false, false);
  }
  cpu.stack_top = stack_bottom + kStackPages * 4096;

  constexpr size_t kIsrStackPages = 0x10;
  auto isr_stack_bottom = AllocateVirtualAddress(kIsrStackPages);
  auto isr_stack_phy = AllocatePages(kIsrStackPages);
  for (size_t s = 0; s < kIsrStackPages; ++s) {
    Map4kPage(isr_stack_bottom + s * 4096, isr_stack_phy + s * 4096, false,
              false);
  }
  cpu.isr_stack_top = isr_stack_bottom + kIsrStackPages * 4096;

  auto table_page = AllocateVirtualAddress(1);
  auto table_phy = AllocatePages(1);
  void* tables = Map4kPage(table_page, table_phy, false, false);
  auto* tss = (TaskStateSegment*)tables;
  tss->iopb = sizeof(TaskStateSegment);
  tss->rsp[0].low = cpu.stack_top;
  tss->rsp[0].high = cpu.stack_top >> 32;
  tss->ist[0].low = cpu.isr_stack_top;
  tss->ist[0].high = cpu.isr_stack_top >> 32;
  cpu.tss = gCurrentGDTSize * 8;
  auto tss_int = (uint64_t)tss;
  static_assert(sizeof(TaskStateSegment) - 1 < 0xFFFF);

  gCurrentGDT[gCurrentGDTSize] = (sizeof(TaskStateSegment) - 1);
  gCurrentGDT[gCurrentGDTSize] |= (tss_int & 0xFFFF) << 16;
  gCurrentGDT[gCurrentGDTSize] |= ((tss_int >> 16) & 0xFF) << 32;
  gCurrentGDT[gCurrentGDTSize] |= ((tss_int >> 24) & 0xFF) << 56;
  gCurrentGDT[gCurrentGDTSize] |=
      0x89ULL << 40;  // Access byte (Present | Available TSS)
  gCurrentGDT[gCurrentGDTSize + 1] = tss_int >> 32;
  gCurrentGDTSize += 2;

  AllocEarlySlab(10, &cpu.small_alloc_slab, &cpu.small_alloc_slab_limit);
  AllocEarlySlab(10, &cpu.thread_slab, &cpu.thread_slab_limit);
}

void SetupApLapics() {
  const uint8_t* pmax = (uint8_t*)gMadt + gMadt->header.length;
  const uint8_t* p = (uint8_t*)gMadt + sizeof(MADT);
  while (p < pmax) {
    MADTRecord* record = (MADTRecord*)p;
    p += record->length;
    if (record->type == kProcessorLocalAPIC) {
      if ((record->lapic.flags & 1) != 1) {
        continue;
      }
      auto& cpu =gCpus[record->lapic.apic_id];
      cpu.lapic_id = record->lapic.apic_id;
      cpu.cpu_id = record->lapic.processor_id;
      if (!cpu.lapic) {
        auto ap_lapic_vaddr = AllocateVirtualAddress(1);
        cpu.lapic =
            (volatile uint32_t*)Map4kPage(ap_lapic_vaddr, 0, true, true);
      }
      SetupStacksAndTables(cpu);
    }
  }
}

void FinishCommonTables() {
  // [limit:16][base:64], word-aligned.
  uint16_t* uint_tables_limit = (uint16_t*)(&gCurrentGDT[gCurrentGDTSize]);
  *uint_tables_limit = (char*)&gCurrentGDT[gCurrentGDTSize] -
                       (char*)&gCurrentGDT[0];  // TODO: -1? (probably)
  uint64_t* uint_tables_ptr = (uint64_t*)(uint_tables_limit + 1);
  *uint_tables_ptr = (uint64_t)&gCurrentGDT[0];
  gLongModeGDTP = &gCurrentGDT[gCurrentGDTSize];

  uint16_t* idt_limit = (uint16_t*)(gLongModeGDTP + 2);
  // The limit should always be one less than an integral multiple of 8.
  *idt_limit = (char*)&gLongModeIDT[256] - (char*)&gLongModeIDT[0] - 1;
  uint64_t* idt_ptr = (uint64_t*)(idt_limit + 1);
  *idt_ptr = (uint64_t)&gLongModeIDT[0];
  gLongModeIDTP = (uint64_t*)idt_limit;
}

void SetupDMAR() {

}

/// Wait for at least `usecs` usecs.
void WaitUsec(uint64_t usecs) {
  uint64_t tsc = __rdtsc();
  uint64_t acc = 0;
  usecs *= gTicksPerUsec;
  while (acc < usecs) {
    uint64_t new_tsc = __rdtsc();
    if (tsc < new_tsc) {
      acc += (new_tsc - tsc);
    }
    tsc = new_tsc;
    _mm_pause();
  }
}

/// Wait for at least `msecs` msecs.
void WaitMsec(uint64_t msecs) { WaitUsec(msecs * 1000); }

void WakeupAPs(uint8_t bsp_id) {
  gAwakeCpus = 1;  // the BSP is awake
  volatile uint32_t* lapic_base = gCpus[bsp_id].lapic;
  const uint8_t* pmax = (uint8_t*)gMadt + gMadt->header.length;
  const uint8_t* p = (uint8_t*)gMadt + sizeof(MADT);
  uint64_t cpu_count = 0;
  while (p < pmax) {
    MADTRecord* record = (MADTRecord*)p;
    p += record->length;
    if (record->type == kProcessorLocalAPIC) {
      //DV(record->lapic.apic_id);
      //DV(record->lapic.processor_id);
      //DV(record->lapic.flags);
      // if (record->lapic.processor_id == bsp_id) continue;
      if ((record->lapic.flags & 1) != 1) {
        DisplayString("(Processor is not enabled; skipping.)");
        if (record->lapic.apic_id == bsp_id) {
          PANIC("Fatal: boostrap processor is not enabled?");
        }
        continue;
      }
      ++cpu_count;
      if (record->lapic.apic_id == bsp_id) continue;
      // if (record->lapic.apic_id != 1) continue;
      DisplayString("Starting AP.\n");
      // Clear error status.
      lapic_base[kLapicErrorStatus] = 0;
      // Select AP.
      lapic_base[kLapicInterruptCommand1] =
          (lapic_base[kLapicInterruptCommand1] & 0x00ffffff) |
          (record->lapic.apic_id << 24);  // processor_id
      // Trigger INIT IPI.
      lapic_base[kLapicInterruptCommand0] =
          (lapic_base[kLapicInterruptCommand0] & 0xfff00000) | 0x00C500;
      // Wait for delivery.
      DisplayString("Waiting for INIT to be delivered.\n");
      while (lapic_base[kLapicInterruptCommand0] & (1 << 12)) _mm_pause();
      // DV_SPAM(lapic_base[kLapicErrorStatus]);
      WaitMsec(10);  // ?
      // Select AP.
      lapic_base[kLapicInterruptCommand1] =
          (lapic_base[kLapicInterruptCommand1] & 0x00ffffff) |
          (record->lapic.apic_id << 24);  // processor_id
      // Deassert.
      lapic_base[kLapicInterruptCommand0] =
          (lapic_base[kLapicInterruptCommand0] & 0xfff00000) | 0x008500;
      DisplayString("Waiting for INIT (deassert) to be delivered.\n");
      // Wait for delivery.
      while (lapic_base[kLapicInterruptCommand0] & (1 << 12)) _mm_pause();
      WaitMsec(10);
      lapic_base[kLapicErrorStatus] = 0;  // new
      // DV_SPAM(lapic_base[kLapicErrorStatus]);
      // Send STARTUP IPI twice.
      for (int j = 0; j < 2; ++j) {
        // Clear error status.
        lapic_base[kLapicErrorStatus] = 0;
        // Select AP.
        lapic_base[kLapicInterruptCommand1] =
            (lapic_base[kLapicInterruptCommand1] & 0x00ffffff) |
            (record->lapic.apic_id << 24);  // processor_id
        // Trigger STARTUP IPI for 0800:0000
        DisplayString("Sending STARTUP.\n");
        lapic_base[kLapicInterruptCommand0] =
            (lapic_base[kLapicInterruptCommand0] & 0xfff0f800) | 0x000608;
        WaitUsec(200);
        // DV_SPAM(lapic_base[kLapicErrorStatus]);
        DisplayString("Waiting for STARTUP to be delivered.\n");
        // Wait for delivery.
        while (lapic_base[kLapicInterruptCommand0] & (1 << 12)) _mm_pause();
        lapic_base[kLapicErrorStatus] = 0;  // new
        // DV_SPAM(lapic_base[kLapicErrorStatus]);
      }
    }
  }
  while (gAwakeCpus != cpu_count) {
    DisplayString("Waiting for APs to wake up: ");
    DisplayUint64(gAwakeCpus);
    DisplayString(" online out of ");
    DisplayUint64(cpu_count);
    DisplayString(" with BootstrapDebugCounter=");
    DisplayUint64(*gBootstrapDebugCounter);
    DisplayString("\n");
    WaitMsec(1000);
  }
  DisplayUint64(cpu_count);
  DisplayString(" total CPUs online\n");
}

void Handoff() {
  memset(&gCpus, 0, sizeof(Cpu) * 256);
  SetupBootstrap();
  MapRuntimeStartImage();
  _wbinvd();
  auto bsp_id = ConfigureBspLapic();
  SetupCommonTables();
  SetupApLapics();
  FinishCommonTables();
  SetupDMAR();
  WakeupAPs(bsp_id);
  DisplayString("EnterRuntime() on BSP\n");
  EnterRuntime((uint64_t)&gCpus[0], &gCpus[1] - &gCpus[0]);
  halt_forever();
}

void ResetApic(Cpu* self) {
  self->lapic[kLapicDestinationFormat] = 0xFFFFFFFF;
  auto ldr = self->lapic[kLapicLogicalDestination];
  ldr = (ldr & 0x00FFFFFF) | 1;
  self->lapic[kLapicLogicalDestination] = ldr;
  self->lapic[kLapicLvtTimer] = kLapicDisable;
  self->lapic[kLapicLvtPerfCtr] = kLapicNmi;
  self->lapic[kLapicLvtLint0] = kLapicDisable;
  self->lapic[kLapicLvtLint1] = kLapicDisable;
  self->lapic[kLapicTaskPriority] = 0;
  // Set global enable bit.
  wrmsr(kApicBaseMsr, rdmsr(kApicBaseMsr) | (1 << 11));
  // Software enable (shared with the spurious vector register). Map spurious
  // interrupt to dummy isr.
  self->lapic[kLapicSpuriousVector] = 39 | kLapicSwEnable;
  // Map timer to an interrupt, enabling one-shot mode.
  self->lapic[kLapicTimerInitialCount] =
      0;  // cancel (TODO: check this; on vbox we get a timer interrupt a couple
          // seconds after sti on the bsp, but on actual hardware this doesn't
          // happen; setting this register seems to stop the "extra" interrupt)
  self->lapic[kLapicLvtTimer] = 0x20;
  // 1e sends 1f (illegal)
  // 1f sends 20 (ok)
  // Set timer divide value.
  self->lapic[kLapicTimerDivide] = 3;
  // TODO: send eoi
  // TODO: set up stack switching
  // TODO: make sure the stack is aligned
}

// CpuEntryPoint starts with interrupts off.
// If CpuEntryPoint exits, we turn interrupts on and enter the idle loop.
extern "C" void CpuEntryPoint(Cpu* self) {
  wrmsr(kGsBaseMSR, (uint64_t)self);
  wrmsr(kKernelGsBaseMSR, (uint64_t)self);
  wrmsr(kFsBaseMSR, 0);  // FS is the TCB
  
  if (!self->is_bsp) {
    //bfi::DisplayString(">>>>>>>>>>>>>>>> ap entry point ");
    //DV(self);
    // On the off chance that the local apic is at a different physical address,
    // map it somewhere.
    uint64_t lapic_base_phy = rdmsr(kApicBaseMsr);
    wrmsr(kApicBaseMsr,
               (lapic_base_phy & ~0xFFFFULL) | kApicBaseMsrEnable);
    // This is safe as long as no_alloc is true.
    self->lapic = (uint32_t* volatile)Map4kPage(
        (uint64_t)self->lapic, lapic_base_phy, true, true, /*remap_ok=*/true,
        /*no_alloc=*/true);
    ResetApic(self);
    self->lapic[kLapicTimerInitialCount] = 1;  // arm timer
  } else {
    //SV(&self);
    //bfi::DisplayString(">>>>>>>> bsp entry point <<<<<<<<<");
    DisplayString("BSP entry point\n");
    ResetApic(self);
    self->lapic[kLapicTimerInitialCount] = 1;  // arm timer
  }
  DebugSetActiveStatus();
  if (self->is_bsp) {
    const void* entry = Hello1RawEntry();
    if (entry == nullptr) {
      PANIC("no entry point");
    }
    auto* tcb = AllocThread(entry);
    EnterThread(tcb);
  }
}