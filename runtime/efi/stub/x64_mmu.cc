/*
 * x86-64 paging for the Kraken EFI stub (see x64_mmu.h).
 */
#include "x64_mmu.h"

#include <efi.h>

#include "debug.h"
#include "stub.h"  // memset

namespace {
uint64_t gFreeVirtualAddress = 0;
uint64_t gAllocBase = 0;
}  // anonymous namespace

uint64_t gApBootstrapAddress = 0;

EFI_STATUS InitMMU(EFI_MEMORY_DESCRIPTOR* map, UINTN memory_map_size, UINTN descriptor_size, uint64_t bootstrap_length) {
  // We can reclaim more of this later, but just find the biggest block for now.
  uint64_t total_size = 0;
  uint64_t largest_block_start = 0;
  uint64_t largest_block_size = 0;
  uint64_t largest_low_block_start = 0;
  uint64_t largest_low_block_size = 0;

  // PrintString("EFI memory map\n");
  // PrintString("Type PhysicalStart VirtualStart NumberOfPages Attribute\n");
  char* memory_descriptor_raw = (char*)map;
  char* memory_descriptor_limit = memory_descriptor_raw + memory_map_size;
  for (; memory_descriptor_raw < memory_descriptor_limit;
       memory_descriptor_raw += descriptor_size) {
    EFI_MEMORY_DESCRIPTOR* md = (EFI_MEMORY_DESCRIPTOR*)memory_descriptor_raw;
#if 0
    PrintUint64(md->Type);
    PrintString(" ");
    PrintUint64(md->PhysicalStart);
    PrintString(" ");
    PrintUint64(md->VirtualStart);
    PrintString(" ");
    PrintUint64(md->NumberOfPages);
    PrintString(" ");
    PrintUint64(md->Attribute);
    PrintString("\n");
#endif
    if (md->PhysicalStart == 0) {
      if (md->Type != EfiConventionalMemory &&
          md->Type != EfiBootServicesCode) {
        PANIC("Physical memory block starting at 0 was not type 7 or 3 (EfiConventionalMemory/EfiBootServicesCode)");
        return EFI_INVALID_PARAMETER;
      }
      if (md->NumberOfPages < bootstrap_length / 4096 + 1) {
        PANIC("Physical memory block starting at 0 was not large enough to copy AP bootstrap");
        return EFI_INVALID_PARAMETER;
      }
    }
    total_size += md->NumberOfPages * 4096;
    if (md->NumberOfPages > largest_block_size &&
        md->Type == EfiConventionalMemory) {
      largest_block_size = md->NumberOfPages;
      largest_block_start = md->PhysicalStart;
    }
    if (md->NumberOfPages > largest_low_block_size &&
        md->Type == EfiConventionalMemory &&
        md->PhysicalStart < 0x100000000UL) {
      largest_low_block_size = md->NumberOfPages;
      largest_low_block_start = md->PhysicalStart;
    }
    if (md->Type == EfiConventionalMemory && md->PhysicalStart <= 0x8000 &&
        md->PhysicalStart + md->NumberOfPages * 4096 >=
            bootstrap_length + 0x8000) {
      gApBootstrapAddress = 0x8000;
    }
    gFreeVirtualAddress = md->PhysicalStart + md->NumberOfPages * 0x1000;
  }

  if (gApBootstrapAddress == 0) {
    PANIC("Could not find a conventional block around 0x8000 long enough to fit the AP bootstrap.");
    return EFI_INVALID_PARAMETER;
  }

  DisplayString("Total memory size ");
  DisplayUint64(total_size);
  DisplayString(" largest block start ");
  DisplayUint64(largest_block_start);
  DisplayString(" largest block size ");
  DisplayUint64(largest_block_size);
  DisplayString(" largest low block start ");
  DisplayUint64(largest_low_block_start);
  DisplayString(" largest low block size ");
  DisplayUint64(largest_low_block_size);

  DisplayString("\n");

  gAllocBase = largest_block_start;
  gFreeVirtualAddress = 0xB0000000000ULL;

  return EFI_SUCCESS;
}

uint64_t AllocatePages(uint64_t pages) {
  auto allocated_base = gAllocBase;
  gAllocBase += pages * 0x1000;
  char* bp = (char*)allocated_base;
  memset(bp, 0, pages * 0x1000);
  // LOAD_BEARING_PRINT(SV(allocated_base));
  return allocated_base;
}

uint64_t AllocateVirtualAddress(uint64_t pages) {
  auto base = gFreeVirtualAddress;
  gFreeVirtualAddress += pages * 0x1000;
  return base;
}

uint64_t Allocate2MVirtualAddress(uint64_t pages) {
  if ((gFreeVirtualAddress % 0x200000) != 0) {
    gFreeVirtualAddress += (0x200000 - (gFreeVirtualAddress % 0x200000));
  }
  auto base = gFreeVirtualAddress;
  gFreeVirtualAddress += pages * 0x200000;
  return base;
}

constexpr uint64_t k2M = 1ULL << 21;
constexpr uint64_t k1G = 1ULL << 30;
// Bit 7: PS in a PDPT or PD entry (a 1 GB or 2 MB page), PAT in a PTE.
constexpr uint64_t kPageSizeBit = 1ULL << 7;
// PAT in a 1 GB or 2 MB page's entry.
constexpr uint64_t kLargePagePat = 1ULL << 12;
// The physical address bits of an entry (51:12).
constexpr uint64_t kAddressMask = 0x000FFFFFFFFFF000ULL;

// Firmware identity-maps memory with large pages: 1 GB in a PDPT entry, 2 MB
// in a PD entry (PS set). To map something inside one, replace it with a
// table of the 512 next-smaller pages that maps the same range with the same
// attributes; the translations do not change, so the walk can go on below.
static void SplitLargePage(uint64_t* entry, bool one_gb,
                           uint64_t virtual_address) {
  uint64_t e = *entry;
  uint64_t size = one_gb ? k1G : k2M;
  uint64_t child_size = size >> 9;
  uint64_t address_bits = kAddressMask & ~(size - 1);
  uint64_t base = e & address_bits;
  uint64_t flags = e & ~address_bits;  // with PS, PAT (bit 12) and NX
  if (!one_gb) {
    // 4 KB entries have no PS, and their PAT bit is bit 7, not bit 12.
    bool pat = (flags & kLargePagePat) != 0;
    flags &= ~(kPageSizeBit | kLargePagePat);
    if (pat) flags |= kPageSizeBit;
  }
  auto* table = reinterpret_cast<uint64_t*>(AllocatePages(1));
  for (uint64_t i = 0; i < 512; ++i) table[i] = flags | (base + i * child_size);
  // The table's own entry: present and writable, user if the page was; the
  // pages below keep their own permissions.
  *entry = reinterpret_cast<uint64_t>(table) | 3 | (e & 4);
  // Same translations at a new page size: drop the large page from the TLB
  // (INVLPG also clears the paging-structure caches).
  invlpg(reinterpret_cast<void*>(virtual_address));
}

uint64_t PhysicalAddressForVirtualAddress(uint64_t virtual_address) {
  auto pt4 = GetRootPageTable();
  auto pt4_ofs = (virtual_address >> (uint64_t)(12 + 9 * 3)) & 0x1FFULL;
  auto pt3 = (pt3e*)(pt4[pt4_ofs].ptr_shr_12 << 12);
  auto pt3_ofs = (virtual_address >> (uint64_t)(12 + 9 * 2)) & 0x1FFULL;
  if (pt3[pt3_ofs].raw & kPageSizeBit) {  // a 1 GB page
    return (pt3[pt3_ofs].raw & kAddressMask & ~(k1G - 1)) |
           (virtual_address & (k1G - 1));
  }
  auto pt2 = (pt2e*)(pt3[pt3_ofs].ptr_shr_12 << 12);
  // auto pt2_2mb = (pt2e_2mb_s*)pt2;
  auto pt2_ofs = (virtual_address >> (uint64_t)(12 + 9 * 1)) & 0x1FFULL;
  if (pt2[pt2_ofs].is_2mb_pt2e) {  // a 2 MB page
    return (pt2[pt2_ofs].raw & kAddressMask & ~(k2M - 1)) |
           (virtual_address & (k2M - 1));
  }
  auto pt1 = (pt1e*)(pt2[pt2_ofs].ptr_shr_12 << 12);
  auto pt1_ofs = (virtual_address >> (12 + 9 * 0)) & 0x1FFULL;
  return pt1[pt1_ofs].ptr_shr_12 << 12 | (virtual_address & ~(~0ULL << 12));
}

void* Map2MPage(uint64_t virtual_address, uint64_t physical_address,
                bool cache_disable, bool writethrough, bool remap_ok,
                bool no_alloc) {
  if (virtual_address % 0x200000 != 0 || physical_address % 0x200000 != 0) {
    // PrintString("unaligned Map2MPage");
    for (;;);
  }
  auto pt4 = GetRootPageTable();
  DisableWriteProtection dwp;
  auto pt4_ofs = (virtual_address >> (uint64_t)(12 + 9 * 3)) & 0x1FFULL;
  // LOAD_BEARING_PRINT(SV(pt4_ofs));
  if (pt4[pt4_ofs].raw == 0) {
    if (no_alloc) {
      // PrintString("would allocate");
      for (;;);
    }
    pt4[pt4_ofs].raw = AllocatePages(1) | 3;
  }
  auto pt3 = (pt3e*)(pt4[pt4_ofs].ptr_shr_12 << 12);
  auto pt3_ofs = (virtual_address >> (uint64_t)(12 + 9 * 2)) & 0x1FFULL;
  if (pt3[pt3_ofs].raw == 0) {
    if (no_alloc) {
      // PrintString("would allocate");
      for (;;);
    }
    pt3[pt3_ofs].raw = AllocatePages(1) | 3;
  }
  if (pt3[pt3_ofs].raw & kPageSizeBit) {  // a 1 GB page: split it
    SplitLargePage(&pt3[pt3_ofs].raw, true, virtual_address);
  }
  auto pt2 = (pt2e*)(pt3[pt3_ofs].ptr_shr_12 << 12);
  auto pt2_2mb = (pt2e_2mb_s*)pt2;
  auto pt2_ofs = (virtual_address >> (uint64_t)(12 + 9 * 1)) & 0x1FFULL;
  if (!remap_ok && pt2[pt2_ofs].raw != 0) {
    // PrintString("overwriting existing mapping ");
    // SV(pt2_2mb[pt2_ofs].raw);
    for (;;) {
    }
  }
  pt2_2mb[pt2_ofs].one_0 = 1;
  pt2_2mb[pt2_ofs].ptr_shr_21 = (physical_address >> 21);
  pt2_2mb[pt2_ofs].raw |= 3;
  pt2_2mb[pt2_ofs].page_level_cache_disable = cache_disable ? 1 : 0;
  pt2_2mb[pt2_ofs].page_level_writethrough = writethrough ? 1 : 0;

  // LOAD_BEARING_PRINT(PrintString("mapped 2M page "));
  // LOAD_BEARING_PRINT(PrintUint64(virtual_address));
  // LOAD_BEARING_PRINT(PrintString(" to "));
  // LOAD_BEARING_PRINT(PrintUint64(physical_address));
  // LOAD_BEARING_PRINT(PrintString("\n"));
  invlpg((void*)virtual_address);
  return (void*)(virtual_address);
}

void* Map4kPage(uint64_t virtual_address, uint64_t physical_address,
                bool cache_disable, bool writethrough, bool remap_ok,
                bool no_alloc) {
  auto pt4 = GetRootPageTable();
  DisableWriteProtection dwp;
  auto pt4_ofs = (virtual_address >> (uint64_t)(12 + 9 * 3)) & 0x1FFULL;
  // LOAD_BEARING_PRINT(SV(pt4_ofs));
  if (pt4[pt4_ofs].raw == 0) {
    if (no_alloc) {
      PANIC("would allocate");
    }
    pt4[pt4_ofs].raw = AllocatePages(1) | 3;
  }
  auto pt3 = (pt3e*)(pt4[pt4_ofs].ptr_shr_12 << 12);
  auto pt3_ofs = (virtual_address >> (uint64_t)(12 + 9 * 2)) & 0x1FFULL;
  if (pt3[pt3_ofs].raw == 0) {
    if (no_alloc) {
      PANIC("would allocate");
    }
    pt3[pt3_ofs].raw = AllocatePages(1) | 3;
  }
  if (pt3[pt3_ofs].raw & kPageSizeBit) {  // a 1 GB page: split it
    SplitLargePage(&pt3[pt3_ofs].raw, true, virtual_address);
  }
  auto pt2 = (pt2e*)(pt3[pt3_ofs].ptr_shr_12 << 12);
  // For the commented-out SV below.
  [[maybe_unused]] auto pt2_2mb = (pt2e_2mb_s*)pt2;
  auto pt2_ofs = (virtual_address >> (uint64_t)(12 + 9 * 1)) & 0x1FFULL;
  if (pt2[pt2_ofs].raw == 0) {
    if (no_alloc) {
      PANIC("would allocate");
    }
    pt2[pt2_ofs].raw = AllocatePages(1) | 3;
  } else if (pt2[pt2_ofs].is_2mb_pt2e) {  // a 2 MB page: split it
    SplitLargePage(&pt2[pt2_ofs].raw, false, virtual_address);
  }
  auto pt1 = (pt1e*)(pt2[pt2_ofs].ptr_shr_12 << 12);
  auto pt1_ofs = (virtual_address >> (12 + 9 * 0)) & 0x1FFULL;
  if (!remap_ok && pt1[pt1_ofs].raw != 0) {
    PANIC("overwriting existing 4K mapping ");
    // SV(pt1[pt1_ofs].raw);
    // for (;;) {
    // }
  }
  pt1[pt1_ofs].raw = physical_address | 3;
  pt1[pt1_ofs].page_level_cache_disable = cache_disable ? 1 : 0;
  pt1[pt1_ofs].page_level_writethrough = writethrough ? 1 : 0;
  // LOAD_BEARING_PRINT(PrintString("mapped "));
  // LOAD_BEARING_PRINT(PrintUint64(virtual_address));
  // LOAD_BEARING_PRINT(PrintString(" to "));
  // LOAD_BEARING_PRINT(PrintUint64(physical_address));
  // LOAD_BEARING_PRINT(PrintString("\n"));
  invlpg((void*)virtual_address);
  return (void*)(virtual_address);
}

void Set4kPageReadOnly(uint64_t virtual_address) {
  auto pt4 = GetRootPageTable();
  DisableWriteProtection dwp;
  auto pt4_ofs = (virtual_address >> (uint64_t)(12 + 9 * 3)) & 0x1FFULL;
  if (!pt4[pt4_ofs].present) PANIC("Set4kPageReadOnly: not mapped");
  auto pt3 = (pt3e*)(pt4[pt4_ofs].ptr_shr_12 << 12);
  auto pt3_ofs = (virtual_address >> (uint64_t)(12 + 9 * 2)) & 0x1FFULL;
  if (!pt3[pt3_ofs].present || (pt3[pt3_ofs].raw & kPageSizeBit)) {
    PANIC("Set4kPageReadOnly: not a 4K mapping");
  }
  auto pt2 = (pt2e*)(pt3[pt3_ofs].ptr_shr_12 << 12);
  auto pt2_ofs = (virtual_address >> (uint64_t)(12 + 9 * 1)) & 0x1FFULL;
  if (!pt2[pt2_ofs].present || pt2[pt2_ofs].is_2mb_pt2e) {
    PANIC("Set4kPageReadOnly: not a 4K mapping");
  }
  auto pt1 = (pt1e*)(pt2[pt2_ofs].ptr_shr_12 << 12);
  auto pt1_ofs = (virtual_address >> (12 + 9 * 0)) & 0x1FFULL;
  if (!pt1[pt1_ofs].present) PANIC("Set4kPageReadOnly: not mapped");
  pt1[pt1_ofs].read_write = 0;
  invlpg((void*)virtual_address);
}
