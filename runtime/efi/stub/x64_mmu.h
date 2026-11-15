/*
 * x86-64 paging for the Kraken EFI stub: the 4-level page table entries
 * (amd64_page_directory, pt4e..pt1e, pt2e_2mb), the current root table
 * (GetRootPageTable) and CR0.WP (DisableWriteProtection). Implementation in
 * x64_mmu.cc.
 */
#ifndef KRAKEN_EFI_X64_MMU_H_
#define KRAKEN_EFI_X64_MMU_H_

#include <stdint.h>  // clang's own header

#include "debug.h"
#include "x64.h"  // readcr0, writecr0, readcr3

/// the first three levels in the amd64 page table look identical to one
/// another:
typedef struct __attribute__((packed)) amd64_page_directory_s {
  union {
    struct {
      uint64_t present : 1;
      uint64_t read_write : 1;       /// if 0, writes may not be allowed to the
                                     /// region controlled by this entry
                                     /// (depends on CPL and CR0.WP (sec 4.6))
      uint64_t user_supervisor : 1;  /// if 0, accesses to the region with CPL=3
                                     /// are refused (4.6)
      uint64_t page_level_writethrough : 1;   /// (4.9)
      uint64_t page_level_cache_disable : 1;  /// (4.9)
      uint64_t accessed : 1;  /// indicates if this entry has been used for
                              /// linear access translation (4.8)
      uint64_t ignored_0 : 1;
      uint64_t is_2mb_pt2e : 1;  /// must be 0; if 1 and this is a pt2e, it's a
                                 /// 2mb
                                 /// page
      uint64_t ignored_1 : 4;
      uint64_t ptr_shr_12 : 41;  /// phys address of page-aligned next level,
                                 /// shifted
                                 /// right by 12 bits
      uint64_t ignored_2 : 10;
      uint64_t execute_disable : 1;  /// if 1 and IA32_EFER.NXE, disallow insn
                                     /// fetches from the region (otherwise must
                                     /// be 0)
    };
    uint64_t raw;
  };
} amd64_page_directory;

typedef amd64_page_directory pt4e;  // 512GB
typedef amd64_page_directory pt3e;  // 1GB
typedef amd64_page_directory pt2e;  // 2MB

typedef struct __attribute__((packed)) pt2e_2mb_s {
  union {
    struct {
      uint64_t present : 1;
      uint64_t read_write : 1;                /// see above (region here is 2MB)
      uint64_t user_supervisor : 1;           /// see above
      uint64_t page_level_writethrough : 1;   /// (4.9)
      uint64_t page_level_cache_disable : 1;  /// (4.9)
      uint64_t
          accessed : 1;  /// indicates whether software has accessed this page
      uint64_t
          dirty : 1;  /// indicates whether software has written to this page
      uint64_t one_0 : 1;   /// must be 1 (if not, this is actually a pde_s)
      uint64_t global : 1;  /// if CR4.PGE=1, determines if translation is
                            /// global
                            /// (4.10); ignored otherwise
      uint64_t ignored_0 : 3;
      uint64_t pat : 1;  /// controls memory type (4.9)
      uint64_t zero_0 : 8;
      uint64_t ptr_shr_21 : 32;  /// physical address of the page, shr 21.
      uint64_t ignored_1 : 10;
      uint64_t execute_disable : 1;  /// see above
    };
    uint64_t raw;
  };
} pt2e_2mb;

/// 4KB pages live underneath PDEs.
typedef struct __attribute__((packed)) pt1e_s {
  union {
    struct {
      uint64_t present : 1;
      uint64_t read_write : 1;                /// see above (region here is 4KB)
      uint64_t user_supervisor : 1;           /// see above
      uint64_t page_level_writethrough : 1;   /// (4.9)
      uint64_t page_level_cache_disable : 1;  /// (4.9)
      uint64_t
          accessed : 1;  /// indicates whether software has accessed this page
      uint64_t
          dirty : 1;     /// indicates whether software has written to this page
      uint64_t pat : 1;  /// controls memoty type (4.9)
      uint64_t global : 1;  /// if CR4.PGE=1, determines if translation is
                            /// global
                            /// (4.10); ignored otherwise
      uint64_t ignored_0 : 3;
      uint64_t ptr_shr_12 : 41;  /// phys address of the page, shr 12
      uint64_t ignored_1 : 10;
      uint64_t execute_disable : 1;  /// see above
    };
    uint64_t raw;
  };
} pt1e;

static inline pt4e* GetRootPageTable() {
  uint64_t cr3 = readcr3();
  return (pt4e*)(cr3 & ~0x7FFULL);
}

struct DisableWriteProtection {
  DisableWriteProtection() {
    cr0 = readcr0();
    writecr0(cr0 & (~(1ULL << 16)));
  }
  ~DisableWriteProtection() { writecr0(cr0); }
  uint64_t cr0;
};

extern uint64_t gApBootstrapAddress;

// Expensive and cheerful memory management.
uint64_t AllocatePages(uint64_t pages);
uint64_t AllocateVirtualAddress(uint64_t pages);
uint64_t Allocate2MVirtualAddress(uint64_t pages);
uint64_t PhysicalAddressForVirtualAddress(uint64_t virtual_address);
void* Map2MPage(uint64_t virtual_address, uint64_t physical_address,
                bool cache_disable, bool writethrough, bool remap_ok = false,
                bool no_alloc = false);
void* Map4kPage(uint64_t virtual_address, uint64_t physical_address,
                bool cache_disable, bool writethrough, bool remap_ok = false,
                bool no_alloc = false);

#endif  // KRAKEN_EFI_X64_MMU_H_
