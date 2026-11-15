#pragma once

#include <stdint.h>  // clang's own header: the stub has no C++ standard library

#include "acpi.h"

#pragma pack(push, 1)

using PCIBAR = uint32_t;

constexpr uint32_t kPCIBARPrefetchable = (1 << 3);
constexpr uint32_t kPCIBARIsIOspace = 1;
constexpr uint32_t kPCIBARTypeMask = 6;
/// base address ((BAR[x] & 0xFFFFFFF0) + ((BAR[x + 1] & 0xFFFFFFFF) << 32))
constexpr uint32_t kPCIBARType64 = (0x2 << 1);
constexpr uint32_t kPCIBARTypeLegacy = (0x1 << 1);
/// base address (BAR[x] & 0xFFFFFFF0)
constexpr uint32_t kPCIBARType32 = 0;

constexpr uint8_t kPCICapabilityMSI = 0x5;
constexpr uint8_t kPCICapabilityMSIX = 0x11;
constexpr uint16_t kPCIMSI64BitCapable = 0x80;

struct PCICapabilityHeader {
  uint8_t cap_id;
  uint8_t next_cap;
};

struct PCICapabilityMSI {
  PCICapabilityHeader header;
  uint16_t control;
  uint32_t addr_low;
  uint32_t addr_high;
  uint16_t data;
  uint16_t reserved;
  uint32_t mask;
  uint32_t pending;
};

struct PCICapabilityMSIX {
  PCICapabilityHeader header;
};

// PCI configuration space. Names follow the PCI Local Bus Specification's
// configuration space header; the comments only summarise it.

/// Type 0 header fields after the common part (offsets 0x10-0x3F).
struct PCIConfigHeader0 {
  PCIBAR bar[6];
  /// CardBus CIS pointer.
  uint32_t cis;
  uint16_t subvendor_id;
  uint16_t subsystem_id;
  uint32_t rom_base;
  uint8_t capabilities_ptr;
  uint8_t reserved_0[3];
  uint32_t reserved;
  /// On x86, the legacy PIC IRQ (0-15) the interrupt pin is routed to; 0xFF
  /// if none.
  uint8_t int_line;
  /// Interrupt pin: 1-4 for INTA#-INTD#, 0 for none.
  uint8_t int_pin;
  /// Burst period in 1/4 microseconds (conventional PCI only).
  uint8_t min_grant;
  /// Bus access period in 1/4 microseconds (conventional PCI only).
  uint8_t max_latency;
};

// Command register bits. Bits 3, 4, 5, 7 and 9 are 0 on PCIe.

/// The device responds to I/O space accesses.
constexpr uint16_t kPCICommandIOEnable = (1 << 0);
/// The device responds to memory space accesses.
constexpr uint16_t kPCICommandMemoryEnable = (1 << 1);
/// The device may issue memory and I/O requests: DMA, and on PCIe also MSI
/// and MSI-X, which are memory writes.
constexpr uint16_t kPCICommandBusMasterEnable = (1 << 2);
constexpr uint16_t kPCICommandSpecialCycleEnable = (1 << 3);
constexpr uint16_t kPCICommandMemoryWriteAndInvalidateEnable = (1 << 4);
constexpr uint16_t kPCICommandVGAPaletteSnoopEnable = (1 << 5);
constexpr uint16_t kPCICommandParityErrorResponseEnable = (1 << 6);
constexpr uint16_t kPCICommandReserved = (1 << 7);
constexpr uint16_t kPCICommandSERREnable = (1 << 8);
constexpr uint16_t kPCICommandFastBackBackEnable = (1 << 9);
/// Masks the device's INTx# interrupt (not MSI or MSI-X).
constexpr uint16_t kPCICommandInterruptDisable = (1 << 10);

// Status register bits.

/// An INTx# interrupt is pending.
constexpr uint16_t kPCIStatusInterruptStatus = (1 << 3);
/// `capabilities_ptr` (offset 0x34) is valid.
constexpr uint16_t kPCIStatusCapabilitiesList = (1 << 4);
constexpr uint16_t kPCIStatus66MhzCapable = (1 << 5);
constexpr uint16_t kPCIStatusFastBackToBackCapable = (1 << 7);
constexpr uint16_t kPCIStatusMasterDataParityError = (1 << 8);
/// Two-bit field (bits 10:9): 0 fast, 1 medium, 2 slow.
constexpr uint16_t kPCIStatusDEVSELTiming = (1 << 9);
constexpr uint16_t kPCIStatusSignaledTargetAbort = (1 << 11);
constexpr uint16_t kPCIStatusReceivedTargetAbort = (1 << 12);
constexpr uint16_t kPCIStatusReceivedMasterAbort = (1 << 13);
constexpr uint16_t kPCIStatusSignaledSystemError = (1 << 14);
constexpr uint16_t kPCIStatusDetectedParityError = (1 << 15);

/// A function's configuration space header (PCI Local Bus Specification,
/// configuration space).
struct PCIConfig {
  /// 0xFFFF when no function is present.
  uint16_t vendor_id;
  uint16_t device_id;
  /// See kPCICommand*.
  uint16_t command;
  /// See kPCIStatus*.
  uint16_t status;
  uint8_t revision_id;
  /// Programming interface, subclass and base class: the class code.
  uint8_t prog_if;
  uint8_t subclass;
  uint8_t baseclass;
  /// In 32-bit units.
  uint8_t cache_line_size;
  /// Conventional PCI only.
  uint8_t latency_timer;
  /// Bits 6:0: the header layout (0 for PCIConfigHeader0); bit 7: the device
  /// has several functions.
  uint8_t header_type;
  /// Built-in self test control and status.
  uint8_t bist;
  /// Valid only when the header layout is 0 (not for bridges).
  PCIConfigHeader0 header_0;

  uint8_t device_specific[0];
};

struct MCFGRecord {
  uint64_t base_address;
  uint16_t pci_segment_group;
  uint8_t start_bus_number;
  uint8_t end_bus_number;
  uint32_t reserved;
};

struct MCFG {
  SDTHeader header;
  uint64_t reserved;
};
#pragma pack(pop)
