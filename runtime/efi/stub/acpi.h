#pragma once

#include <stdint.h>

inline bool FourCCMatch(const char* fourcc_a, const char* fourcc_b) {
  for (int i = 0; i < 4; ++i) if (fourcc_a[i] != fourcc_b[i]) return false;
  return true;
}

#pragma pack(push, 1)
struct SDTHeader {
  char signature[4];
  uint32_t length;
  uint8_t revision;
  uint8_t checksum;
  char oem[6];
  char oem_table[8];
  uint32_t oem_revision;
  uint32_t creator_id;
  uint32_t creator_revision;
};

struct XSDT {
  SDTHeader header;
  SDTHeader* sdt[];
};

enum MADTRecordType : uint8_t { kProcessorLocalAPIC = 0 };

struct MADTProcessorLocalAPIC {
  uint8_t processor_id;
  uint8_t apic_id;
  uint32_t flags;
};

struct MADTRecord {
  MADTRecordType type;
  uint8_t length;
  union {
    MADTProcessorLocalAPIC lapic;
  };
};

struct MADT {
  SDTHeader header;
  uint32_t lapic_address;
  uint32_t flags;
};

struct DMARRecordHeader {
  uint16_t type;
  uint16_t length;
};

// DMAR records. Field and flag names follow the Intel VT-d architecture
// specification, chapter 8 ("BIOS Considerations"): 8.1 the DMAR table, 8.3
// the DRHD record, 8.3.1 the Device Scope structure. The comments here only
// summarise; the specification is the reference.

/// INCLUDE_PCI_ALL: set if this unit covers every PCI device in its segment
/// that no other unit lists; clear if it covers only the devices in its Device
/// Scope entries. When set, the Device Scope may still list I/O APICs and
/// HPETs, and the record comes after the segment's other DRHD records.
constexpr uint8_t kDRHDFlagINCLUDE_PCI_ALL = (1 << 0);

struct DMARRecordDRHD {
  DMARRecordHeader header;
  /// See kDRHDFlag*.
  uint8_t flags;
  /// Bits 3:0: the unit's register set is 2^N 4 KiB pages.
  uint8_t size;
  /// The PCI segment of this unit.
  uint16_t segment;
  /// Base address of the unit's registers, aligned to the register set size.
  uint64_t base_address;
};

// Device Scope entry types.

/// A PCI endpoint.
constexpr uint8_t kDRHDDeviceScopeTypePCIEndpoint = 1;
/// A PCI-PCI bridge and everything below it.
constexpr uint8_t kDRHDDeviceScopeTypePCISubHierarchy = 2;
/// An I/O APIC listed in the MADT.
constexpr uint8_t kDRHDDeviceScopeTypeIOAPIC = 3;
/// An MSI-capable HPET timer block listed in the HPET table.
constexpr uint8_t kDRHDDeviceScopeTypeMSI_CAPABLE_HPET = 4;
/// An ACPI namespace device that can issue DMA or MSIs (see the ANDD record).
constexpr uint8_t kDRHDDeviceScopeTypeACPI_NAMESPACE_DEVICE = 5;

// Device Scope flags. The first three constrain the PASID table entry used
// for this source ID's requests without a PASID (RID_PASID).

/// Nested translation (PGTT = 011b) should not be used in that entry.
constexpr uint8_t kDRHDDeviceScopeFlagREQ_WO_PASID_NESTED_NOTALLOWED = (1 << 0);
/// PWSNP must stay 0 in that entry.
constexpr uint8_t kDRHDDeviceScopeFlagREQ_WO_PASID_PWSNP_NOTALLOWED = (1 << 1);
/// PGSNP must stay 0 in that entry, and SNP must stay clear in the leaf
/// second-stage entries it uses.
constexpr uint8_t kDRHDDeviceScopeFlagREQ_WO_PASID_PGSNP_NOTALLOWED = (1 << 2);
/// The device's address translation cache (ATC) meets the specification's
/// hardening requirements; enabling it is recommended.
constexpr uint8_t kDRHDDeviceScopeFlagATC_HARDENED = (1 << 3);
/// The device does not work unless its ATC is enabled (ATS capability).
constexpr uint8_t kDRHDDeviceScopeFlagATC_REQUIRED = (1 << 4);

/// One Device Scope entry: a device under this remapping unit. The fixed part
/// is followed by (device, function) byte pairs, the path from
/// `start_bus_number` down to the device (VT-d specification, 8.3.1).
struct DeviceScope {
  /// See kDRHDDeviceScopeType*.
  uint8_t type;
  /// Entry length in bytes: 6 plus the path's length.
  uint8_t length;
  /// See kDRHDDeviceScopeFlag*.
  uint8_t flags;
  uint8_t reserved;
  /// IOAPIC entries: the I/O APIC's ID, as in the MADT. MSI_CAPABLE_HPET
  /// entries: the HPET number, as in the HPET table. ACPI_NAMESPACE_DEVICE
  /// entries: the ACPI device number, as in the ANDD record.
  uint8_t enumeration_id;
  /// The bus the path starts on. For HPET and ACPI namespace devices, the bus
  /// byte of the source ID the platform assigned to the device.
  uint8_t start_bus_number;
};

constexpr uint8_t kDMARTagDRHD = 0;
constexpr uint8_t kDMARTagRMRR = 1;
constexpr uint8_t kDMARTagATSR = 2;
constexpr uint8_t kDMARTagRHSA = 3;
constexpr uint8_t kDMARTagANDD = 4;
constexpr uint8_t kDMARTagSATC = 5;
constexpr uint8_t kDMARTagSIDP = 6;

// DMAR table flags.

/// The platform supports interrupt remapping.
constexpr uint8_t kDMARFlagINTR_REMAP = (1 << 0);
/// Firmware asks the OS not to enable x2APIC mode (meaningful only with
/// INTR_REMAP set).
constexpr uint8_t kDMARFlagX2APIC_OPT_OUT = (1 << 1);
/// Firmware reports that platform-initiated DMA at handoff is limited to the
/// regions listed in RMRR records, so the OS may block all other DMA except
/// to memory that drivers register.
constexpr uint8_t kDMARFlagDMA_CTRL_PLATFORM_OPT_IN_FLAG = (1 << 2);

struct DMAR {
  SDTHeader header;
  /// The platform's DMA address width minus 1 (e.g. 39 for 40-bit addresses).
  uint8_t host_address_width;
  /// See the kDMARFlag constants.
  uint8_t flags;
  uint8_t reserved[10];
};

struct XSDP {
  char signature[8];
  uint8_t checksum;
  char oem[6];
  uint8_t revision;
  uint32_t deprecated;

  uint32_t length;
  XSDT* xsdt;
  uint8_t checksum_ext;
  uint8_t reserved[3];
};
#pragma pack(pop)
