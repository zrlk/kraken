#!/usr/bin/env bash
# Wi-Fi facts on the board, read-only: which firmware the AX101 runs and
# how Linux has set the device up.
#
# Usage: sudo ./facts.sh [OUTDIR]
#
# Run it while Wi-Fi is connected. It records: the firmware file's hashes
# and its table of command versions (fwtlv.py; numbers only, no firmware
# bytes), driver and kernel versions, the security parameters of the
# current link, interrupt counts, PCI device control and capability
# registers, the IOMMU group, and the driver's debugfs ring state.
# Nothing is written to the device and the driver is not reloaded.
#
# Not recorded: the network's name (SSID lines are dropped), scan results
# other than the cipher lines of the connected access point, keys. MAC
# addresses do appear (the adapter's and the access point's).
set -u
[ "$(id -u)" -eq 0 ] || { echo "facts.sh: run as root" >&2; exit 1; }
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:-wifi-facts-$(date -u +%Y%m%d-%H%M%S)}
mkdir -p "$OUT" || exit 1
run() { # run NAME CMD...: output and exit status to $OUT/NAME.txt
  local n=$1; shift
  { echo "\$ $*"; "$@" 2>&1; echo "exit $?"; } > "$OUT/$n.txt"
}

DEV=$(for d in /sys/bus/pci/drivers/iwlwifi/0000:*; do [ -e "$d" ] && basename "$d"; done | head -1)
IF=$(ls "/sys/bus/pci/devices/$DEV/net" 2>/dev/null | head -1)
echo "device ${DEV:-none} interface ${IF:-none}" | tee "$OUT/facts.log"
[ -n "$DEV" ] || { echo "facts.sh: no device bound to iwlwifi" >&2; exit 1; }

# 1. Firmware: the file the driver loaded, by the name in the kernel log.
FWN=$(dmesg | awk '/iwlwifi.*loaded firmware version/ { for (i = 1; i <= NF; i++) if ($i ~ /[.]ucode$/) f = $i } END { print f }')
echo "firmware name from dmesg: ${FWN:-unknown}" >> "$OUT/facts.log"
: > "$OUT/firmware.txt"
for f in /lib/firmware/iwlwifi-"${FWN:-so-a0-hr-b0-89.ucode}"*; do
  [ -e "$f" ] || continue
  sha256sum "$f" >> "$OUT/firmware.txt"
  python3 "$HERE/fwtlv.py" "$f" >> "$OUT/firmware.txt" 2>&1
done
dmesg | awk '/iwlwifi/' > "$OUT/dmesg-iwlwifi.txt"

# 2. Versions.
run versions sh -c 'uname -r; modinfo -F version iwlwifi; modinfo -F vermagic iwlwifi; modinfo -F firmware iwlwifi | awk "/so-a0-hr-b0/"'
run modparams sh -c 'for p in /sys/module/iwlwifi/parameters/* /sys/module/iwlmvm/parameters/*; do echo "$p $(cat "$p" 2>/dev/null)"; done'

# 3. Security parameters of the current link, without the network's name.
if [ -n "$IF" ]; then
  { iw dev "$IF" link 2>&1 | awk '$1 != "SSID:"'; } > "$OUT/link.txt"
  iw dev "$IF" station dump > "$OUT/station.txt" 2>&1
  BSS=$(awk '/^Connected to/ { print $3 }' "$OUT/link.txt")
  if [ -n "$BSS" ]; then
    iw dev "$IF" scan dump 2>/dev/null | awk -v b="$BSS" '
      /^BSS / { p = (index($2, b) == 1) }
      p && /^BSS |freq:|capability:|RSN:|Version:|Group cipher|Pairwise ciphers|Authentication suites|Capabilities:|Group mgmt cipher/' \
      > "$OUT/bss-security.txt"
  fi
  iw dev "$IF" info 2>&1 | awk '$1 != "ssid"' > "$OUT/info.txt"
  iw reg get > "$OUT/reg.txt" 2>&1
fi

# 4. Interrupts.
awk 'NR == 1 || /iwlwifi/' /proc/interrupts > "$OUT/interrupts.txt"

# 5. PCI and IOMMU.
run lspci lspci -vvv -nn -s "$DEV"
run lspci-hex lspci -xxxx -s "$DEV"
run devctl setpci -s "$DEV" CAP_EXP+8.w
G=$(basename "$(readlink "/sys/bus/pci/devices/$DEV/iommu_group" 2>/dev/null)" 2>/dev/null)
{
  echo "iommu group ${G:-none}"
  [ -n "$G" ] && ls "/sys/kernel/iommu_groups/$G/devices" && cat "/sys/kernel/iommu_groups/$G/type"
  echo "reset_method $(cat "/sys/bus/pci/devices/$DEV/reset_method" 2>/dev/null)"
  echo "msi_irqs $(ls "/sys/bus/pci/devices/$DEV/msi_irqs" 2>/dev/null | tr '\n' ' ')"
} > "$OUT/iommu.txt" 2>&1

# 6. The driver's own view of its rings (debugfs, read-only).
D=/sys/kernel/debug/iwlwifi/$DEV
{
  ls -R "$D" 2>&1 | head -200
  for f in "$D"/trans/rx_queue "$D"/trans/tx_queue "$D"/trans/interrupt "$D"/trans/fh_reg \
           "$D"/*/fw_ver "$D"/*/*/fw_ver; do
    [ -r "$f" ] || continue
    echo "== $f"; cat "$f" 2>&1
  done
} > "$OUT/debugfs.txt"

tar -czf "$OUT.tar.gz" "$OUT" && echo "facts.sh: wrote $OUT.tar.gz"
