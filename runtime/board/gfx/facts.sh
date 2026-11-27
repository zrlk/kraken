#!/bin/sh
# Graphics board facts: read-only collection of firmware, engine, IOMMU, CPU
# and PCIe facts for the GPU experiments.
#
# Usage: facts.sh OUTDIR
#
# Reads files under /proc, /sys and debugfs and runs dmesg and lspci. It
# writes only into OUTDIR, never changes a setting, never loads or unloads a
# module, and bounds every command with timeout. Run as root for dmesg,
# debugfs and the full lspci capability dump.

set -u

if [ $# -ne 1 ]; then
  echo "usage: facts.sh OUTDIR" >&2
  exit 1
fi
OUT=$1
mkdir -p "$OUT" || exit 1

T=10 # seconds per command

# run NAME CMD...: run CMD with a time bound, stdout and stderr into OUT/NAME.
run() {
  name=$1
  shift
  timeout "$T" "$@" >"$OUT/$name" 2>&1
  echo "exit=$?" >>"$OUT/$name"
}

# dumpfiles NAME FILE...: copy each readable regular file, with a header.
dumpfiles() {
  name=$1
  shift
  for f in "$@"; do
    [ -f "$f" ] || continue
    echo "== $f"
    timeout "$T" cat "$f" 2>&1
  done >"$OUT/$name"
}

# Kernel, command line, OS.
run uname.txt uname -a
dumpfiles cmdline.txt /proc/cmdline
dumpfiles os-release.txt /etc/os-release
run date.txt date -u

# Kernel log: whole, and the graphics/IOMMU lines.
run dmesg.txt dmesg
awk 'tolower($0) ~ /i915|guc|huc|dmc|drm|dmar|iommu/' "$OUT/dmesg.txt" \
  >"$OUT/dmesg-gfx.txt" 2>/dev/null

# i915 module parameters (enable_guc shows the submission setting).
dumpfiles i915-params.txt /sys/module/i915/parameters/*

# Firmware files present on the image.
run firmware.txt sh -c 'ls -l /lib/firmware/i915/ | awk "/adl|tgl/"'

# debugfs, when mounted and readable (root): uC status, capabilities, DMC,
# engines. Nothing here is written.
D=/sys/kernel/debug/dri
dumpfiles debugfs-uc.txt $D/*/gt*/uc/guc_info $D/*/gt*/uc/huc_info \
  $D/*/gt/uc/guc_info $D/*/gt/uc/huc_info
dumpfiles debugfs-info.txt $D/*/i915_capabilities $D/*/i915_dmc_info \
  $D/*/name
dumpfiles debugfs-engines.txt $D/*/i915_engine_info $D/*/gt*/engines \
  $D/*/gt/engines

# Engines from sysfs (top-level attributes of each engine directory).
for e in /sys/class/drm/card*/engine/*; do
  [ -d "$e" ] || continue
  echo "== $e"
  for a in "$e"/*; do
    [ -f "$a" ] && printf '%s=%s\n' "${a##*/}" "$(timeout "$T" cat "$a" 2>&1)"
  done
done >"$OUT/engines.txt" 2>&1
run dri-nodes.txt ls -l /dev/dri /dev/dri/by-path

# VT-d units: capability and extended capability, with ECAP.C (bit 0,
# page-walk coherency) and ECAP.SC (bit 7, snoop control) decoded.
for u in /sys/class/iommu/dmar*; do
  [ -d "$u" ] || continue
  echo "== $u"
  for a in address cap ecap version; do
    f=$u/intel-iommu/$a
    [ -f "$f" ] && printf '%s=%s\n' "$a" "$(cat "$f")"
  done
  if [ -f "$u/intel-iommu/ecap" ]; then
    ec=$(cat "$u/intel-iommu/ecap")
    printf 'ecap.C=%d ecap.SC=%d\n' $(((0x$ec >> 0) & 1)) $(((0x$ec >> 7) & 1))
  fi
  for d in "$u"/devices/*; do
    [ -e "$d" ] && echo "device ${d##*/}"
  done
done >"$OUT/iommu.txt" 2>&1

# CPU: line size and cache-maintenance instructions.
awk 'NR==1,/^$/' /proc/cpuinfo >"$OUT/cpuinfo-cpu0.txt" 2>&1
awk -F: '/^flags/ && !done {
  n = split($2, f, " "); s = "";
  for (i = 1; i <= n; i++)
    if (f[i] == "clflush" || f[i] == "clflushopt" || f[i] == "clwb") s = s " " f[i];
  print "cache instructions:" s; done = 1 }
  /^clflush size|^cache_alignment/ && !seen[$1]++ { print }' /proc/cpuinfo \
  >"$OUT/cpu-cache.txt" 2>&1
for c in /sys/devices/system/cpu/cpu0/cache/index*; do
  [ -d "$c" ] || continue
  printf '%s level=%s type=%s size=%s line=%s\n' "${c##*/}" \
    "$(cat "$c/level")" "$(cat "$c/type")" "$(cat "$c/size")" \
    "$(cat "$c/coherency_line_size")"
done >>"$OUT/cpu-cache.txt" 2>&1
command -v lscpu >/dev/null && run lscpu.txt lscpu

# PCIe: device list, and Device Control of the GPU and the Realtek NICs.
if command -v lspci >/dev/null; then
  run lspci.txt lspci -nn
  run lspci-vvv.txt lspci -vvv -nn
  {
    for dev in 00:02.0 $(lspci -D -n -d 10ec: 2>/dev/null | awk '{print $1}'); do
      echo "== $dev"
      timeout "$T" lspci -vvv -s "$dev" 2>&1 |
        awk '/^[0-9a-f]/ || /DevCap:|DevCtl:|DevSta:|RlxdOrd|NoSnoop/'
    done
  } >"$OUT/pcie-devctl.txt" 2>&1
else
  echo "lspci not found" >"$OUT/lspci.txt"
fi

# Summary of the submission mode (HG-1) and firmware versions.
{
  echo "enable_guc=$(cat /sys/module/i915/parameters/enable_guc 2>/dev/null)"
  awk 'tolower($0) ~ /guc|huc|dmc/' "$OUT/dmesg.txt" 2>/dev/null
  if awk 'tolower($0) ~ /guc/ && tolower($0) ~ /submission/ && tolower($0) ~ /enabled/ {f=1} END {exit !f}' \
    "$OUT/dmesg.txt" 2>/dev/null; then
    echo "submission: GuC (from dmesg)"
  else
    echo "submission: no 'GuC submission enabled' line in dmesg" \
      "(execlists, or dmesg not readable)"
  fi
} >"$OUT/summary.txt" 2>&1

echo "facts written to $OUT"
