#!/bin/sh
# Realtek NIC facts: read-only collection of driver, register, statistics,
# offload, ring, link, PCI and interrupt facts for every Realtek 10ec:8168
# function (the board has two RTL8168h ports, driven by r8169).
#
# Usage: facts.sh OUTDIR
#
# Only reads: ethtool query options, ip, lspci, files under /proc and /sys,
# dmesg, and a checksum of the firmware file. It never changes a setting,
# never unbinds or reloads the driver and never brings a link up or down.
# Missing tools or permissions are recorded in the output and skipped. Run
# as root for the register dump, the PCI config space and dmesg.

set -u

if [ $# -ne 1 ]; then
  echo "usage: facts.sh OUTDIR" >&2
  exit 1
fi
OUT=$1
mkdir -p "$OUT" || exit 1

T=10 # seconds per command
# Overridable to try the script on another machine's NIC.
VENDOR=${NIC_VENDOR:-0x10ec}
DEVICE=${NIC_DEVICE:-0x8168}
FW=/lib/firmware/rtl_nic/rtl8168h-2.fw

# run FILE CMD...: run CMD with a time bound, stdout and stderr into FILE,
# then its exit status. A missing tool is recorded instead of run.
run() {
  file=$1
  shift
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "$1: not found" >"$file"
    return
  fi
  timeout "$T" "$@" >"$file" 2>&1
  echo "exit=$?" >>"$file"
}

run "$OUT/uname.txt" uname -a
run "$OUT/dmesg-r8169.txt" sh -c 'dmesg | awk "/r8169|rtl_nic/"'
run "$OUT/interrupts.txt" sh -c 'awk "NR==1 || /enp|eth|r8169/" /proc/interrupts'
run "$OUT/ip-link.txt" ip -d link
run "$OUT/r8169-module.txt" sh -c \
  'cat /sys/module/r8169/version 2>/dev/null; ls /sys/module/r8169/parameters 2>/dev/null; modinfo r8169 2>&1 | awk "/^(filename|version|firmware|vermagic):/"'

# Firmware: checksum only, the file is not copied.
if [ -f "$FW" ]; then
  run "$OUT/firmware.txt" sha256sum "$FW"
  ls -l "$FW" >>"$OUT/firmware.txt" 2>&1
else
  echo "$FW: not present" >"$OUT/firmware.txt"
  ls -l /lib/firmware/rtl_nic/ >>"$OUT/firmware.txt" 2>&1
fi

found=0
for dev in /sys/bus/pci/devices/*; do
  [ -f "$dev/vendor" ] || continue
  [ "$(cat "$dev/vendor")" = "$VENDOR" ] || continue
  [ "$(cat "$dev/device")" = "$DEVICE" ] || continue
  found=$((found + 1))
  bdf=${dev##*/}
  D=$OUT/$bdf
  mkdir -p "$D"

  # PCI: full config space and capabilities, and the sysfs attributes.
  run "$D/lspci.txt" lspci -vvv -xxxx -nn -s "$bdf"
  for a in msi_irqs irq resource current_link_speed current_link_width \
    max_link_speed max_link_width revision subsystem_vendor \
    subsystem_device; do
    p=$dev/$a
    if [ -d "$p" ]; then
      for f in "$p"/*; do
        [ -e "$f" ] && printf '%s/%s=%s\n' "$a" "${f##*/}" "$(cat "$f" 2>&1)"
      done
    elif [ -e "$p" ]; then
      printf '%s=%s\n' "$a" "$(tr '\n' ' ' <"$p" 2>&1)"
    fi
  done >"$D/sysfs.txt" 2>&1
  readlink "$dev/driver" >>"$D/sysfs.txt" 2>&1

  # Network interface(s) of this function.
  real=$(readlink -f "$dev")
  for n in /sys/class/net/*; do
    case $(readlink -f "$n/device") in
    "$real" | "$real"/*) ;;
    *) continue ;;
    esac
    ifc=${n##*/}
    echo "$ifc" >>"$D/interfaces.txt"
    run "$D/$ifc-ethtool-i.txt" ethtool -i "$ifc"
    run "$D/$ifc-ethtool-d.txt" ethtool -d "$ifc"
    run "$D/$ifc-ethtool-d-hex.txt" ethtool -d "$ifc" hex on
    # Raw register dump (the driver returns 256 bytes of MMIO), binary.
    if command -v ethtool >/dev/null 2>&1; then
      timeout "$T" ethtool -d "$ifc" raw on >"$D/$ifc-regs.bin" \
        2>"$D/$ifc-regs.err"
      echo "exit=$?" >>"$D/$ifc-regs.err"
    fi
    run "$D/$ifc-ethtool-S.txt" ethtool -S "$ifc"
    run "$D/$ifc-ethtool-k.txt" ethtool -k "$ifc"
    run "$D/$ifc-ethtool-c.txt" ethtool -c "$ifc"
    run "$D/$ifc-ethtool-g.txt" ethtool -g "$ifc"
    run "$D/$ifc-ethtool.txt" ethtool "$ifc"
    run "$D/$ifc-ip-link.txt" ip -d -s link show dev "$ifc"
    # shellcheck disable=SC2016 # $0 is awk's, not the shell's
    run "$D/$ifc-interrupts.txt" awk -v i="$ifc" 'NR==1 || index($0, i)' \
      /proc/interrupts
  done
  [ -f "$D/interfaces.txt" ] || echo "no network interface bound" \
    >"$D/interfaces.txt"
done

echo "functions found: $found ($VENDOR:$DEVICE)" >"$OUT/summary.txt"
echo "nic facts written to $OUT ($found functions)"
