#!/usr/bin/env bash
# Boots .lake/efi/<isa>/esp.img (built by build.sh) in QEMU with a display
# window: the way to watch the stub on screen. From WSL it runs the Windows QEMU
# through Windows interop; on macOS, the native one. qemu_smoke.py is the
# headless check; this only launches.
#
# Usage: runtime/efi/qemu_window.sh [--gdb] [x64|a64]   (default x64)
# QEMU and firmware, from WSL: $KRAKEN_WIN_QEMU_DIR (default /mnt/c/Program
# Files/qemu), with the edk2 images QEMU's Windows installer puts in its share/.
# On macOS: qemu-system-* from the PATH (brew install qemu), with the edk2
# images in share/qemu next to its bin/.
# The image is attached with snapshot=on (never written); the vars store is
# read-only. Serial output also goes to this terminal. x64 runs 4 CPUs (the
# stub itself uses only the boot CPU) and has an Intel IOMMU, so that the
# firmware provides an ACPI DMAR table (QEMU wants intel-iommu before the
# other PCI devices). x64 uses -cpu max: EnterRuntime (entry.asm) sets
# CR4.OSXSAVE and enables AVX with xsetbv, which qemu64 (no XSAVE) faults on.
# a64 uses ramfb: the stub draws to a linear framebuffer
# (InitVideo), and edk2's virtio-gpu driver has none (PixelBltOnly, which
# InitVideo rejects as "Invalid pixel format"). The image is rebuilt first (build.sh)
# when it is missing or older than any of build.sh's inputs.
#
# --gdb boots the debug image (DEBUG=1 build.sh: .lake/efi/<isa>-debug/) and
# opens QEMU's gdb server on port $KRAKEN_GDB_PORT (default 1234). From WSL it
# listens on all of the Windows host's interfaces: QEMU runs on Windows and gdb
# in WSL, which reaches the host at its default gateway, not at localhost. On
# macOS it listens on localhost only. Then attach with
# runtime/efi/gdb/kraken.py (kraken-attach) or VS Code's "Kraken EFI stub".
#
# Not part of the Lean build, the merge gates or Scc/Test: a manual path.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
if [ "$(uname -s)" = Darwin ]; then
  QBIN=$(dirname "$(command -v qemu-system-x86_64 || { echo "no qemu-system-x86_64 on the PATH: brew install qemu" >&2; exit 1; })")
  QFW=$QBIN/../share/qemu
  EXE=
  GDB_BIND=127.0.0.1
  w() { printf '%s' "$1"; }
else
  QBIN=${KRAKEN_WIN_QEMU_DIR:-/mnt/c/Program Files/qemu}
  QFW=$QBIN/share
  EXE=.exe
  GDB_BIND=0.0.0.0
  w() { wslpath -w "$1"; }
fi
gdb=0
if [ "${1:-}" = --gdb ]; then gdb=1; shift; fi
isa=${1:-x64}
case "$isa" in x64|a64) ;; *) echo "unknown isa $isa (x64, a64)" >&2; exit 2 ;; esac
if [ $gdb = 1 ]; then img=$ROOT/.lake/efi/$isa-debug/esp.img; else img=$ROOT/.lake/efi/$isa/esp.img; fi
# Rebuild the image when it is missing or older than any input of build.sh.
E=$ROOT/runtime/efi
if [ ! -f "$img" ] || [ -n "$(find "$E/stub" "$E/build.sh" "$E/mkesp.py" "$E/generate_font.cc" \
     "$ROOT/third_party/gnu-efi/inc" "$ROOT/Scc/Test/elf/hello1rawx64/hello1" -newer "$img" -print -quit)" ]; then
  DEBUG=$gdb "$E/build.sh" "$isa" >&2
fi

common=(-accel tcg -m 256M -nic none -serial stdio
        -drive "if=none,id=esp,format=raw,snapshot=on,file=$(w "$img")"
        -device virtio-blk-pci,drive=esp)
if [ $gdb = 1 ]; then
  common+=(-gdb "tcp:$GDB_BIND:${KRAKEN_GDB_PORT:-1234}")
  if [ -n "$EXE" ]; then
    echo "gdb server on port ${KRAKEN_GDB_PORT:-1234}; from WSL: $(ip route show default | awk '{print $3}')" >&2
  else
    echo "gdb server on localhost:${KRAKEN_GDB_PORT:-1234}" >&2
  fi
fi
case "$isa" in
  x64) exec "$QBIN/qemu-system-x86_64$EXE" -name kraken-efi-x64 -M q35 -cpu max -smp 4 \
         -drive "if=pflash,format=raw,readonly=on,file=$(w "$QFW/edk2-x86_64-code.fd")" \
         -drive "if=pflash,format=raw,readonly=on,file=$(w "$QFW/edk2-i386-vars.fd")" \
         -device intel-iommu \
         "${common[@]}" ;;
  a64) exec "$QBIN/qemu-system-aarch64$EXE" -name kraken-efi-a64 -M virt -cpu max \
         -bios "$(w "$QFW/edk2-aarch64-code.fd")" \
         -device ramfb -device qemu-xhci -device usb-kbd \
         "${common[@]}" ;;
  *) echo "unknown isa $isa (x64, a64)" >&2; exit 2 ;;
esac
