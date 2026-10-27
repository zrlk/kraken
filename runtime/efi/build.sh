#!/usr/bin/env bash
# Builds the Kraken EFI images (PE32+ EFI applications) with clang + lld-link,
# directly, without gnu-efi's ELF->PE glue (third_party/gnu-efi has only the
# BSD-licensed headers inc/; see third_party/gnu-efi/VENDOR.md). The x64
# halt loop is NASM source (stub/halt_x64.asm), assembled with nasm -f win64.
#
# Usage: runtime/efi/build.sh [x64|a64|all]   (default all)
# Output: .lake/efi/<isa>/stub.efi, and .lake/efi/<isa>/esp.img: a raw FAT16
#         image with /EFI/BOOT/BOOT{X64,AA64}.EFI (runtime/efi/mkesp.py) to
#         attach to QEMU or write to a USB stick.
#
# Not part of the Lean build, the merge gates or Scc/Test: a manual path.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
GNUEFI=$ROOT/third_party/gnu-efi
OUT=$ROOT/.lake/efi
CLANG=${CLANG:-clang}
LLDLINK=${LLDLINK:-lld-link}
NASM=${NASM:-nasm}

CFLAGS_COMMON=(
  -std=c11 -O2 -Wall -Wextra -Werror
  -ffreestanding -fshort-wchar -fno-stack-protector -fno-stack-check
  -fno-builtin -nostdlib -nostdinc
  -isystem "$("$CLANG" -print-resource-dir)/include"
  -I "$GNUEFI/inc"
)

build_isa() {
  local isa=$1 target arch boot cflags=()
  case "$isa" in
    x64) target=x86_64-unknown-windows; arch=x86_64; boot=BOOTX64.EFI
         cflags=(-mno-red-zone -mgeneral-regs-only) ;;
    a64) target=aarch64-unknown-windows; arch=aarch64; boot=BOOTAA64.EFI
         cflags=(-mgeneral-regs-only) ;;
    *) echo "unknown isa $isa (x64, a64, all)" >&2; exit 2 ;;
  esac
  local d=$OUT/$isa objs=()
  mkdir -p "$d"
  if [ "$isa" = x64 ]; then
    "$NASM" -f win64 -o "$d/halt.obj" "$ROOT/runtime/efi/stub/halt_x64.asm"
    objs+=("$d/halt.obj")
  fi
  "$CLANG" --target=$target "${CFLAGS_COMMON[@]}" -I "$GNUEFI/inc/$arch" "${cflags[@]}" \
    -c "$ROOT/runtime/efi/stub/stub.c" -o "$d/stub.obj"
  "$LLDLINK" /nologo /subsystem:efi_application /entry:efi_main /nodefaultlib \
    /dynamicbase /out:"$d/stub.efi" "$d/stub.obj" "${objs[@]}"
  python3 "$ROOT/runtime/efi/mkesp.py" "$d/esp.img" "$boot" "$d/stub.efi"
  echo "built $d/stub.efi ($(stat -c %s "$d/stub.efi") bytes; sha256 $(sha256sum "$d/stub.efi" | cut -c1-16))"
}

case "${1:-all}" in
  all) build_isa x64; build_isa a64 ;;
  *) build_isa "$1" ;;
esac
