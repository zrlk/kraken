#!/usr/bin/env bash
# Builds the Kraken EFI images (PE32+ EFI applications) with clang + lld-link,
# directly, without gnu-efi's ELF->PE glue (third_party/gnu-efi has only the
# BSD-licensed headers inc/; see third_party/gnu-efi/VENDOR.md). The x64
# halt loop is NASM source (stub/entry.asm), assembled with nasm -f win64, as
# are the runtime's assembler routines (stub/runtime.asm).
# The x64 AP startup code (stub/ap_entry.asm) is a flat binary for address
# 0x8000 (nasm -f bin: ORG needs it), which stub_x64.cc embeds with .incbin
# as ApBootstrap..ApBootstrapEnd. The x64 image also embeds
# Scc/Test/elf/hello1rawx64/hello1 (scc's raw-host hello1) as
# Hello1Raw..Hello1RawEnd.
#
# Usage: runtime/efi/build.sh [x64|a64|all|compdb]   (default all)
# Output: .lake/efi/<isa>/stub.efi, and .lake/efi/<isa>/esp.img: a raw FAT16
#         image with /EFI/BOOT/BOOT{X64,AA64}.EFI (runtime/efi/mkesp.py) to
#         attach to QEMU or write to a USB stick.
# DEBUG=1 builds the debug images instead, into .lake/efi/<isa>-debug/: -O0,
#         DWARF kept in the PE (lld-link /debug:dwarf; gdb reads it, a PDB
#         would not do), and KRAKEN_DEBUG, which makes the stub wait for a
#         debugger (stub.cc, runtime/efi/gdb/kraken.py).
# The stub is freestanding C++ (stub/stub.cc, ISA-independent, and
# stub/stub_x64.cc or stub/stub_a64.cc, sharing stub/stub.h): no
# exceptions, no RTTI, no C++ runtime library linked. The targets are the -windows-gnu (MinGW) ones:
# the same PE/COFF output and calling convention as -windows (MSVC), but
# Itanium C++ name mangling, which gdb demangles (it cannot read MSVC's).
# Font: .lake/efi/font/{offsets,bits}.bin, the tables generate_font.cc (built
#         for the host with $HOSTCXX, default clang++) makes from the gunzipped
#         stub/unifont_all-17.0.05.hex.gz; shared by all images, regenerated
#         only when the font or generate_font.cc changes.
#
# compile_commands: every run first writes .lake/efi/compile_commands.json, which
#         VS Code's C/C++ extension reads (.vscode/settings.json): with the same
#         flags and -D paths, it does not trip the "build with
#         runtime/efi/build.sh" #errors. It covers both ISAs and the host font
#         tool. `compdb` writes only that file, and needs only clang++ and python3.
#
# Not part of the Lean build, the merge gates or Scc/Test: a manual path.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
GNUEFI=$ROOT/third_party/gnu-efi
OUT=$ROOT/.lake/efi
CLANG=${CLANG:-clang++}
LLDLINK=${LLDLINK:-lld-link}
NASM=${NASM:-nasm}
HOSTCXX=${HOSTCXX:-clang++}
DEBUG=${DEBUG:-0}
FONT=$ROOT/runtime/efi/stub/unifont_all-17.0.05.hex.gz
HELLO1_RAW=$ROOT/Scc/Test/elf/hello1rawx64/hello1

CFLAGS_COMMON=(
  -std=c++20 -O2 -Wall -Wextra -Werror
  # Helpers that only one ISA uses are not errors on the other.
  -Wno-unused-function
  -fno-exceptions -fno-rtti -fno-threadsafe-statics -fno-use-cxa-atexit
  -ffreestanding -fshort-wchar -fno-stack-protector -fno-stack-check
  -fno-builtin -nostdlib -nostdinc
  -isystem "$("$CLANG" -print-resource-dir)/include"
  -I "$GNUEFI/inc"
  # stub.cc embeds the font tables (build_font) with .incbin.
  "-DKRAKEN_FONT_OFFSETS=\"$OUT/font/offsets.bin\""
  "-DKRAKEN_FONT_BITS=\"$OUT/font/bits.bin\""
)

FONT_TOOL_SRC=$ROOT/runtime/efi/generate_font.cc
FONT_TOOL_CMD=("$HOSTCXX" -std=c++20 -O2 -Wall -Wextra -Werror
               -o "$OUT/font/generate_font" "$FONT_TOOL_SRC")

build_font() {
  local d=$OUT/font gen=$OUT/font/generate_font
  # The font is not checked in (stub/.gitignore); stub/font.note names the
  # file and its sha256.
  if [ ! -f "$FONT" ]; then
    echo "build.sh: missing $FONT; download the file named in" \
         "runtime/efi/stub/font.note and put it there" >&2
    exit 1
  fi
  if ! (cd "$(dirname "$FONT")" && sha256sum --quiet -c font.note); then
    echo "build.sh: $FONT does not match the sha256 in runtime/efi/stub/font.note" >&2
    exit 1
  fi
  mkdir -p "$d"
  if [ ! -x "$gen" ] || [ "$FONT_TOOL_SRC" -nt "$gen" ]; then
    "${FONT_TOOL_CMD[@]}"
  fi
  if [ ! -f "$d/offsets.bin" ] || [ ! -f "$d/bits.bin" ] || [ "$FONT" -nt "$d/bits.bin" ] ||
     [ "$gen" -nt "$d/bits.bin" ]; then
    gunzip -c "$FONT" | "$gen" "$d/offsets.bin" "$d/bits.bin"
  fi
}

# Sets the caller's target, arch, boot, d, cflags and srcs for ISA $1.
isa_config() {
  case "$1" in
    x64) target=x86_64-w64-windows-gnu; arch=x86_64; boot=BOOTX64.EFI
         cflags=(-mno-red-zone -mgeneral-regs-only) ;;
    a64) target=aarch64-w64-windows-gnu; arch=aarch64; boot=BOOTAA64.EFI
         cflags=(-mgeneral-regs-only) ;;
    *) echo "unknown isa $1 (x64, a64, all, compdb)" >&2; exit 2 ;;
  esac
  d=$OUT/$1
  if [ "$DEBUG" = 1 ]; then
    # -gdwarf: a windows target defaults to CodeView. Later -O0 overrides -O2.
    d=$OUT/$1-debug
    cflags+=(-O0 -gdwarf -DKRAKEN_DEBUG)
  fi
  # stub.cc and debug.cc are ISA-independent; stub_<isa>.cc holds the rest,
  # with x64_mmu.cc and runtime_x64.cc on x64.
  srcs=(stub debug "stub_$1")
  if [ "$1" = x64 ]; then
    srcs+=(x64_mmu runtime_x64)
    cflags+=("-DKRAKEN_AP_ENTRY=\"$d/ap_entry.bin\"")
    # stub_x64.cc embeds the raw-host hello1 executable (Hello1Raw).
    cflags+=("-DKRAKEN_HELLO1_RAW=\"$HELLO1_RAW\"")
  fi
}

# Sets the caller's cmd to the compile command of stub/$1.cc, from isa_config's
# results.
compile_cmd() {
  cmd=("$CLANG" --target=$target "${CFLAGS_COMMON[@]}" -I "$GNUEFI/inc/$arch"
       "${cflags[@]}" -c "$ROOT/runtime/efi/stub/$1.cc" -o "$d/$1.obj")
}

compdb_entry() {  # FILE COMMAND...
  python3 -c 'import json, sys; print(json.dumps({"directory": sys.argv[1], "file": sys.argv[2], "arguments": sys.argv[3:]}))' \
    "$ROOT" "$@"
}

# The release images' flags, whatever $DEBUG says. The ISA-independent files
# appear once, with x64's flags; a64 adds only its own file.
write_compdb() {
  local DEBUG=0 isa src target arch boot d cflags srcs cmd
  mkdir -p "$OUT"
  {
    for isa in x64 a64; do
      isa_config "$isa"
      for src in "${srcs[@]}"; do
        if [ "$isa" = a64 ] && [ "$src" != stub_a64 ]; then continue; fi
        compile_cmd "$src"
        compdb_entry "$ROOT/runtime/efi/stub/$src.cc" "${cmd[@]}"
      done
    done
    compdb_entry "$FONT_TOOL_SRC" "${FONT_TOOL_CMD[@]}"
  } | python3 -c 'import json, sys; print(json.dumps([json.loads(l) for l in sys.stdin], indent=1))' \
    >"$OUT/compile_commands.json"
}

build_isa() {
  local isa=$1 target arch boot d cflags srcs cmd src objs=() ldflags=()
  isa_config "$isa"
  if [ "$DEBUG" = 1 ]; then ldflags=(/debug:dwarf); fi
  # x64: 16 KiB section alignment, so that the firmware loads the image, and
  # with it Hello1Raw (stub_x64.cc), on a 16 KiB boundary.
  if [ "$isa" = x64 ]; then ldflags+=(/align:16384); fi
  mkdir -p "$d"
  if [ "$isa" = x64 ]; then
    "$NASM" -f win64 -o "$d/entry.obj" "$ROOT/runtime/efi/stub/entry.asm"
    objs+=("$d/entry.obj")
    "$NASM" -f win64 -o "$d/runtime.obj" "$ROOT/runtime/efi/stub/runtime.asm"
    objs+=("$d/runtime.obj")
    "$NASM" -f bin -o "$d/ap_entry.bin" "$ROOT/runtime/efi/stub/ap_entry.asm"
  fi
  for src in "${srcs[@]}"; do
    compile_cmd "$src"
    "${cmd[@]}"
    objs+=("$d/$src.obj")
  done
  # /base: lld-link links 64-bit images at 0x140000000 (5 GB) by default, and
  # EDK2-based firmware loads an image at its link address when that memory
  # is free: above 4 GB on a machine with more than 5 GB of RAM. Linked at
  # 256 MB, the firmware tries there first; with its relocations kept
  # (/dynamicbase), it can still load the image elsewhere, which
  # CheckLoadedBelow4G (stub_x64.cc) catches if that is above 4 GB.
  "$LLDLINK" /nologo /subsystem:efi_application /entry:efi_main /nodefaultlib \
    /dynamicbase /base:0x10000000 ${ldflags[@]+"${ldflags[@]}"} /out:"$d/stub.efi" "${objs[@]}"
  python3 "$ROOT/runtime/efi/mkesp.py" "$d/esp.img" "$boot" "$d/stub.efi"
  echo "built $d/stub.efi ($(wc -c <"$d/stub.efi" | tr -d ' ') bytes; sha256 $(sha256sum "$d/stub.efi" | cut -c1-16))"
}

write_compdb
if [ "${1:-}" = compdb ]; then exit 0; fi
build_font
case "${1:-all}" in
  all) build_isa x64; build_isa a64 ;;
  *) build_isa "$1" ;;
esac
