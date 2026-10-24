#!/usr/bin/env bash
# AArch64 code alignment after the link: every program under Scc/Test/ that
# scc accepts, compiled with `scc --arch arm` and linked as Scc/Test/run.sh
# links AArch64 binaries (clang with lld, `ld.lld`'s default script), has
# `.text`, and the entry point at its start, on a 16-byte boundary (the
# placement check requires it of the code region).
#
# `ld.lld` puts `.rodata` below `.text` and starts `.text` at `.text`'s own
# alignment past it; the emitter opens `.text` with `.p2align 4` for this.
# With `.p2align 2` there, `.text` started 8 past a 16-byte boundary when
# `.rodata` ended there. The programs in REGRESS are such cases (their
# `.rodata` ends 8 mod 16, checked, so they keep testing it).
#
# Usage: Scc/Test/textalign.sh
# Exit status 0 when every program is aligned, 1 otherwise. `scc` is built
# first (`lake` from `$LAKE`); clang, lld and readelf must be on PATH.
set -u
LAKE=${LAKE:-lake}
cd "$(dirname "$0")/../.."
REGRESS="hello1 tailwide"
"$LAKE" build scc >/dev/null || { echo "textalign: lake build scc failed"; exit 1; }
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT

# The address and size of section $2 of ELF file $1, in hex (empty if none).
sec() { readelf -SW "$1" | awk -v s="$2" '{ sub(/^ *\[ *[0-9]+\] */, "") } $1 == s { print $3, $5 }'; }

bad=0; n=0
for w in Scc/Test/*.w; do
  p=$(basename "$w" .w)
  .lake/build/bin/scc --arch arm -o "$T/$p.s" "$w" 2>/dev/null || continue
  n=$((n + 1))
  if ! clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
      -o "$T/$p" "$T/$p.s" 2>"$T/$p.err"; then
    echo "FAIL $p: link: $(head -n 1 "$T/$p.err")"; bad=1; continue
  fi
  read -r tx _ <<<"$(sec "$T/$p" .text)"
  read -r ro rs <<<"$(sec "$T/$p" .rodata)"
  entry=$(readelf -hW "$T/$p" | awk '/Entry point address/ { print $4 }')
  if [ -z "$tx" ] || [ $((0x$tx % 16)) != 0 ] || [ $((entry)) != $((0x$tx)) ]; then
    echo "FAIL $p: .text at 0x$tx, entry $entry"; bad=1; continue
  fi
  for r in $REGRESS; do
    if [ "$r" = "$p" ] && { [ -z "$ro" ] || [ $(((0x$ro + 0x$rs) % 16)) != 8 ]; }; then
      echo "FAIL $p: .rodata no longer ends 8 mod 16 (0x$ro + 0x$rs): pick another REGRESS program"; bad=1
    fi
  done
done
for r in $REGRESS; do
  [ -f "$T/$r" ] || { echo "FAIL $r: not compiled"; bad=1; }
done
[ $bad = 0 ] && { echo "textalign: ok ($n programs, .text 16-aligned)"; exit 0; }
echo "textalign: FAILED"; exit 1
