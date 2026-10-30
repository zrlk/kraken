#!/usr/bin/env bash
# The ELF layout reader (`Scc.Cert.Elf.elfParts`) against `readelf`.
#
# Usage: Scc/Test/elf.sh [--relink | --relink-check]
#
# With `--relink-check` it only relinks every fixture into a temporary
# directory with its recorded command (below) and compares the result with
# the checked-in file (`cmp`), printing per fixture `same`, `differs` or
# `skip` (a tool missing; not a failure); exits 1 when one differs.
#
# For each executable of `Scc/Test/elf/` (`x`, `a`, `a_def`, `a_bid`; see
# `Scc/Test/ElfTest.lean`) it evaluates the reader with `lake env lean`
# (`lake` from `$LAKE`, default `lake`) and compares the regions, the code,
# `.rodata` and the data symbols with what `readelf -SsW` reports (`a_def`,
# linked by `ld.lld`'s default script, has `.rodata` below the code). With
# `--relink` it first rebuilds every fixture with its recorded command: the
# four executables from `x.s` and `a.s` (GNU `as` and `ld`, `clang` and
# `ld.lld`; `a_bid` with `--build-id` and `bid.ld`), `ret0x64/ret0` from
# `ret0x64/ret0.s` (the x86-64 `ret0` certificate's text,
# `Spike/Test/Ret0LinkedX64.lean`), `frame0x64/frame0` from
# `frame0x64/frame0.s` (the x86-64 `frame0` certificate's text,
# `Spike/Test/Frame0LinkedX64.lean`), `call1x64/call1` from
# `call1x64/call1.s` (the x86-64 `call1` certificate's text,
# `Spike/Test/Call1LinkedX64.lean`), `hello1x64/hello1` from
# `hello1x64/hello1.s` (the x86-64 `hello1` certificate's text, linked the
# same way, `Spike/Test/Hello1LinkedX64.lean`), `ret0x64lld/ret0` from
# `ret0x64lld/ret0.s` (the x86-64 `ret0` text again, linked by `ld.lld
# -static`, `.rodata` below the code; `Spike/Test/Ret0LldX64.lean`), `ret0a64/ret0` from `ret0a64/ret0.s`
# (the AArch64 `ret0` certificate's text, linked as `run.sh` links it,
# `Spike/Test/Ret0LinkedA64.lean`), and `hello1a64/hello1` from
# `hello1a64/hello1.s` (the AArch64 `hello1` certificate's text, linked the
# same way, `Spike/Test/Hello1LinkedA64.lean`), and `call1a64/call1` from
# `call1a64/call1.s` (the AArch64 `call1` certificate's text, linked the same
# way, `Spike/Test/Call1LinkedA64.lean`), and `wakea64/wake` from
# `wakea64/wake.s` (the AArch64 `wake` certificate's text, linked the same
# way, `Spike/Test/WakeLinkedA64Elf.lean`); the digests in `ElfTest.lean`,
# `Ret0LinkedX64.lean`, `Frame0LinkedX64.lean`, `Ret0LldX64.lean`,
# `Ret0LinkedA64.lean`, `Hello1LinkedA64.lean`, `Call1LinkedA64.lean` and
# `Call1LinkedX64.lean`, `Hello1LinkedX64.lean`, `WakeLinkedA64Elf.lean` then
# need updating if the tools changed. Exits 1 on a mismatch.
set -eu
LAKE=${LAKE:-lake}
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
D=$ROOT/Scc/Test/elf
cd "$ROOT"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
# The fixtures, the tools each needs, and its recorded command
# (`link F OUT`: write fixture F under the directory OUT).
FIXTURES="x a a_def a_bid ret0x64/ret0 ret0a64/ret0 hello1a64/hello1 call1a64/call1 frame0x64/frame0 call1x64/call1"
FIXTURES="$FIXTURES ret0x64lld/ret0 hello1x64/hello1 wakea64/wake"
tools() {
  case "$1" in
    x|ret0x64/ret0|frame0x64/frame0|call1x64/call1|hello1x64/hello1) echo "as ld" ;;
    a|a_def|a_bid|ret0a64/ret0|hello1a64/hello1|call1a64/call1|wakea64/wake) echo "clang ld.lld" ;;
    ret0x64lld/ret0) echo "as ld.lld" ;;
  esac
}
link() {
  case "$1" in
    x) as -o "$TMP/x.o" "$D/x.s" && ld -static -o "$2/x" "$TMP/x.o" ;;
    a) clang --target=aarch64-linux-gnu -c -o "$TMP/a.o" "$D/a.s" &&
       ld.lld -static -o "$2/a" "$TMP/a.o" "$D/ins.ld" ;;
    a_def) clang --target=aarch64-linux-gnu -c -o "$TMP/a.o" "$D/a.s" &&
       ld.lld -static -o "$2/a_def" "$TMP/a.o" ;;
    a_bid) clang --target=aarch64-linux-gnu -c -o "$TMP/a.o" "$D/a.s" &&
       ld.lld -static --build-id -o "$2/a_bid" "$TMP/a.o" "$D/bid.ld" ;;
    ret0x64/ret0) mkdir -p "$2/ret0x64" && as -o "$TMP/ret0.o" "$D/ret0x64/ret0.s" &&
       ld -static -o "$2/ret0x64/ret0" "$TMP/ret0.o" ;;
    frame0x64/frame0) mkdir -p "$2/frame0x64" && as -o "$TMP/frame0.o" "$D/frame0x64/frame0.s" &&
       ld -static -o "$2/frame0x64/frame0" "$TMP/frame0.o" ;;
    call1x64/call1) mkdir -p "$2/call1x64" && as -o "$TMP/call1.o" "$D/call1x64/call1.s" &&
       ld -static -o "$2/call1x64/call1" "$TMP/call1.o" ;;
    hello1x64/hello1) mkdir -p "$2/hello1x64" && as -o "$TMP/hello1.o" "$D/hello1x64/hello1.s" &&
       ld -static -o "$2/hello1x64/hello1" "$TMP/hello1.o" ;;
    ret0x64lld/ret0) mkdir -p "$2/ret0x64lld" && as -o "$TMP/ret0.o" "$D/ret0x64lld/ret0.s" &&
       ld.lld -static -o "$2/ret0x64lld/ret0" "$TMP/ret0.o" ;;
    ret0a64/ret0) mkdir -p "$2/ret0a64" &&
       clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
         -o "$2/ret0a64/ret0" "$D/ret0a64/ret0.s" ;;
    hello1a64/hello1) mkdir -p "$2/hello1a64" &&
       clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
         -o "$2/hello1a64/hello1" "$D/hello1a64/hello1.s" ;;
    call1a64/call1) mkdir -p "$2/call1a64" &&
       clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
         -o "$2/call1a64/call1" "$D/call1a64/call1.s" ;;
    wakea64/wake) mkdir -p "$2/wakea64" &&
       clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
         -o "$2/wakea64/wake" "$D/wakea64/wake.s" ;;
  esac
}
if [ "${1:-}" = --relink ]; then
  for f in $FIXTURES; do link "$f" "$D"; done
elif [ "${1:-}" = --relink-check ]; then
  # Relink every fixture into a temporary directory with its recorded
  # command and compare it with the checked-in file, byte for byte: drift
  # of the toolchain shows here before the digests in the tests go stale.
  # A fixture whose tools are missing is skipped, not failed.
  bad=0
  for f in $FIXTURES; do
    miss=""
    for t in $(tools "$f"); do command -v "$t" >/dev/null 2>&1 || miss="$miss $t"; done
    if [ -n "$miss" ]; then echo "skip     $f: toolchain missing:$miss"; continue; fi
    mkdir -p "$TMP/re"
    if ! link "$f" "$TMP/re" 2>"$TMP/link.err"; then
      echo "differs  $f: the recorded command fails: $(head -c 500 "$TMP/link.err")"; bad=1; continue
    fi
    if cmp -s "$TMP/re/$f" "$D/$f"; then echo "same     $f"
    else echo "differs  $f: $(sha256sum <"$TMP/re/$f" | cut -c1-16)… relinked, $(sha256sum <"$D/$f" | cut -c1-16)… checked in"; bad=1; fi
  done
  [ $bad = 0 ] && { echo "elf.sh: relink check ok"; exit 0; }
  echo "elf.sh: relink check: a fixture differs (toolchain drift? relink with --relink and update the digests)"; exit 1
fi
cat >"$TMP/q.lean" <<'EOF'
import Scc.Cert.Elf
open Scc.Cert.Elf
def r (x : Scc.Sem.Range) : String := s!"{x.lo} {x.size}"
#eval show IO Unit from do
  for f in ["x", "a", "a_def", "a_bid"] do
    match elfParts (← IO.FS.readBinFile s!"Scc/Test/elf/{f}") with
    | .error e => IO.println s!"{f} error {e}"
    | .ok e =>
      IO.println s!"{f} code {r e.code}"
      IO.println s!"{f} rodata {r e.rodata}"
      IO.println s!"{f} heap {r e.heap}"
      IO.println s!"{f} pinned {r e.pinned}"
      IO.println s!"{f} pool {r e.stackPool}"
      for (n, a) in e.symbols do IO.println s!"{f} sym {n} {a}"
EOF
"$LAKE" env lean "$TMP/q.lean" | sort >"$TMP/got"
# The same from readelf.
for f in x a a_def a_bid; do
  # Name, type, address, offset, size after the `[Nr]` column.
  readelf -SW "$D/$f" | sed -n 's/^ *\[ *[0-9]*\] *//p' | awk -v f=$f '
    $1 == ".text" { printf "%s code %d %d\n", f, strtonum("0x" $3), strtonum("0x" $5) }
    $1 == ".rodata" { printf "%s rodata %d %d\n", f, strtonum("0x" $3), strtonum("0x" $5) }'
  readelf -sW "$D/$f" | awk -v f=$f '
    $5 == "LOCAL" && ($4 == "NOTYPE" || $4 == "OBJECT") && $8 !~ /^\$/ { print }' |
  while read -r _ val size _ _ _ ndx name; do
    sec=$(readelf -SW "$D/$f" | sed -n "s/^ *\\[ *$ndx\\] *\\([^ ]*\\).*/\\1/p")
    case "$sec" in .data|.bss) ;; *) continue ;; esac
    v=$((16#$val))
    case "$name" in
      scc_rt_heap) echo "$f heap $v $size" ;;
      scc_rt_pinned) echo "$f pinned $v $size" ;;
      scc_rt_stacks) echo "$f pool $v $size" ;;
    esac
    echo "$f sym $name $v"
  done
done | awk '{ if ($2 != "sym" && $4 ~ /^0x/) $4 = strtonum($4); print }' >"$TMP/want0"
sort "$TMP/want0" >"$TMP/want"
if diff "$TMP/want" "$TMP/got"; then echo "elf.sh: ok ($(wc -l <"$TMP/got") lines)"; else exit 1; fi
