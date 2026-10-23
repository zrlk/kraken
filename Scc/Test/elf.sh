#!/usr/bin/env bash
# The ELF layout reader (`Scc.Cert.Elf.elfParts`) against `readelf`.
#
# Usage: Scc/Test/elf.sh [--relink]
#
# For each executable of `Scc/Test/elf/` (`x`, `a`; see
# `Scc/Test/ElfTest.lean`) it evaluates the reader with `lake env lean`
# (`lake` from `$LAKE`, default `lake`) and compares the regions, the code,
# `.rodata` and the data symbols with what `readelf -SsW` reports, and checks
# that the reader refuses `a_def`. With `--relink` it first rebuilds the
# three executables from `x.s` and `a.s` (GNU `as` and `ld`, `clang` and
# `ld.lld`), and `ret0x64/ret0` from `ret0x64/ret0.s` (the x86-64 `ret0`
# certificate's text, `Spike/Test/Ret0LinkedX64.lean`); the digests in
# `ElfTest.lean` and `Ret0LinkedX64.lean` then need updating if the tools
# changed. Exits 1 on a mismatch.
set -eu
LAKE=${LAKE:-lake}
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
D=$ROOT/Scc/Test/elf
cd "$ROOT"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
if [ "${1:-}" = --relink ]; then
  as -o "$TMP/x.o" "$D/x.s" && ld -static -o "$D/x" "$TMP/x.o"
  clang --target=aarch64-linux-gnu -c -o "$TMP/a.o" "$D/a.s"
  ld.lld -static -o "$D/a" "$TMP/a.o" "$D/ins.ld"
  ld.lld -static -o "$D/a_def" "$TMP/a.o"
  as -o "$TMP/ret0.o" "$D/ret0x64/ret0.s" && ld -static -o "$D/ret0x64/ret0" "$TMP/ret0.o"
fi
cat >"$TMP/q.lean" <<'EOF'
import Scc.Cert.Elf
open Scc.Cert.Elf
def r (x : Scc.Sem.Range) : String := s!"{x.lo} {x.size}"
#eval show IO Unit from do
  for f in ["x", "a", "a_def"] do
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
for f in x a; do
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
echo "a_def error data symbol scc_stackmap below the code" >>"$TMP/want0"
sort "$TMP/want0" >"$TMP/want"
if diff "$TMP/want" "$TMP/got"; then echo "elf.sh: ok ($(wc -l <"$TMP/got") lines)"; else exit 1; fi
