#!/bin/bash
# Freeze the herd7 litmus corpora and cache the oracle's output.
#
# Copies the test files from a herdtools7 checkout into this directory and
# runs herd7 on each, storing the output next to the test as `<name>.herd`
# (with the `Time` and `Hash` lines dropped, so the files are stable).
#
# Usage: refresh.sh <herdtools7-checkout> <herd7-binary>
#
# The oracle revision is recorded in ORACLE.txt.
set -euo pipefail

SRC=${1:?herdtools7 checkout}
HERD=${2:?herd7 binary}
DST=$(cd "$(dirname "$0")" && pwd)

copy_suite() {  # <suite dir under SRC> <dest subdir> <herd flags...>
  local src="$SRC/$1" dst="$DST/$2" name="$2"; shift 2
  mkdir -p "$dst"
  local list
  if [ -f "$src/@all" ]; then
    list=$(grep -v '^#' "$src/@all" | sed '/^$/d')
  else
    list=$(cd "$src" && ls *.litmus)
  fi
  for t in $list; do
    cp "$src/$t" "$dst/$t"
    if [ -f "$src/$t.expected" ]; then cp "$src/$t.expected" "$dst/$t.expected"; fi
    ( cd "$src" && "$HERD" "$@" "$t" 2>/dev/null || true ) \
      | grep -v '^Time \|^Hash=' > "$dst/$t.herd" || true
  done
  if [ -f "$src/kinds.txt" ]; then cp "$src/kinds.txt" "$dst/kinds.txt"; fi
  if [ -f "$src/ci.cfg" ]; then cp "$src/ci.cfg" "$dst/ci.cfg"; fi
  echo "$name: $(echo "$list" | wc -w) tests"
}

copy_suite catalogue/aarch64/tests aarch64 -kinds kinds.txt
copy_suite catalogue/x86_64/tests x86_64 -kinds kinds.txt
copy_suite catalogue/x86/tests x86
copy_suite herd/tests/instructions/AArch64 aarch64-instructions -conf ci.cfg
copy_suite herd/tests/instructions/X86_64 x86_64-instructions

{
  echo "herd7: $("$HERD" -version)"
  echo "herdtools7 revision: $(cd "$SRC" && git rev-parse HEAD) ($(cd "$SRC" && git log -1 --format=%ad --date=short))"
  echo "frozen: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "$DST/ORACLE.txt"
cat "$DST/ORACLE.txt"
