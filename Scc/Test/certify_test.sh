#!/usr/bin/env bash
# Tests of Scc/Test/certify.sh: its verdict and exit status on x64 `ret0`
# (certified with --instantiate, placement decided without), on two damaged copies of that executable (a truncated
# file; `scc_rt_heap`'s symbol size patched to 0), on a program outside the
# certified fragment (non-tail recursion) and on arm `ret0` (not yet
# supported).  `lake` from `$LAKE`, default `lake`.  Prints one line per case
# and exits 1 when a case differs.
set -u
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$ROOT"
C=Scc/Test/certify.sh
N=.lake/certify/neg
fails=0

run() { # expected-status expected-verdict-prefix args...
  local want=$1 pre=$2; shift 2
  local out rc
  out=$(bash "$C" "$@" 2>&1); rc=$?
  out=$(printf '%s\n' "$out" | tail -n 1)
  case "$out" in
    *": $pre"*) [ "$rc" = "$want" ] && { echo "ok   $*: $out"; return; } ;;
  esac
  echo "FAIL $* (status $rc, want $want, '$pre'): $out"; fails=$((fails+1))
}

run 0 "certified" --instantiate Scc/Test/ret0.w
run 10 "placement decided" Scc/Test/ret0.w
rm -rf "$N"; mkdir -p "$N"
cp .lake/certify/x64/ret0/ret0 "$N/good"
head -c 12288 "$N/good" >"$N/trunc"
python3 - "$N/good" "$N/heap0" <<'EOF'
import struct, sys
b = bytearray(open(sys.argv[1], 'rb').read())
shoff, = struct.unpack_from('<Q', b, 0x28)
shentsize, shnum = struct.unpack_from('<HH', b, 0x3a)
sh = [struct.unpack_from('<IIQQQQIIQQ', b, shoff + i * shentsize) for i in range(shnum)]
done = False
for s in sh:
    if s[1] != 2:  # SHT_SYMTAB
        continue
    strtab = sh[s[6]]
    for off in range(s[4], s[4] + s[5], 24):
        name, = struct.unpack_from('<I', b, off)
        p = strtab[4] + name
        if bytes(b[p:b.index(0, p)]) == b'scc_rt_heap':
            struct.pack_into('<Q', b, off + 16, 0)
            done = True
assert done, 'scc_rt_heap not found'
open(sys.argv[2], 'wb').write(b)
EOF
run 1 "failed: the ELF reader refuses ret0: truncated" --elf "$ROOT/$N/trunc" Scc/Test/ret0.w
run 1 "failed: the ELF reader refuses ret0: scc_rt_heap has size 0" --elf "$ROOT/$N/heap0" Scc/Test/ret0.w
run 3 "not certifiable" Scc/Test/deeprec.w
run 4 "not yet supported" --arch arm Scc/Test/ret0.w

[ "$fails" = 0 ] && echo "certify_test: all passed" || { echo "certify_test: $fails failed"; exit 1; }
