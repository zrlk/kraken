#!/usr/bin/env bash
# Tests of Scc/Test/certify.sh: its verdict and exit status on x64 `ret0`
# (certified with --instantiate, placement decided without; the theorem over
# `Accepted1` with `prog_mainFrame1`, and with CERTIFY_X64_FRAGMENT=0 the one
# over `Accepted0`), on x64 `ifsub1` (certified, outside `Accepted0`), on two damaged copies of that executable (a truncated
# file; `scc_rt_heap`'s symbol size patched to 0), on a program outside the
# certified fragment (non-tail recursion) and on arm `ret0` (`ld.lld`'s
# default link: `.rodata` below the code, a build-id note; certified with
# --instantiate, placement decided without), and -v on x64 `ret0` (the
# command trace names scc and `lake env lean`; the verdict, up to time and
# memory, and the status are those without -v), and hello1 on both ISAs (the
# registry; cases below).  `lake` from `$LAKE`, default
# `lake`.  Prints one line per case and exits 1 when a case differs.
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
# x64 instantiates the theorem over `Accepted1` with `main`'s frame bound.
thm() { # case, post file, expected theorem, expected frame-bound flag (1/0)
  local t=$1 f=$2 want=$3 hfr=$4 n
  n=$(grep -c "^theorem prog_mainFrame1 " "$f" 2>/dev/null)
  if grep -q "^  Spike\.Lib\.LowerX64\.$want (cfg := config)" "$f" && [ "$n" = "$hfr" ]; then
    echo "ok   $t: $want"
  else echo "FAIL $t: not $want (prog_mainFrame1: $n)"; fails=$((fails+1)); fi
}
thm "x64 ret0" .lake/certify/x64/ret0/ret0.post.lean x64_scc_correctE_text_closedAt1 1
run 0 "certified" --instantiate Scc/Test/ifsub1.w
thm "x64 ifsub1" .lake/certify/x64/ifsub1/ifsub1.post.lean x64_scc_correctE_text_closedAt1 1
# An `Accepted0` program without `MainFrame1Ok` takes the theorem over
# `Accepted0` (forced: no `Accepted0` program found has a frame above 4096
# bytes; `maxAdds0` checked `+`s give 4064, evidence only, not a proof).
CERTIFY_X64_FRAGMENT=0 run 0 "certified" --instantiate Scc/Test/ret0.w
# The path taken is in T.post.lean's header.
if grep -q '^-- certify.sh: theorem path: closedAt fallback ' .lake/certify/x64/ret0/ret0.post.lean; then
  echo "ok   x64 ret0, CERTIFY_X64_FRAGMENT=0: header names the closedAt fallback"
else echo "FAIL x64 ret0, CERTIFY_X64_FRAGMENT=0: header does not name the closedAt fallback"; fails=$((fails+1)); fi
thm "x64 ret0, CERTIFY_X64_FRAGMENT=0" .lake/certify/x64/ret0/ret0.post.lean x64_scc_correctE_text_closedAt 0
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
run 10 "placement decided" --arch arm Scc/Test/ret0.w
run 0 "certified" --arch arm --instantiate Scc/Test/ret0.w
# Programs that take their thread id and spawn: `placeOK2At` decided
# (`Scc/Cert/Spawn*.lean`), no theorem to instantiate.
for A in x64 arm; do
  run 10 "placement decided" --arch $A Scc/Test/wake.w
  run 10 "placement decided" --arch $A Scc/Test/hello.w
done
# wake (the registry's arm entry): certified at run.sh's link; on x64 no proved theorem.
run 0 "certified" --arch arm --instantiate Scc/Test/wake.w
run 3 "not certifiable: no proved theorem for a program that takes its thread id" --instantiate Scc/Test/wake.w

# hello1 (the registry), both ISAs: certified at run.sh's link and at a link moved by the
# linker (--elf); exit 3 naming the component at a link above 4 GiB (A1); exit 3 for another
# Accepted2 program (`hello1L.w`, the registry message) and for hello1.w with one byte changed
# (`13` -> `12`: no proved theorem).
sed 's/let n = 13/let n = 12/' Scc/Test/hello1.w >"$N/hello1.w"
cmp -s Scc/Test/hello1.w "$N/hello1.w" && { echo "FAIL hello1 variant: unchanged"; fails=$((fails+1)); }
for a in x64 arm; do
  s=Scc/Test/elf/hello1${a/arm/a64}/hello1.s
  if [ $a = x64 ]; then
    as -o "$N/h1.o" "$s" && ld -static -Ttext-segment=0x800000 -o "$N/h1_${a}_moved" "$N/h1.o" \
      && ld -static -Ttext-segment=0x100000000 -o "$N/h1_${a}_high" "$N/h1.o"
  else
    for b in moved:0x800000 high:0x100000000; do
      clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
        -Wl,--image-base=${b#*:} -o "$N/h1_${a}_${b%%:*}" "$s"
    done
  fi
  run 0 "certified" --arch $a --instantiate Scc/Test/hello1.w
  run 0 "certified" --arch $a --instantiate --elf "$ROOT/$N/h1_${a}_moved" Scc/Test/hello1.w
  run 3 "not certifiable: placeOKAt fails at the executable's layout (component A1" \
    --arch $a --instantiate --elf "$ROOT/$N/h1_${a}_high" Scc/Test/hello1.w
  run 3 "not certifiable: outside the certified fragment (Accepted2 programs other than Scc/Test/hello1.w" \
    --arch $a --instantiate Scc/Test/hello1L.w
  run 3 "not certifiable: outside the certified fragment (not Scc.Lower.Accepted1; no proved theorem" \
    --arch $a --instantiate "$N/hello1.w"
done

# -v on x64 ret0: the `+ cd DIR && CMD` trace on stderr names scc and `lake env lean`; the
# verdict line (time and memory masked) and the exit status are those of the run without -v.
mask() { printf '%s\n' "$1" | tail -n 1 | sed -E 's/\([0-9.]+ s, [0-9]+ MB RssAnon peak\)/(TIME, MEM)/'; }
plain=$(bash "$C" --instantiate Scc/Test/ret0.w 2>&1); prc=$?
plain=$(mask "$plain")
verr=$(bash "$C" -v --instantiate Scc/Test/ret0.w 2>&1 >"$N/v.out"); vrc=$?
vout=$(cat "$N/v.out")
vlast=$(mask "$vout")
if printf '%s\n' "$verr" | grep -q '^+ cd /.* && .*/scc --arch x64 ' &&
   printf '%s\n' "$verr" | grep -q '^+ cd /.* && .*lake env lean /' &&
   [ "$vlast" = "$plain" ] && [ "$vrc" = "$prc" ]; then
  echo "ok   -v --instantiate Scc/Test/ret0.w: $vlast (status $vrc, as without -v)"
else
  echo "FAIL -v --instantiate Scc/Test/ret0.w (status $vrc, want $prc): '$vlast' vs '$plain'"
  fails=$((fails+1))
fi

[ "$fails" = 0 ] && echo "certify_test: all passed" || { echo "certify_test: $fails failed"; exit 1; }
