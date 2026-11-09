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
# registry; cases below), and hello (the registry: certified on arm, on x64
# when its theorem's module is in the checkout; cases below).  `lake` from `$LAKE`, default
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
# wake (the registry's entry), both ISAs: certified at run.sh's link.
run 0 "certified" --arch arm --instantiate Scc/Test/wake.w
run 0 "certified" --arch x64 --instantiate Scc/Test/wake.w

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

# hello (the registry's entry): certified on arm at its theorem's link (`.text` and `.rodata`
# placed as `Scc/Test/elf/helloa64/hello`); exit 3 at arm's default `ld.lld` link (--elf: not
# the theorem's executable) and for hello.w with one byte changed (`13` -> `12`: no proved
# theorem). On x64, certified at run.sh's link and exit 3 at a link moved by the linker (--elf:
# not the theorem's executable) when `Spike/Test/HelloLinkedX64Root.lean` is in the checkout;
# else exit 3 in both (no proved theorem: the module is not in this checkout).
run 0 "certified" --arch arm --instantiate Scc/Test/hello.w
clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld \
  -o "$N/hello_arm_default" Scc/Test/elf/helloa64/hello.s
run 3 "not certifiable: no proved theorem at this executable's layout" \
  --arch arm --instantiate --elf "$ROOT/$N/hello_arm_default" Scc/Test/hello.w
mkdir -p "$N/hv"
sed 's/let n = 13/let n = 12/' Scc/Test/hello.w >"$N/hv/hello.w"
cmp -s Scc/Test/hello.w "$N/hv/hello.w" && { echo "FAIL hello variant: unchanged"; fails=$((fails+1)); }
run 3 "not certifiable: no proved theorem for a program that takes its thread id" \
  --arch arm --instantiate "$N/hv/hello.w"
as -o "$N/hello_x64.o" Scc/Test/elf/hellox64/hello.s \
  && ld -static -Ttext-segment=0x800000 -o "$N/hello_x64_moved" "$N/hello_x64.o"
if [ -f Spike/Test/HelloLinkedX64Root.lean ]; then
  run 0 "certified" --arch x64 --instantiate Scc/Test/hello.w
  run 3 "not certifiable: no proved theorem at this executable's layout" \
    --arch x64 --instantiate --elf "$ROOT/$N/hello_x64_moved" Scc/Test/hello.w
else
  X64NO="not certifiable: no proved theorem for a program that takes its thread id or spawns (hello on x64: \
Spike/Test/HelloLinkedX64Root.lean is not in this checkout"
  run 3 "$X64NO" --arch x64 --instantiate Scc/Test/hello.w
  run 3 "$X64NO" --arch x64 --instantiate --elf "$ROOT/$N/hello_x64_moved" Scc/Test/hello.w
fi

# The linker matrix (--elf): hello1 (the registry), ret0 (`Accepted0`) and ifsub1 (`Accepted1`,
# outside `Accepted0`), each linked from its listing by every linker at hand. x64: GNU ld (bfd),
# gold and ld.lld at their defaults. arm: only ld.lld links AArch64 here (no aarch64 binutils), so
# the layout varies instead: lld's default, the 3-pin of `Scc/Test/a64link.sh`, and the image above
# 4 GiB. Each case is certified or refused with a named reason, never anything else:
#   - gold puts `.rodata` in the executable PT_LOAD: the reader refuses (exit 1);
#   - x64 ld.lld places `.text` right after `.rodata`, at the listing's alignment (1): for hello1
#     (592 bytes of `.rodata`) the code base is not 16-aligned and the reader refuses (`wfB`, exit 1);
#     for ret0 and ifsub1 it is aligned and they are certified. This outcome depends on lld's
#     default section order (`.rodata` before `.text`) and on the size of `.rodata`;
#   - arm above 4 GiB: `placeOKAt` fails, component A1 (exit 3).
# The expected verdicts were recorded with GNU ld (GNU Binutils for Debian) 2.47, GNU gold (GNU
# Binutils for Debian 2.44) 1.16, Debian LLD 21.1.8 and Debian clang version 21.1.8 (the versions in
# use are printed first). A linker (ld.bfd, ld.gold, ld.lld) or the AArch64 clang (`A64_CC`, which
# links with ld.lld) that is not installed skips every case that needs it, with a SKIP line and a
# count. A skipped case is a failure unless CERTIFY_TEST_SKIP_MISSING=1, so a missing or misnamed
# tool cannot pass silently. A tool that is installed must give the verdicts below.
# Every case goes through --elf, also those linked as run.sh links them (bfd, lld's default).
# Two harness-only checks (certify.sh itself does not compare `.text` with the listing, and its
# verdicts do not depend on these): what the ELF reader reads (`.text`, `.rodata`, `.data`'s base)
# equals what readelf reads, for every executable the reader accepts (a difference is a FAIL: a
# misread); and `.text` equals the assembled listing outside the relocated fields
# (`Scc/Test/textcheck.py`; a difference is printed as TEXT DIFFERS and is a FAIL, as is an x86-64
# relocation type textcheck.py does not know, which it reports as DIFFERENT rather than mask).
. Scc/Test/a64link.sh
L=$N/lm; mkdir -p "$L"
LAKE=${LAKE:-lake}
SCC="$ROOT/.lake/build/bin/scc"
textdiff=0
declare -A LMT=([bfd]=ld.bfd [gold]=ld.gold [lld]=ld.lld [clang]="${A64_CC%% *}") LMSKIP=()
lmhas() { # tool (clang: the AArch64 link, `A64_CC`, which also needs ld.lld)
  command -v "${LMT[$1]}" >/dev/null 2>&1 && { [ "$1" != clang ] || lmhas lld; }
}
lmneed() { # tool: true when it is installed; else one more case skipped for it
  lmhas "$1" && return 0
  LMSKIP[$1]=$(( ${LMSKIP[$1]:-0} + 1 )); return 1
}
lmname() { if [ "$1" = clang ]; then echo "${LMT[clang]} or ld.lld (A64_CC)"; else echo "${LMT[$1]}"; fi; }
for t in bfd gold lld clang; do
  if lmhas $t; then echo "info linker matrix: ${LMT[$t]}: $(${LMT[$t]} --version 2>&1 | head -n 1)"
  else echo "SKIP linker matrix: $(lmname $t) not found (its cases are skipped; counts at the end)"; fi
done
tcheck() { # object executable
  local r; r=$(python3 Scc/Test/textcheck.py "$1" "$2"); case "$r" in
    same:*) echo "ok   .text of $2 = its listing's: ${r#same: }" ;;
    *) echo "TEXT DIFFERS: $2: $r"; textdiff=$((textdiff+1)); fails=$((fails+1)) ;;
  esac
}
lmexes=()
lmcase() { # tool arch prog link-name expected-status expected-verdict-prefix
  lmneed "$1" || return 0
  local a=$2 p=$3 n=$4 e="$L/$3.$2.$4"
  tcheck "$L/$p.$a.o" "$e"
  run "$5" "$6" --arch "$a" --instantiate --elf "$ROOT/$e" "Scc/Test/$p.w"
  [ "$5" = 1 ] || lmexes+=("$e")
}
for p in hello1 ret0 ifsub1; do
  "$SCC" --arch x64 -o "$L/$p.x64.s" "Scc/Test/$p.w" && as -o "$L/$p.x64.o" "$L/$p.x64.s" \
    && "$SCC" --arch arm -o "$L/$p.arm.s" "Scc/Test/$p.w" \
    || { echo "FAIL linker matrix: $p: scc or as"; fails=$((fails+1)); continue; }
  for l in bfd gold lld; do
    lmhas $l || continue
    ${LMT[$l]} -static -o "$L/$p.x64.$l" "$L/$p.x64.o" || { echo "FAIL $p: ld.$l"; fails=$((fails+1)); }
  done
  if lmhas clang; then
    $A64_CC -Wno-unused-command-line-argument -c -o "$L/$p.arm.o" "$L/$p.arm.s" \
      && $A64_CC -o "$L/$p.arm.default" "$L/$p.arm.s" \
      && $A64_CC $A64_PIN -o "$L/$p.arm.pin" "$L/$p.arm.s" \
      && $A64_CC -Wl,--image-base=0x100000000 -o "$L/$p.arm.high" "$L/$p.arm.s" \
      || { echo "FAIL $p: arm link"; fails=$((fails+1)); }
  fi
  lmcase bfd x64 $p bfd 0 "certified"
  lmcase gold x64 $p gold 1 "failed: the ELF reader refuses $p: .rodata: its PT_LOAD has flags 5, not 4"
  if [ $p = hello1 ]; then
    lmcase lld x64 $p lld 1 "failed: the ELF reader refuses $p: the layout is not well-formed (wfB): code.lo"
  else lmcase lld x64 $p lld 0 "certified"; fi
  lmcase clang arm $p default 0 "certified"
  lmcase clang arm $p pin 0 "certified"
  lmcase clang arm $p high 3 "not certifiable: placeOKAt fails at the executable's layout (component A1"
done
# The reader against readelf, on every executable above it accepts; and the refusal message's
# conjuncts against `wfB` (`Link.wfBWhy Λ = [] ↔ Link.wfB Λ`): `[]` and true on each accepted
# layout, and on hello1's x64 ld.lld link (refused by `wfB`) a message naming the alignment
# conjunct, not "out of step". One `lake env lean`.
lmwf=(); lmhas lld && lmwf=("$L/hello1.x64.lld")
if [ $(( ${#lmexes[@]} + ${#lmwf[@]} )) -gt 0 ]; then
  { echo "import Scc.Cert.Elf"; echo "open Scc.Cert"; echo "#eval show IO Unit from do"
    for e in ${lmexes[@]+"${lmexes[@]}"} ${lmwf[@]+"${lmwf[@]}"}; do
      echo "  match Elf.elfParts (← IO.FS.readBinFile \"$e\") with"
      echo "  | .error r => IO.println s!\"$e: refused: {r}\""
      printf '  | .ok l => do\n    IO.println s!"%s: code {l.code.lo} {l.code.size} ' "$e"
      echo 'rodata {l.rodata.lo} {l.rodata.size} data {l.data.lo}"'
      printf '    IO.println s!"%s: wf {Link.wfB l.toLayout} {Link.wfBWhy l.toLayout}"\n' "$e"
    done; } >"$L/read.lean"
  "$LAKE" env lean "$L/read.lean" >"$L/read.out" 2>&1
  for e in ${lmexes[@]+"${lmexes[@]}"}; do
    got=$(sed -n "s|^$e: code |code |p" "$L/read.out"); want=$(python3 Scc/Test/textcheck.py --layout "$e")
    if [ "$got" = "$want" ]; then echo "ok   reader = readelf on $e: $got"
    else echo "FAIL reader on $e: '$got', readelf: '$want'"; fails=$((fails+1)); fi
    wf=$(sed -n "s|^$e: wf ||p" "$L/read.out")
    if [ "$wf" = "true []" ]; then echo "ok   wfB and wfBWhy agree on $e: $wf"
    else echo "FAIL wfB/wfBWhy on $e: '$wf', want 'true []'"; fails=$((fails+1)); fi
  done
  for e in ${lmwf[@]+"${lmwf[@]}"}; do
    r=$(sed -n "s|^$e: refused: ||p" "$L/read.out")
    if printf '%s\n' "$r" | grep -Eq '^the layout is not well-formed \(wfB\): (.*, )?code\.lo [0-9]+ is not 16-aligned'
    then echo "ok   wfBWhy names the conjunct on $e: $r"
    else echo "FAIL wfBWhy on $e: '$r', want the code.lo alignment conjunct"; fails=$((fails+1)); fi
  done
fi

# Refusals: wake and hello linked by a linker or at a layout other than their registry entry's
# (exit 3: no proved theorem at that layout, or the reader's refusal), and a dynamic executable or
# PIE (the reader refuses: no PT_INTERP, ET_EXEC only). arm PIE: ld.lld does not link the listing
# as PIE (absolute relocations in `.rodata`), so there is no such executable to refuse. Each case
# needs one tool and is skipped alone when it is not installed.
as -o "$L/wake.x64.o" Scc/Test/elf/wakex64/wake.s \
  || { echo "FAIL refusal cases: as wake"; fails=$((fails+1)); }
lmlink() { "$@" || { echo "FAIL refusal cases: $*"; fails=$((fails+1)); }; }
if lmneed gold; then
  lmlink ld.gold -static -o "$L/wake.x64.gold" "$L/wake.x64.o"
  run 1 "failed: the ELF reader refuses wake: .rodata: its PT_LOAD has flags 5, not 4" \
    --arch x64 --instantiate --elf "$ROOT/$L/wake.x64.gold" Scc/Test/wake.w
fi
if lmneed lld; then
  lmlink ld.lld -static -o "$L/wake.x64.lld" "$L/wake.x64.o"
  # ld.lld's default layout puts .text in the segment after .rodata's, at the file offset
  # that follows .rodata; the listing's .text has alignment 1, so code.lo is 16-aligned only
  # when .rodata's end is (ret0 and ifsub1 above: yes; wake and hello1: no, and the reader
  # refuses by wfB).
  run 1 "failed: the ELF reader refuses wake: the layout is not well-formed (wfB): code.lo" \
    --arch x64 --instantiate --elf "$ROOT/$L/wake.x64.lld" Scc/Test/wake.w
fi
# wake on x86-64 at a layout other than its theorem's (GNU ld, moved): exit 3.
lmlink ld -static -Ttext-segment=0x800000 -o "$L/wake.x64.moved" "$L/wake.x64.o"
run 3 "not certifiable: no proved theorem at this executable's layout (wake's theorem" \
  --arch x64 --instantiate --elf "$ROOT/$L/wake.x64.moved" Scc/Test/wake.w
if lmneed clang; then
  lmlink $A64_CC -Wl,--image-base=0x800000 -o "$L/wake.arm.moved" Scc/Test/elf/wakea64/wake.s
  run 3 "not certifiable: no proved theorem at this executable's layout (wake's theorem" \
    --arch arm --instantiate --elf "$ROOT/$L/wake.arm.moved" Scc/Test/wake.w
fi
if lmneed clang; then
  lmlink $A64_CC -o "$L/hello.arm.default" Scc/Test/elf/helloa64/hello.s
  run 3 "not certifiable: no proved theorem at this executable's layout (hello's theorem" \
    --arch arm --instantiate --elf "$ROOT/$L/hello.arm.default" Scc/Test/hello.w
fi
if lmneed bfd; then
  lmlink ld.bfd -pie --no-dynamic-linker -o "$L/ret0.x64.pie" "$L/ret0.x64.o" 2>/dev/null
  run 1 "failed: the ELF reader refuses ret0: not an executable (ET_EXEC)" \
    --arch x64 --instantiate --elf "$ROOT/$L/ret0.x64.pie" Scc/Test/ret0.w
fi
if lmneed lld; then
  lmlink ld.lld -dynamic-linker /lib64/ld-linux-x86-64.so.2 --export-dynamic \
    -o "$L/ret0.x64.dyn" "$L/ret0.x64.o"
  run 1 "failed: the ELF reader refuses ret0: unexpected program header type 3" \
    --arch x64 --instantiate --elf "$ROOT/$L/ret0.x64.dyn" Scc/Test/ret0.w
fi
if lmneed clang; then
  lmlink $A64_CC -Wl,-dynamic-linker,/lib/ld-linux-aarch64.so.1,--export-dynamic -o "$L/ret0.arm.dyn" \
    "$L/ret0.arm.s"
  run 1 "failed: the ELF reader refuses ret0: unexpected program header type 3" \
    --arch arm --instantiate --elf "$ROOT/$L/ret0.arm.dyn" Scc/Test/ret0.w
fi
[ "$textdiff" = 0 ] && echo "ok   linker matrix: no linker changed .text outside relocated fields" \
  || echo "FAIL linker matrix: TEXT DIFFERS in $textdiff executables (each counted as a failure above)"
lmskips=0
for t in bfd gold lld clang; do
  [ -n "${LMSKIP[$t]:-}" ] || continue
  echo "SKIP linker matrix: $(lmname $t) not found (${LMSKIP[$t]} cases)"; lmskips=$((lmskips + LMSKIP[$t]))
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

sk=""
if [ "$lmskips" != 0 ]; then
  if [ "${CERTIFY_TEST_SKIP_MISSING:-0}" = 1 ]; then
    sk=" ($lmskips linker matrix cases skipped: a tool not found; CERTIFY_TEST_SKIP_MISSING=1)"
  else
    echo "FAIL linker matrix: $lmskips cases skipped, each counted as a failure (a tool not found; set CERTIFY_TEST_SKIP_MISSING=1 to allow)"
    fails=$((fails+lmskips)); sk=" ($lmskips linker matrix cases skipped: a tool not found)"
  fi
fi
[ "$fails" = 0 ] && echo "certify_test: all passed$sk" || { echo "certify_test: $fails failed$sk"; exit 1; }
