#!/usr/bin/env bash
# Build scc, compile every Scc/Test/*.w, assemble, link and run the binaries,
# and compare standard output, standard error and exit status with the
# expected files.
#
# Usage: Scc/Test/run.sh [--arch x64|arm] [--arm-run qemu|native|auto]
#
# Per test T.w (all files optional):
#   T.code    expected exit status of the binary (default 0)
#   T.out     expected standard output (default empty)
#   T.stderr  expected standard error of the binary (default: not compared)
#   T.report  expected output of `scc --report` (default: not compared)
#   T.runs    how many times to run the binary (default 1; multi-threaded
#             tests run many times to catch nondeterministic failures)
# A test named reject_*.w must be rejected by scc with exit status 1 and
# standard error equal to reject_*.err.
#
# Every accepted test also gets a certificate (`scc --cert`), which must check
# (`scc --check`; its time and peak RssAnon, `Scc/Test/rssanon.sh`, are printed) and record the SHA-256
# of the source and assembler text; a tampered certificate (one instruction of
# the embedded text changed so that it is no longer lowerable) must not check.
# A program outside the certified fragment (no stack need table: non-tail
# recursion) gets a file with its source and the reason only
# (`Scc.Cert.Gen.renderOutside`), counted as not certifiable, not as a failure.
# So is a program whose certificate does not check because `placeOK` fails:
# the placement diagnostic (`Scc/Test/placediag.sh`, untrusted) names the
# first failing component AN, and the certificate of that failure
# (`scc --cert-fails N`, `T.fails.cert.lean`) must check.
#
# Environment: LAKE (default `lake`) is the lake command used to build scc.
# x64 binaries are assembled with GNU `as` and linked with `ld -static`; arm
# binaries are built with clang and lld and run under `qemu-aarch64`, or
# natively on a qualifying aarch64 host (--arm-run; see Scc/Test/armrun.sh).
set -u

ARCH=x64
while [ $# -gt 0 ]; do
  case "$1" in
    --arch) ARCH="$2"; shift 2 ;;
    --arm-run) ARM_RUN="$2"; shift 2 ;;
    *) echo "usage: $0 [--arch x64|arm] [--arm-run qemu|native|auto]" >&2; exit 2 ;;
  esac
done
case "$ARCH" in x64|arm) ;; *) echo "unknown arch $ARCH" >&2; exit 2 ;; esac
. "$(dirname "$0")/armrun.sh"
[ "$ARCH" = arm ] && arm_run_resolve

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
TESTS="$ROOT/Scc/Test"
LAKE=${LAKE:-lake}
WORK="$ROOT/.lake/scc-test/$ARCH"
SCC="$ROOT/.lake/build/bin/scc"

(cd "$ROOT" && $LAKE build scc scc_x64 scc_arm) >/dev/null || { echo "FAIL: lake build scc"; exit 1; }
rm -rf "$WORK"; mkdir -p "$WORK"; cd "$WORK" || exit 1

pass=0; fail=0; certified=0; uncertifiable=0
ok() { pass=$((pass + 1)); echo "ok   $1"; }
bad() { fail=$((fail + 1)); echo "FAIL $1: $2"; }

# Assemble and link $1.s into $1.
link() {
  if [ "$ARCH" = x64 ]; then
    as -o "$1.o" "$1.s" && ld -static -o "$1" "$1.o"
  else
    clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld -o "$1" "$1.s"
  fi
}

# Run binary $1 (with a timeout), stdout to $2, stderr to $3; prints the status.
runbin() {
  if [ "$ARCH" = x64 ]; then
    timeout 20 "./$1" >"$2" 2>"$3"
  else
    arm_exec "./$1" >"$2" 2>"$3"
  fi
  echo $?
}

for src in "$TESTS"/*.w; do
  t=$(basename "$src" .w)
  cp "$src" .
  if [[ "$t" == reject_* ]]; then
    "$SCC" --arch "$ARCH" "$t.w" >/dev/null 2>"$t.err.actual"; rc=$?
    if [ $rc -ne 1 ]; then bad "$t" "scc exit $rc, expected 1"; continue; fi
    if ! cmp -s "$t.err.actual" "$TESTS/$t.err"; then
      bad "$t" "diagnostic differs: $(cat "$t.err.actual")"; continue
    fi
    ok "$t"; continue
  fi
  "$SCC" --arch "$ARCH" --report --cert "$t.cert.lean" -o "$t.s" "$t.w" >"$t.report.actual" 2>"$t.scc.err" \
    || { bad "$t" "scc failed: $(cat "$t.scc.err")"; continue; }
  if [ -f "$TESTS/$t.report" ] && ! cmp -s "$t.report.actual" "$TESTS/$t.report"; then
    bad "$t" "report differs: $(cat "$t.report.actual")"; continue
  fi
  link "$t" 2>"$t.link.err" || { bad "$t" "assemble/link failed: $(cat "$t.link.err")"; continue; }
  code=0; [ -f "$TESTS/$t.code" ] && code=$(cat "$TESTS/$t.code")
  runs=1; [ -f "$TESTS/$t.runs" ] && runs=$(cat "$TESTS/$t.runs")
  if [ -f "$TESTS/$t.out" ]; then cp "$TESTS/$t.out" "$t.out.expected"; else : >"$t.out.expected"; fi
  failed=""
  for i in $(seq 1 "$runs"); do
    rc=$(runbin "$t" "$t.out.actual" "$t.stderr.actual")
    if [ "$rc" != "$code" ]; then failed="run $i: exit $rc, expected $code"; break; fi
    if ! cmp -s "$t.out.actual" "$t.out.expected"; then failed="run $i: stdout differs"; break; fi
    if [ -f "$TESTS/$t.stderr" ] && ! cmp -s "$t.stderr.actual" "$TESTS/$t.stderr"; then
      failed="run $i: stderr differs"; break
    fi
  done
  if [ -n "$failed" ]; then bad "$t" "$failed"; else ok "$t (x$runs)"; fi
done

# Certificates: each checks, with the digests of the embedded texts. A file
# for a program outside the certified fragment (its marker line,
# `Scc.Cert.Gen.outsideMark`) embeds the source only, and must check too.
OUTSIDE="-- outside the certified fragment: no stack need table (non-tail recursion)"
# The check's time and peak memory: the peak RssAnon of its `lean` child
# (`rssanon.sh`, the budget's measure, untrusted), else GNU time's max RSS.
TIMER=""; [ -x /usr/bin/time ] && TIMER="/usr/bin/time -f %e:%M -o cert.time"
RSS="$ROOT/Scc/Test/rssanon.sh cert.rss"
for cert in *.cert.lean; do
  t=${cert%.cert.lean}
  hs=$(sha256sum "$t.w" | cut -d' ' -f1); ha=$(sha256sum "$t.s" | cut -d' ' -f1)
  if grep -qxF -- "$OUTSIDE" "$cert"; then
    if [ "$(grep -c "^-- SHA-256 (UTF-8): $hs\$" "$cert")" != 1 ]; then
      bad "cert $t" "source digest differs from sha256sum"; continue
    fi
    if LAKE="$LAKE" "$SCC" --arch "$ARCH" --check "$cert" >"$t.check.out" 2>&1; then
      uncertifiable=$((uncertifiable + 1)); echo "--   cert $t: not certifiable (no stack need table)"
    else bad "cert $t" "does not check: $(head -c 2000 "$t.check.out")"; fi
    continue
  fi
  if [ "$(grep -c "^-- SHA-256 (UTF-8): \($hs\|$ha\)\$" "$cert")" != 2 ]; then
    bad "cert $t" "digests differ from sha256sum"; continue
  fi
  rm -f cert.rss cert.time
  if LAKE="$LAKE" $RSS $TIMER "$SCC" --arch "$ARCH" --check "$cert" >"$t.check.out" 2>&1; then
    secs=""; ra=""; kb=""
    [ -f cert.rss ] && IFS=: read -r secs ra <cert.rss
    [ -f cert.time ] && IFS=: read -r _ kb <cert.time
    if [ -n "$ra" ]; then ok "cert $t (${secs} s, $((ra / 1024)) MB RssAnon peak)"
    elif [ -n "$kb" ]; then ok "cert $t (${secs} s, $((kb / 1024)) MB)"
    else ok "cert $t"; fi
    certified=$((certified + 1))
    continue
  fi
  # It does not check: is it `placeOK` that fails, and at which component?
  an=$(LAKE="$LAKE" "$ROOT/Scc/Test/placediag.sh" --arch "$ARCH" "$cert" 2>"$t.diag.err")
  case "$an" in
    a[0-9]*)
      if "$SCC" --arch "$ARCH" --cert "$t.fails.cert.lean" --cert-fails "${an#a}" -o "$t.fails.s" "$t.w" \
            >/dev/null 2>"$t.fails.err" \
          && LAKE="$LAKE" "$SCC" --arch "$ARCH" --check "$t.fails.cert.lean" >"$t.fails.check.out" 2>&1; then
        uncertifiable=$((uncertifiable + 1)); echo "--   cert $t: not certifiable (fails PlaceOK: $an)"
      else bad "cert $t" "placeOK fails at $an, but its certificate does not check: \
$(head -c 2000 "$t.fails.check.out" 2>/dev/null)$(cat "$t.fails.err")"; fi ;;
    *) bad "cert $t" "does not check (placeOK: ${an:-?}): $(head -c 2000 "$t.check.out")" ;;
  esac
done

# A tampered certificate does not check: one instruction of the embedded
# assembler text made unlowerable (x64: `lock xaddq` -> `xaddq`, an unlocked
# RMW; arm: `ldaddal x9, x11` -> `ldaddal x9, xzr`, a no-return atomic). Both
# the reproducibility check and the lowerability proof must fail.
if [ "$ARCH" = x64 ]; then
  sed '0,/\\tlock xaddq/s//\\txaddq/' hello.cert.lean >tampered.cert.lean
else
  sed '0,/\\tldaddal x9, x11,/s//\\tldaddal x9, xzr,/' hello.cert.lean >tampered.cert.lean
fi
if cmp -s hello.cert.lean tampered.cert.lean; then bad "tampered cert" "nothing was changed"
else
  LAKE="$LAKE" "$SCC" --arch "$ARCH" --check tampered.cert.lean >tampered.out 2>&1; rc=$?
  # The lowerability failure is reported either by `decide`'s diagnosis or,
  # when the diagnosis gives up on a large program, as the kernel's mismatch.
  if [ $rc -eq 1 ] && grep -q "reproduces config source asm" tampered.out \
      && { grep -q "Tactic \`decide\` proved that the proposition" tampered.out \
           || grep -q "WCLowerable.* = true →" tampered.out; }; then
    ok "tampered cert does not check (exit 1: reproducibility and lowerability fail)"
  else bad "tampered cert" "exit $rc: $(head -c 2000 tampered.out)"; fi
fi

# The IR-level stack relocation test (Scc/Test/StackTest.lean): stack
# addresses held across calls and prologue checks while the stack grows.
if [ "$ARCH" = x64 ]; then RELOC=X64; else RELOC=Arm; fi
printf 'import Scc.Test.Stack%s\ndef main (args : List String) : IO UInt32 :=\n  Scc.Test.Stack.%s.writeReloc args\n' \
  "$RELOC" "$RELOC" >reloc_driver.lean
if (cd "$ROOT" && $LAKE build "Scc.Test.Stack$RELOC") >/dev/null \
    && (cd "$ROOT" && $LAKE env lean --run "$WORK/reloc_driver.lean" "$WORK") >reloc.gen.err 2>&1; then
  cp "reloc_$ARCH.s" reloc.s
  if link reloc 2>reloc.link.err; then
    rc=$(runbin reloc reloc.out.actual reloc.stderr.actual)
    if [ "$rc" = 0 ] && [ "$(cat reloc.out.actual)" = "reloc ok" ]; then ok "reloc (IR-level stack addresses)"
    else bad "reloc" "exit $rc, stdout $(cat reloc.out.actual)"; fi
  else bad "reloc" "assemble/link failed: $(cat reloc.link.err)"; fi
else bad "reloc" "could not build or write the program: $(cat reloc.gen.err)"; fi

# Index arithmetic keeps its overflow check (printidx's `printL` has `iv + 1`).
if [ "$ARCH" = x64 ]; then
  if [[ "$(cat printidx.s)" == *"jb .Lwc_printL.ovf"* ]]; then ok "printidx: index + keeps its check"
  else bad "printidx" "no overflow check on printL's +"; fi
else
  if [[ "$(cat printidx.s)" =~ b\.hs\ \.L[0-9]+_wc_printL\.abort_overflow ]]; then
    ok "printidx: index + keeps its check"
  else bad "printidx" "no overflow check on printL's +"; fi
fi

# The listing on standard output, piped into the assembler.
if [ "$ARCH" = x64 ]; then
  if "$SCC" -S hello.w 2>/dev/null | as -o pipe.o - && ld -static -o pipe pipe.o \
      && [ "$(./pipe)" = "Hello, world" ]; then ok "scc -S hello.w | as"; else bad "scc -S" "pipe failed"; fi
else
  if "$SCC" --arch arm -S hello.w 2>/dev/null >pipe.s && link pipe \
      && [ "$(arm_exec ./pipe)" = "Hello, world" ]; then ok "scc -S hello.w"; else bad "scc -S" "failed"; fi
fi

# Command-line errors: exit status 2 and the message.
cli() {  # name, expected message, args...
  local name="$1" msg="$2"; shift 2
  "$SCC" "$@" >/dev/null 2>cli.err; rc=$?
  if [ $rc -eq 2 ] && [ "$(head -n 1 cli.err)" = "$msg" ]; then ok "$name"
  else bad "$name" "exit $rc: $(cat cli.err)"; fi
}
cli "--host raw" "scc: --host raw: not implemented" --host raw hello.w
cli "--gc unknown" "scc: --gc copying: unknown collector (available: none)" --gc copying hello.w
cli "--arch unknown" "scc: --arch sparc: unknown architecture (available: x64, arm)" --arch sparc hello.w
cli "no input" "scc: no input file"

# Every check is counted once: passed, failed, or (a certificate) not
# certifiable, which is neither; the total does not move when a program's
# certificate changes between certified and not certifiable.
echo "$((pass + fail + uncertifiable)) checks: $pass passed, $fail failed, $uncertifiable not certifiable;" \
  "certificates: $certified certified, $uncertifiable not certifiable"
[ $fail -eq 0 ]
