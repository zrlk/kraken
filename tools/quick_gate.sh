#!/usr/bin/env bash
# The quick release gate: an incremental build under per-module memory caps,
# then the cheap check groups in parallel, on the checkout this script is in.
#
# Usage: tools/quick_gate.sh            (from anywhere; runs in the repository root)
#   SETUP_ONLY=1 tools/quick_gate.sh    print the plan (groups, commands, caps) and exit
#
# Phases:
#   0 solo   every `solo`/`cert` module of tools/memory_caps.tsv that is not up to
#            date is built alone (its imports first, in parallel), when
#            MemAvailable >= MINAVAIL_GB; SOLO=0 skips this phase
#   1 build  lake build $BUILD_TARGETS (incremental), LEAN_NUM_THREADS=1
#   2 checks the groups below, at most PAR at once, each started only when
#            MemAvailable >= MINAVAIL_GB, longest first:
#     place_arm, place_x64  [diff.sh, DIFF=1 only] then tools/diff_place.sh for
#                           that ISA, under `timeout $DPLACE_TIMEOUT` (default 7200 s)
#                           each; one group per ISA because diff.sh and diff_place.sh
#                           share .lake/scc-diff/<ISA>/ (the two ISAs run in parallel)
#     run_arm, run_x64      Scc/Test/run.sh per ISA (.lake/scc-test/<ISA>/)
#     static                sorry/native_decide file set equal to $BASE's (skipped
#                           without BASE); tools/trusted_check.sh HEAD against
#                           tools/trusted_paths.md5; regen --check of every generated
#                           instance; Spike/Gen/drift.sh
#     quick                 blocks.sh --check, textalign.sh, elf.sh, elf.sh
#                           --relink-check (every fixture `same`), elf.sh --raw-check
#     asm                   the assembler tests of both ISAs
#     hooks                 AUDIT_CMD, SEG_CMD, FREEZE_CMD, GUARD_CMD: optional
#                           external checks (shell commands run in the repository
#                           root); a group each, skipped when unset
#   Not here (release gate only): cold timed builds, certify.sh / certify_test.sh.
#
# Memory: tools/memwatch.py watches every lean of this checkout with the caps of
# tools/memory_caps.tsv; killing (above the cap) in phases 0-1, record only in 2.
# A module killed in phase 1 gets one solo re-run at the next tier
# (4096 -> 5120 -> 6144 -> 8192), then phase 1 runs once more; a second kill is a
# failure, and its row in tools/memory_caps.tsv must be re-measured.
#
# Environment:
#   LAKE (default `lake`), PAR (4), MINAVAIL_GB (20), BASE (unset), DIFF (0),
#   DPLACE_TIMEOUT (7200), DIFF_TIMEOUT (3600), SOLO (1), BUILD_TARGETS,
#   QG_GROUPS (default: all, in the order above; a subset for a partial run),
#   LOGDIR (.lake/quick-gate), A64_TOOLS (a directory prepended to PATH for the
#   AArch64 assembler tests, optional), AUDIT_CMD/SEG_CMD/FREEZE_CMD/GUARD_CMD,
#   CERT_BUILD (optional: a command that builds one certificate module, given as
#   its argument, with CERT_CAP_MB from tools/memory_caps.tsv in the environment;
#   used for the `cert` rows in phase 0 instead of a plain lake build).
# Output: $LOGDIR/g_<group>.out per group, $LOGDIR/memwatch*.tsv, a summary
# with one `RESULT <group> PASS|FAIL|SKIP` line per group. Exit status 0 when
# no group fails, 1 otherwise, 3 when a module is killed twice.
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT" || exit 2
export LAKE=${LAKE:-lake}
export LEAN_NUM_THREADS=1
# A lake wrapper that caps `lake env` processes may read KRAKEN_ENV_MAX; the
# blocks.sh AArch64 `.code` checks need more than 4 GiB.
export KRAKEN_ENV_MAX=${KRAKEN_ENV_MAX:-6G}
PAR=${PAR:-4}
MINAVAIL_GB=${MINAVAIL_GB:-20}
BASE=${BASE:-}
DIFF=${DIFF:-0}
DPLACE_TIMEOUT=${DPLACE_TIMEOUT:-7200}
DIFF_TIMEOUT=${DIFF_TIMEOUT:-3600}
SOLO=${SOLO:-1}
BUILD_TARGETS=${BUILD_TARGETS:-"Kraken KrakenAArch64 WeakCore Scc Spike scc scc_x64 scc_arm"}
LOGDIR=${LOGDIR:-$ROOT/.lake/quick-gate}
CAPS=$ROOT/tools/memory_caps.tsv
TIERS="4096 5120 6144 8192"
GROUPS_ALL=${QG_GROUPS:-"place_arm place_x64 run_arm run_x64 static quick asm audit seg freeze guard"}

avail_gb() { awk '/^MemAvailable:/{print int($2/1048576)}' /proc/meminfo; }
wait_avail() { while [ "$(avail_gb)" -lt "$MINAVAIL_GB" ]; do sleep 15; done; }
imports_of() { awk '/^(public |meta |private )*import /{print $NF} /^(namespace|open|section|def|theorem|set_option)/{exit}' "$(echo "$1" | tr . /).lean"; }
solo_mods() { awk -F'\t' '!/^#/ && ($4 == "solo" || $4 == "cert") {print $3, $1}' "$CAPS" | sort -n | awk '{print $2}'; }
cap_of() { awk -F'\t' -v m="$1" '$1 == m {c = $3} $1 == "*" {d = $3} END {print (c ? c : d)}' "$CAPS"; }
next_tier() { local t; for t in $TIERS; do [ "$t" -gt "$1" ] && { echo "$t"; return; }; done; echo "$1"; }
killed_count() { awk '/ - killed$/' "$LOGDIR/memwatch_build.tsv.events" 2>/dev/null | wc -l; }
killed_since() { awk -v k="$1" '/ - killed$/ {c++; if (c > k) print $3}' "$LOGDIR/memwatch_build.tsv.events" 2>/dev/null | sort -u; }

# ---- check groups: each prints its log lines and ends with RESULT <group> ... ----
g_place() {  # g_place <isa>
  local a=$1 st=0
  if [ "$DIFF" = 1 ]; then
    timeout --kill-after=60 "$DIFF_TIMEOUT" bash Scc/Test/diff.sh --arch "$a" -n 300 --seed 70 --place 10 > "$LOGDIR/diff_$a.log" 2>&1
    local rc=$?; echo "diff.sh $a rc=$rc $(tail -3 "$LOGDIR/diff_$a.log" | tr '\n' ' ')"; [ $rc = 0 ] || st=1
  fi
  timeout --kill-after=60 "$DPLACE_TIMEOUT" bash tools/diff_place.sh "$a" > "$LOGDIR/dplace_$a.log" 2>&1
  local rc=$?; echo "diff_place $a rc=$rc$([ $rc = 124 ] && echo " (timeout ${DPLACE_TIMEOUT} s)")"
  awk '/^(OK|FAIL):/' "$LOGDIR/dplace_$a.log"; [ $rc = 0 ] || st=1
  [ $st = 0 ] && echo "RESULT place_$a PASS" || echo "RESULT place_$a FAIL"
}
g_place_arm() { g_place arm; }
g_place_x64() { g_place x64; }
g_run() {  # g_run <isa>
  bash Scc/Test/run.sh --arch "$1" > "$LOGDIR/run_$1.log" 2>&1; local rc=$?
  echo "run.sh $1 rc=$rc $(tail -1 "$LOGDIR/run_$1.log")"
  [ $rc = 0 ] && echo "RESULT run_$1 PASS" || echo "RESULT run_$1 FAIL"
}
g_run_arm() { g_run arm; }
g_run_x64() { g_run x64; }
sorry_set() {  # files with a sorry/native_decide outside a line comment, at revision $1
  python3 - "$1" <<'EOF'
import re, subprocess, sys
rev = sys.argv[1]
pat = re.compile(r"^[^-\n]*\b(sorry|native_decide)\b", re.M)
ls = subprocess.run(["git", "ls-tree", "-r", rev], capture_output=True, text=True, check=True).stdout
blobs = [(l.split("\t", 1)[1], l.split()[2]) for l in ls.splitlines() if l.endswith(".lean")]
cat = subprocess.Popen(["git", "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
hits = []
for path, sha in blobs:
    cat.stdin.write((sha + "\n").encode()); cat.stdin.flush()
    size = int(cat.stdout.readline().split()[2])
    if pat.search(cat.stdout.read(size + 1)[:size].decode("utf-8", errors="replace")):
        hits.append(path)
print("\n".join(sorted(hits)))
EOF
}
g_static() {
  local st=0 rc
  echo "== sorry/native_decide file set"
  sorry_set HEAD > "$LOGDIR/sorry_head.txt"
  if [ -n "$BASE" ]; then
    sorry_set "$BASE" > "$LOGDIR/sorry_base.txt"
    if cmp -s "$LOGDIR/sorry_head.txt" "$LOGDIR/sorry_base.txt"; then echo "SORRY_SET_SAME ($(wc -l < "$LOGDIR/sorry_head.txt") files)"
    else echo "SORRY_SET_DIFF"; diff "$LOGDIR/sorry_base.txt" "$LOGDIR/sorry_head.txt" | head -20; st=1; fi
  else echo "SORRY_SET_SKIP (BASE unset; $(wc -l < "$LOGDIR/sorry_head.txt") files at HEAD)"; fi
  echo "== trusted files (tools/trusted_paths.md5)"
  bash tools/trusted_check.sh HEAD > "$LOGDIR/trusted.log" 2>&1; rc=$?
  awk '/^(ADDED|REMOVED|CHANGED) /' "$LOGDIR/trusted.log" | head -60; awk '/^trusted_check:/' "$LOGDIR/trusted.log"
  [ $rc = 0 ] && echo TRUSTED_SAME || { echo "TRUSTED_DIFF (rc=$rc; review, then regenerate with --write)"; st=1; }
  echo "== generated files (regen --check)"
  local spec isa name mod
  for spec in a64:ret0:A64Ret0 x64:ret0:X64Ret0 x64:hello1:X64Hello1 a64:hello1:A64Hello1 \
              a64:wake:A64Wake x64:wake:X64Wake a64:hello:A64Hello x64:hello:X64Hello; do
    IFS=: read -r isa name mod <<< "$spec"
    [ -f "Spike/Gen/$name.w" ] || { echo "regen $isa $name: no Spike/Gen/$name.w"; st=1; continue; }
    bash "Spike/Gen/regen_$isa.sh" "$name" "$mod" --check > "$LOGDIR/regen_${isa}_$name.log" 2>&1; rc=$?
    echo "regen $isa $name rc=$rc $(tail -1 "$LOGDIR/regen_${isa}_$name.log")"; [ $rc = 0 ] || st=1
  done
  echo "== drift"
  bash Spike/Gen/drift.sh > "$LOGDIR/drift.log" 2>&1; rc=$?
  echo "drift rc=$rc $(tail -1 "$LOGDIR/drift.log")"; [ $rc = 0 ] || st=1
  [ $st = 0 ] && echo "RESULT static PASS" || echo "RESULT static FAIL"
}
g_quick() {
  local st=0 rc
  bash Scc/Test/blocks.sh --check > "$LOGDIR/blocks.log" 2>&1; rc=$?
  echo "blocks rc=$rc $(tail -1 "$LOGDIR/blocks.log")"; [ $rc = 0 ] || st=1
  bash Scc/Test/textalign.sh > "$LOGDIR/textalign.log" 2>&1; rc=$?
  echo "textalign rc=$rc $(tail -1 "$LOGDIR/textalign.log")"; [ $rc = 0 ] || st=1
  bash Scc/Test/elf.sh > "$LOGDIR/elf.log" 2>&1; rc=$?
  echo "elf rc=$rc $(tail -1 "$LOGDIR/elf.log")"; [ $rc = 0 ] || st=1
  bash Scc/Test/elf.sh --relink-check > "$LOGDIR/relink.log" 2>&1; rc=$?
  echo "relink rc=$rc $(tail -1 "$LOGDIR/relink.log"); same=$(awk '$1 == "same"' "$LOGDIR/relink.log" | wc -l) other: $(awk '$1 == "differs" || $1 == "skip" {printf "%s %s; ", $1, $2}' "$LOGDIR/relink.log")"
  { [ $rc = 0 ] && ! awk '$1 == "skip" {f = 1} END {exit !f}' "$LOGDIR/relink.log"; } || st=1
  bash Scc/Test/elf.sh --raw-check > "$LOGDIR/rawcheck.log" 2>&1; rc=$?
  echo "rawcheck rc=$rc $(tail -1 "$LOGDIR/rawcheck.log")"; [ $rc = 0 ] || st=1
  [ $st = 0 ] && echo "RESULT quick PASS" || echo "RESULT quick FAIL"
}
g_asm() {
  local st=0 out
  out=$(PATH=${A64_TOOLS:+$A64_TOOLS:}$PATH python3 Kraken/AArch64/Test/asm_tests.py Kraken/AArch64/Test/asm 2>&1 | awk '/^Result:/')
  echo "asm AArch64: ${out:-no Result line}"; echo "$out" | awk '{split($2, a, "/"); exit !(NF && a[1] == a[2])}' || st=1
  out=$(python3 Kraken/X64/Test/asm_tests.py Kraken/X64/Test/asm 2>&1 | awk '/^Result:/')
  echo "asm x86-64: ${out:-no Result line}"; echo "$out" | awk '{split($2, a, "/"); exit !(NF && a[1] == a[2])}' || st=1
  [ $st = 0 ] && echo "RESULT asm PASS" || echo "RESULT asm FAIL"
}
g_hook() {  # g_hook <group> <command>
  [ -n "$2" ] || { echo "RESULT $1 SKIP (no command)"; return; }
  bash -c "$2" > "$LOGDIR/hook_$1.log" 2>&1; local rc=$?
  tail -15 "$LOGDIR/hook_$1.log"
  [ $rc = 0 ] && echo "RESULT $1 PASS" || echo "RESULT $1 FAIL (rc=$rc)"
}
g_audit() { g_hook audit "${AUDIT_CMD:-}"; }
g_seg() { g_hook seg "${SEG_CMD:-}"; }
g_freeze() { g_hook freeze "${FREEZE_CMD:-}"; }
g_guard() { g_hook guard "${GUARD_CMD:-}"; }

if [ "${SETUP_ONLY:-0}" = 1 ]; then
  echo "root $ROOT; LAKE=$LAKE PAR=$PAR MINAVAIL_GB=$MINAVAIL_GB BASE=${BASE:-unset} DIFF=$DIFF DPLACE_TIMEOUT=$DPLACE_TIMEOUT SOLO=$SOLO"
  echo "build targets: $BUILD_TARGETS"
  echo "solo/cert modules (cap order):"; for m in $(solo_mods); do echo "  $m cap $(cap_of "$m")"; done
  echo "default cap: $(cap_of '*')"
  echo "groups: $GROUPS_ALL"
  for h in AUDIT_CMD SEG_CMD FREEZE_CMD GUARD_CMD; do echo "  $h=${!h:-unset}"; done
  for g in $GROUPS_ALL; do declare -F "g_$g" > /dev/null || { echo "missing g_$g"; exit 2; }; done
  exit 0
fi

mkdir -p "$LOGDIR" && rm -f "$LOGDIR"/*.out "$LOGDIR"/*.log "$LOGDIR"/memwatch*
T0=$(date +%s)
date -u +"quick_gate start %F %T UTC"
echo "HEAD $(git rev-parse --short=12 HEAD) dirty=$(git status --porcelain | wc -l) base ${BASE:-unset}"
OVR=$LOGDIR/cap_override
: > "$OVR"
python3 tools/memwatch.py "$LOGDIR/memwatch_build.tsv" "$ROOT" --kill --override "$OVR" & WPID=$!
trap 'kill $WPID 2>/dev/null' EXIT

build_solo() {  # build_solo <module> <log>: imports first (parallel), then the module alone
  local m=$1
  "$LAKE" build $(imports_of "$m") > "$LOGDIR/$2.pre.log" 2>&1 || { echo "  $m: imports failed (see $2.pre.log)"; return 1; }
  wait_avail
  case "$m" in
    Spike.Test.Cert.*) [ -n "${CERT_BUILD:-}" ] && { CERT_CAP_MB=$(cap_of "$m") bash -c "$CERT_BUILD $m" > "$LOGDIR/$2.log" 2>&1; return; } ;;
  esac
  "$LAKE" build "$m" > "$LOGDIR/$2.log" 2>&1
}
STOP=0
if [ "$SOLO" = 1 ]; then
  echo "== 0 solo modules"
  for m in $(solo_mods); do
    "$LAKE" build --no-build "$m" > /dev/null 2>&1 && continue
    t=$(date +%s); k0=$(killed_count)
    build_solo "$m" "solo_${m##*.}"; rc=$?
    echo "  $m rc=$rc cap $(cap_of "$m") wall $(( $(date +%s) - t )) s"
    [ -n "$(killed_since "$k0")" ] && { echo "STOP: $m killed at its cap in the solo phase"; STOP=1; }
  done
fi
[ $STOP = 1 ] && exit 3
echo "== 1 build: lake build $BUILD_TARGETS"
t=$(date +%s); k0=$(killed_count)
"$LAKE" build $BUILD_TARGETS > "$LOGDIR/build.log" 2>&1; brc=$?
for m in $(killed_since "$k0"); do
  c=$(next_tier "$(cap_of "$m")"); echo "  KILLED $m at $(cap_of "$m") MiB; solo re-run at $c MiB"
  echo "$m $c" > "$OVR"; k1=$(killed_count)
  build_solo "$m" "resolo_${m##*.}"
  : > "$OVR"
  [ -n "$(killed_since "$k1")" ] && { echo "STOP: $m killed again at $c MiB; re-measure its row in tools/memory_caps.tsv"; exit 3; }
  echo "  $m peak $(awk -F'\t' -v m="$m" '$6 == m {print $1}' "$LOGDIR/memwatch_build.tsv") MiB"
done
if [ -n "$(killed_since "$k0")" ]; then
  k1=$(killed_count); echo "  re-running the build after the solo re-runs"
  "$LAKE" build $BUILD_TARGETS > "$LOGDIR/build.log" 2>&1; brc=$?
  [ -n "$(killed_since "$k1")" ] && { echo "STOP: killed again in the build re-run: $(killed_since "$k1" | tr '\n' ' ')"; exit 3; }
fi
echo "build rc=$brc wall $(( $(date +%s) - t )) s $(tail -1 "$LOGDIR/build.log")"
kill -TERM $WPID 2>/dev/null; wait $WPID 2>/dev/null
echo "memory (phases 0-1): max concurrent leans $(awk '/max_concurrent/{print $2}' "$LOGDIR/memwatch_build.tsv.conc" 2>/dev/null); top:"
head -5 "$LOGDIR/memwatch_build.tsv" 2>/dev/null | awk -F'\t' '{printf "  %s MiB (cap %s) %s\n", $1, $3, $6}'
[ $brc = 0 ] || { echo "RESULT build FAIL"; echo "QUICK_GATE_FAIL"; exit 1; }
echo "RESULT build PASS"

python3 tools/memwatch.py "$LOGDIR/memwatch_checks.tsv" "$ROOT" & WPID=$!
echo "== 2 checks (PAR=$PAR, MemAvailable >= $MINAVAIL_GB GB to start a group)"
running() { local p n=0; for p in "${GPIDS[@]}"; do kill -0 "$p" 2>/dev/null && n=$((n + 1)); done; echo $n; }
GPIDS=()
for g in $GROUPS_ALL; do
  while [ "$(running)" -ge "$PAR" ] || [ "$(avail_gb)" -lt "$MINAVAIL_GB" ]; do sleep 15; done
  echo "start $g $(date -u +%T) (avail $(avail_gb) GB, running $(running))"
  ( g_$g ) > "$LOGDIR/g_$g.out" 2>&1 & GPIDS+=($!)
done
for p in "${GPIDS[@]}"; do wait "$p"; done
kill -TERM $WPID 2>/dev/null; wait $WPID 2>/dev/null
echo "== results"
fail=0
for g in $GROUPS_ALL; do
  echo "---- $g"; cut -c1-220 "$LOGDIR/g_$g.out"
  awk '/^RESULT /{r = $3} END {exit !(r == "PASS" || r == "SKIP")}' "$LOGDIR/g_$g.out" || fail=1
done
echo "memory (checks, recorded): top $(head -3 "$LOGDIR/memwatch_checks.tsv" 2>/dev/null | awk -F'\t' '{printf "%s MiB %s; ", $1, $6}')"
echo "== summary"
awk '/^RESULT /' "$LOGDIR"/g_*.out
date -u +"quick_gate end %F %T UTC (wall $(( $(date +%s) - T0 )) s)"
[ $fail = 0 ] && echo QUICK_GATE_PASS || echo QUICK_GATE_FAIL
exit $fail
