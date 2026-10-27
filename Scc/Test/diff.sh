#!/usr/bin/env bash
# Differential test: compile random programs with scc, run them, and compare
# the exit status with WeakCore's own machine.
#
# Usage: Scc/Test/diff.sh [--arch x64|arm] [--arm-run qemu|native|auto] [-n N] [--seed S]
#                         [--place K] [--place-check] [--narrow]
#
# Scc.Test.Gen writes programs 0 .. N-1 of stream S (well-typed,
# single-threaded, in scc's accepted fragment) and their reference outcomes
# (Scc.Test.RefEval: WeakCore's TermRun machine with scc's checked `Int` `+`)
# to .lake/scc-diff/ARCH/.  Each program is compiled, assembled, linked and
# run; its exit status must equal the reference's (main's result mod 256).
# A reference overflow abort must be exit status 101 with the overflow
# message on standard error; a 101 the reference does not predict is a
# mismatch (the programs stay far below the heap and stack limits).  A
# program the frontend rejects is a generator bug.  Mismatching programs are
# listed and kept in the work directory.
#
# The PlaceOK gate (--place K, K >= 1): every Kth program (programs 0, K,
# 2K, ...; K = 1 all of them) also gets a certificate (`scc --cert`), and
# the first failing component of `placeOK` on its output is evaluated
# (Scc/Test/placediag.sh, untrusted). A program is certifiable when every
# component holds; not certifiable, with the reason, when it is outside the
# certified fragment (no stack need table) or a component AN fails; a
# failure when scc cannot write the certificate or it cannot be evaluated.
# Not certifiable is counted, not a failure: generated programs may lie
# outside the fragment, and a regression shows as a drop in the count of
# certifiable ones (or a new aN). With --place-check the kernel also checks
# each certifiable program's certificate (`scc --check`; much slower), and
# one that does not check is a failure. Each evaluation's (and check's)
# wall time and peak RssAnon (Scc/Test/rssanon.sh) are summed and the peak
# kept; the per-program lines are in place.txt in the work directory. A
# program whose evaluation or check peaks above --keep-mb MB RssAnon
# (default 3584) keeps its certificate files in the work directory for
# profiling, listed in kept.txt; --keep keeps every program's.
#
# --narrow generates no function of more than six argument words (see
# Scc.Test.Gen.program), so that the PlaceOK sample is not all stack-passed
# argument spills; tools/diff_place.sh pins both samples' outcomes.
#
# Environment: LAKE (default `lake`) is the lake command.  Arm binaries run
# under qemu-aarch64 or natively (--arm-run; see Scc/Test/armrun.sh).
set -u

ARCH=x64; N=100; SEED=1; PLACE=0; PLACE_CHECK=0; KEEP_MB=3584; KEEP_ALL=0; NARROW=false
while [ $# -gt 0 ]; do
  case "$1" in
    --arch) ARCH="$2"; shift 2 ;;
    --arm-run) ARM_RUN="$2"; shift 2 ;;
    -n) N="$2"; shift 2 ;;
    --seed) SEED="$2"; shift 2 ;;
    --place) PLACE="$2"; shift 2 ;;
    --place-check) PLACE_CHECK=1; shift ;;
    --keep-mb) KEEP_MB="$2"; shift 2 ;;
    --keep) KEEP_ALL=1; shift ;;
    --narrow) NARROW=true; shift ;;
    *) echo "usage: $0 [--arch x64|arm] [--arm-run qemu|native|auto] [-n N] [--seed S] [--place K] [--place-check]"
       echo "       [--keep-mb MB] [--keep] [--narrow]" >&2
       exit 2 ;;
  esac
done
case "$ARCH" in x64|arm) ;; *) echo "unknown arch $ARCH" >&2; exit 2 ;; esac
case "$PLACE" in ''|*[!0-9]*) echo "--place needs a number" >&2; exit 2 ;; esac
case "$KEEP_MB" in ''|*[!0-9]*) echo "--keep-mb needs a number" >&2; exit 2 ;; esac
. "$(dirname "$0")/armrun.sh"
[ "$ARCH" = arm ] && arm_run_resolve

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
LAKE=${LAKE:-lake}
WORK="$ROOT/.lake/scc-diff/$ARCH"
SCC="$ROOT/.lake/build/bin/scc"
OVF="scc: abort: Int addition overflow"

(cd "$ROOT" && $LAKE build scc scc_x64 scc_arm Scc.Test.Gen) >/dev/null || { echo "FAIL: lake build"; exit 1; }
rm -rf "$WORK"; mkdir -p "$WORK"; cd "$WORK" || exit 1

# Generate the programs and the reference outcomes (`#eval`: WeakCore already
# defines the root `main`, so the driver cannot be run with `lean --run`).
printf 'import Scc.Test.Gen\n#eval Scc.Test.Gen.batch "%s" %s %s (narrow := %s)\n' "$WORK" "$N" "$SEED" "$NARROW" \
  >gen_driver.lean
(cd "$ROOT" && $LAKE env lean "$WORK/gen_driver.lean") || { echo "FAIL: generator"; exit 1; }

link() {
  if [ "$ARCH" = x64 ]; then
    as -o "$1.o" "$1.s" && ld -static -o "$1" "$1.o"
  else
    clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld -o "$1" "$1.s"
  fi
}

runbin() {
  if [ "$ARCH" = x64 ]; then
    timeout 20 "./$1" >"$1.out" 2>"$1.err"
  else
    arm_exec "./$1" >"$1.out" 2>"$1.err"
  fi
  echo $?
}

# The PlaceOK gate on program NAME (index IDX): appends a line to place.txt
# and updates the counts. The marker of a certificate outside the fragment
# is run.sh's (`Scc.Cert.Gen.outsideMark`).
OUTSIDE="-- outside the certified fragment: no stack need table (non-tail recursion)"
RSS="$ROOT/Scc/Test/rssanon.sh"
pl_n=0; pl_ok=0; pl_out=0; pl_an=0; pl_fail=0; pl_checked=0
pl_secs=0; pl_peak=0; ck_secs=0; ck_peak=0
declare -A pl_why=()
measure() {  # measure OUT: add OUT's SECS:KB to the totals named by $2/$3
  local secs kb
  [ -f "$1" ] || return 0
  IFS=: read -r secs kb <"$1"
  printf -v "$2" '%s' "$(echo "${!2} + ${secs:-0}" | bc)"
  [ -n "$kb" ] && [ "$kb" -gt "${!3}" ] && printf -v "$3" '%s' "$kb"
  return 0
}
peakkb() {  # peakkb OUT: OUT's KB, or 0
  local secs kb
  [ -f "$1" ] || { echo 0; return; }
  IFS=: read -r secs kb <"$1"
  echo "${kb:-0}"
}
pl_kept=0
place() {
  local name=$1 an pk=0 k
  pl_n=$((pl_n + 1))
  if ! "$SCC" --arch "$ARCH" --cert "$name.cert.lean" -o "$name.cert.s" "$name.w" 2>"$name.cert.err"; then
    pl_fail=$((pl_fail + 1)); echo "$name fail scc --cert: $(head -c 300 "$name.cert.err")" >>place.txt
    bad+=("$name: scc --cert failed"); return
  fi
  if grep -qxF -- "$OUTSIDE" "$name.cert.lean"; then
    pl_out=$((pl_out + 1)); pl_why["no need table"]=$((${pl_why["no need table"]:-0} + 1))
    echo "$name outside no-need-table" >>place.txt; rm -f "$name.cert.lean" "$name.cert.s" "$name.cert.err"; return
  fi
  rm -f place.rss
  an=$(LAKE="$LAKE" "$RSS" place.rss "$ROOT/Scc/Test/placediag.sh" --arch "$ARCH" "$name.cert.lean" 2>"$name.diag.err")
  measure place.rss pl_secs pl_peak
  pk=$(peakkb place.rss)
  case "$an" in
    none)
      if [ "$PLACE_CHECK" = 1 ]; then
        rm -f place.rss
        if LAKE="$LAKE" "$RSS" place.rss "$SCC" --arch "$ARCH" --check "$name.cert.lean" >"$name.check.out" 2>&1; then
          measure place.rss ck_secs ck_peak; pl_checked=$((pl_checked + 1))
          k=$(peakkb place.rss); [ "$k" -gt "$pk" ] && pk=$k
        else
          measure place.rss ck_secs ck_peak
          pl_fail=$((pl_fail + 1)); echo "$name fail check: $(head -c 300 "$name.check.out")" >>place.txt
          bad+=("$name: placeOK holds but the certificate does not check"); return
        fi
      fi
      pl_ok=$((pl_ok + 1)); echo "$name certifiable" >>place.txt ;;
    a[0-9]*)
      pl_an=$((pl_an + 1)); pl_why["$an"]=$((${pl_why["$an"]:-0} + 1))
      echo "$name not-certifiable $an" >>place.txt; return ;;
    *)
      pl_fail=$((pl_fail + 1)); echo "$name fail placediag: $(head -c 300 "$name.diag.err")" >>place.txt
      bad+=("$name: placeOK could not be evaluated"); return ;;
  esac
  if [ "$KEEP_ALL" = 1 ] || [ "$pk" -gt $((KEEP_MB * 1024)) ]; then
    pl_kept=$((pl_kept + 1)); echo "$name peak RssAnon $((pk / 1024)) MB" >>kept.txt; return
  fi
  rm -f "$name.cert.lean" "$name.cert.s" "$name.cert.err" "$name.cert.diag.lean" "$name.diag.err" "$name.check.out"
}

agree=0; mismatch=0; rejected=0; noverdict=0; ovf=0
bad=()
idx=-1
: >place.txt; : >kept.txt
while read -r name code rest; do
  idx=$((idx + 1))
  case "$rest" in
    rejected*) rejected=$((rejected + 1)); bad+=("$name: rejected by the frontend (generator bug): ${rest#rejected }"); continue ;;
  esac
  if [ "$PLACE" -gt 0 ] && [ $((idx % PLACE)) -eq 0 ]; then place "$name"; fi
  if [ "$code" = - ]; then noverdict=$((noverdict + 1)); continue; fi
  if ! "$SCC" --arch "$ARCH" -o "$name.s" "$name.w" 2>"$name.scc.err"; then
    mismatch=$((mismatch + 1)); bad+=("$name: scc failed: $(head -c 300 "$name.scc.err")"); continue
  fi
  if ! link "$name" 2>"$name.link.err"; then
    mismatch=$((mismatch + 1)); bad+=("$name: assemble/link failed: $(head -c 300 "$name.link.err")"); continue
  fi
  rc=$(runbin "$name")
  err=$(head -n 1 "$name.err")
  # A returning reference: the same status and no abort message.  An overflow
  # abort: status 101 and the overflow message.
  case "$rest" in
    abort*) want_err="$OVF" ;;
    *) want_err="" ;;
  esac
  if [ "$rc" = "$code" ] && [ "$err" = "$want_err" ]; then
    agree=$((agree + 1))
    [ -n "$want_err" ] && ovf=$((ovf + 1))
    rm -f "$name" "$name.o" "$name.s" "$name.out" "$name.err" "$name.scc.err" "$name.link.err"
  else
    mismatch=$((mismatch + 1))
    bad+=("$name: exit $rc (stderr: ${err:-none}), reference: $rest")
  fi
done <ref.txt

for b in "${bad[@]}"; do echo "MISMATCH $b"; done
echo "$ARCH seed $SEED: $N programs, $agree agree ($ovf overflow aborts), $mismatch mismatches, $rejected rejected, $noverdict without a reference verdict"
if [ "$PLACE" -gt 0 ]; then
  why=""; for k in "${!pl_why[@]}"; do why="$why, $k: ${pl_why[$k]}"; done
  echo "$ARCH seed $SEED placeOK (every program numbered a multiple of $PLACE): $pl_n programs, $pl_ok certifiable, $((pl_out + pl_an)) not certifiable${why:+ (${why#, })}, $pl_fail failed"
  [ "$pl_n" -gt "$pl_out" ] && echo "  placediag: $pl_secs s total, $(echo "scale=2; $pl_secs / ($pl_n - $pl_out)" | bc) s per evaluated program, peak RssAnon $((pl_peak / 1024)) MB"
  [ "$PLACE_CHECK" = 1 ] && [ "$pl_checked" -gt 0 ] && echo "  check: $pl_checked kernel-checked, $ck_secs s total, $(echo "scale=2; $ck_secs / $pl_checked" | bc) s each, peak RssAnon $((ck_peak / 1024)) MB"
  [ "$pl_kept" -gt 0 ] && echo "  kept: $pl_kept programs' certificate files (kept.txt)"
fi
[ $mismatch -eq 0 ] && [ $rejected -eq 0 ] && [ $pl_fail -eq 0 ]
