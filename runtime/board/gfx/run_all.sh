#!/bin/sh
# Board experiment kit: collect the graphics and NIC facts, run gtcoh, pack
# the results into gfx-board-<date>.tar.gz in the current directory.
#
# Usage: run_all.sh [--gtcoh PATH] [--iters N] [--quick] [--no-stress]
#
# Order: read-only facts first (graphics, then ../nic), then the gtcoh dry
# run, then the GPU modes without and with the cache-stress thread, then the
# kernel log again (to record any GPU hang or engine reset). Every step has a
# time bound.

set -u

HERE=$(cd "$(dirname "$0")" && pwd)
GTCOH=$HERE/gtcoh
ITERS=100000
STRESS=1
MAXS=600 # seconds per gtcoh mode

while [ $# -gt 0 ]; do
  case $1 in
  --gtcoh) GTCOH=$2; shift 2 ;;
  --iters) ITERS=$2; shift 2 ;;
  --quick) ITERS=1000; MAXS=60; shift ;;
  --no-stress) STRESS=0; shift ;;
  -h | --help)
    sed -n '2,11p' "$0"
    exit 0
    ;;
  *)
    echo "run_all.sh: unknown argument $1" >&2
    exit 1
    ;;
  esac
done

STAMP=$(date -u +%Y%m%d-%H%M%S)
NAME=gfx-board-$STAMP
OUT=$PWD/$NAME
mkdir -p "$OUT" || exit 1
LOG=$OUT/run_all.log

log() { echo "$*" | tee -a "$LOG"; }

log "run_all: start $(date -u) as uid $(id -u)"
[ "$(id -u)" -eq 0 ] || log "run_all: not root; dmesg, debugfs and lspci capabilities may be missing"

# 1. Facts (read-only).
timeout -k 10 300 sh "$HERE/facts.sh" "$OUT/facts" >>"$LOG" 2>&1
log "run_all: facts exit=$?"
if [ -f "$HERE/../nic/facts.sh" ]; then
  timeout -k 10 300 sh "$HERE/../nic/facts.sh" "$OUT/nic" >>"$LOG" 2>&1
  log "run_all: nic facts exit=$?"
else
  log "run_all: no ../nic/facts.sh; skipping NIC facts"
fi

# 2. gtcoh.
if [ ! -x "$GTCOH" ]; then
  log "run_all: no gtcoh binary at $GTCOH; skipping GPU experiments"
else
  "$GTCOH" --dry-run >"$OUT/gtcoh-dry-run.txt" 2>&1
  log "run_all: gtcoh dry run exit=$?"
  # Four modes, each bounded by --max-seconds; the outer timeout is a
  # backstop (four modes plus slack).
  BOUND=$((4 * MAXS + 60))
  timeout -k 10 "$BOUND" "$GTCOH" --iters "$ITERS" --max-seconds "$MAXS" \
    --verbose >"$OUT/gtcoh.txt" 2>&1
  rc=$?
  log "run_all: gtcoh exit=$rc"
  tee -a "$LOG" <"$OUT/gtcoh.txt"
  # Exit codes 2, 3 and 4 mean no device, no permission or no driver
  # support: the stress run would fail the same way. 5 means a GPU error:
  # do not submit more work.
  if [ "$STRESS" -eq 1 ] && { [ $rc -eq 0 ] || [ $rc -eq 6 ]; }; then
    timeout -k 10 "$BOUND" "$GTCOH" --iters "$ITERS" --max-seconds "$MAXS" \
      --stress --verbose >"$OUT/gtcoh-stress.txt" 2>&1
    log "run_all: gtcoh --stress exit=$?"
  fi
fi

# 3. Kernel log after the GPU work, and the submission mode once more.
timeout 10 dmesg 2>&1 | awk 'tolower($0) ~ /i915|guc|huc|drm|dmar|hang|reset/' \
  >"$OUT/dmesg-gfx-after.txt"
log "run_all: done $(date -u)"

# 4. One tarball to send back.
tar -C "$PWD" -czf "$NAME.tar.gz" "$NAME" && log "run_all: wrote $PWD/$NAME.tar.gz"
