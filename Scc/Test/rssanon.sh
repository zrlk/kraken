#!/usr/bin/env bash
# Run a command and record its wall time and the peak resident anonymous
# memory (`RssAnon` of /proc/PID/status) of its process tree: untrusted, a
# measurement for the memory budget only.
#
# Usage: Scc/Test/rssanon.sh OUT CMD [ARG...]
#   Runs CMD, sampling every 0.2 s the `RssAnon` of every process below it
#   and keeping the largest single value (the peak of the `lean` child that
#   `scc --check` runs, in practice). Writes `SECS:KB` to OUT (seconds of
#   wall time, peak RssAnon in KiB) and exits with CMD's status.
#   Without /proc (or without `RssAnon` in it) it writes `SECS:` (no
#   figure), so that callers fall back to their other measurement.
#
# Sampling misses a peak shorter than the period: the figure is a lower
# bound, accurate for the kernel's checks (tens of seconds at their peak).
set -u

if [ $# -lt 2 ]; then echo "usage: $0 OUT CMD [ARG...]" >&2; exit 2; fi
out=$1; shift

# The processes below PID (itself excluded), depth first.
below() {
  local c
  for c in $(pgrep -P "$1" 2>/dev/null); do echo "$c"; below "$c"; done
}

# The largest RssAnon (KiB) among the processes below PID, 0 if none reads.
sample() {
  local m=0 p v
  for p in $(below "$1"); do
    v=$(awk '/^RssAnon:/ {print $2; exit}' "/proc/$p/status" 2>/dev/null)
    [ -n "$v" ] && [ "$v" -gt "$m" ] && m=$v
  done
  echo "$m"
}

start=$(date +%s.%N)
"$@" &
pid=$!
peak=0
if [ -r /proc/self/status ] && grep -q '^RssAnon:' /proc/self/status; then
  while kill -0 "$pid" 2>/dev/null; do
    v=$(sample "$pid")
    [ "$v" -gt "$peak" ] && peak=$v
    sleep 0.2
  done
else
  peak=""
fi
wait "$pid"; st=$?
end=$(date +%s.%N)
secs=$(awk -v a="$start" -v b="$end" 'BEGIN {printf "%.2f", b - a}')
[ "$peak" = 0 ] && peak=""
echo "$secs:$peak" >"$out"
exit $st
