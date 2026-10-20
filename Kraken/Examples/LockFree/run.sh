#!/usr/bin/env bash
# Regression runner for the lock-free `.kl` examples.
#
#   Kraken/Examples/LockFree/run.sh [-isa aarch64|x64] [-timeout SECS] [-slow] DIR|FILE...
#
# Every `.kl` file is run with `.lake/build/bin/krakenlitmus_<isa>` and the
# flags given on its `# flags: ...` line (plus `-v -fuel 300`), and the
# `Observation NAME Always|Sometimes|Never` word is compared with the file's
# `# expect: Always|Sometimes|Never` line. Files with a `# slow` line (more
# than a couple of minutes) are skipped unless `-slow` is given. Exit status
# is non-zero if any file disagrees, faults, is unsupported, or times out.
set -u
root="$(cd "$(dirname "$0")/../../.." && pwd)"
isa=aarch64
timeout_secs=600
slow=0
args=()
while [ $# -gt 0 ]; do
  case "$1" in
    -isa) isa="$2"; shift 2 ;;
    -timeout) timeout_secs="$2"; shift 2 ;;
    -slow) slow=1; shift ;;
    *) args+=("$1"); shift ;;
  esac
done
bin="$root/.lake/build/bin/krakenlitmus_$isa"
if [ ! -x "$bin" ]; then
  echo "missing $bin; run: (cd $root && lake build krakenlitmus_$isa)" >&2
  exit 2
fi
if [ ${#args[@]} -eq 0 ]; then
  case "$isa" in
    aarch64) args=("$root/Kraken/Examples/LockFree/AArch64") ;;
    x64) args=("$root/Kraken/Examples/LockFree/X64") ;;
  esac
fi
files=()
for a in "${args[@]}"; do
  if [ -d "$a" ]; then
    while IFS= read -r f; do files+=("$f"); done < <(find "$a" -maxdepth 1 -name '*.kl' | sort)
  else
    files+=("$a")
  fi
done

fail=0
printf '%-28s %-10s %-10s %-9s %8s  %s\n' FILE EXPECT GOT CONFIGS TIME FLAGS
for f in "${files[@]}"; do
  name="$(basename "$f")"
  flags="$(sed -n 's/^# *flags:[[:space:]]*//p' "$f" | head -1)"
  expect="$(sed -n 's/^# *expect:[[:space:]]*//p' "$f" | head -1 | tr -d '[:space:]')"
  if [ $slow -eq 0 ] && grep -q '^# *slow' "$f"; then
    printf '%-28s %-10s %-10s %-9s %8s  %s\n' "$name" "$expect" "-" "-" "-" "skipped (slow; use -slow)"
    continue
  fi
  if [ -z "$expect" ]; then
    printf '%-28s %-10s %-10s %-9s %8s  %s\n' "$name" "?" "-" "-" "-" "no '# expect:' line"
    fail=1; continue
  fi
  start=$(date +%s.%N)
  # shellcheck disable=SC2086
  out="$(timeout "$timeout_secs" "$bin" -v -fuel 300 $flags "$f" 2>&1)"
  rc=$?
  end=$(date +%s.%N)
  secs=$(printf '%.1fs' "$(echo "$end - $start" | bc)")
  got="$(printf '%s\n' "$out" | sed -n 's/^Observation [^ ]* \([A-Za-z]*\).*/\1/p' | head -1)"
  configs="$(printf '%s\n' "$out" | sed -n 's/^Configs \([0-9]*\).*/\1/p' | head -1)"
  note=""
  if [ $rc -eq 124 ]; then got="TIMEOUT"; fi
  if printf '%s\n' "$out" | grep -q '^Fault'; then note="$note FAULT"; fi
  if printf '%s\n' "$out" | grep -q '^Unsupported'; then note="$note UNSUPPORTED: $(printf '%s\n' "$out" | grep '^Unsupported' | head -1)"; fi
  if printf '%s\n' "$out" | grep -q 'certification budget hit'; then note="$note (budget hit)"; fi
  status=ok
  if [ "$got" != "$expect" ] || [ -n "$note" ]; then status=FAIL; fail=1; fi
  printf '%-28s %-10s %-10s %-9s %8s  %s %s%s\n' "$name" "$expect" "${got:-none}" "${configs:--}" "$secs" "$flags" "$status" "$note"
done
exit $fail
