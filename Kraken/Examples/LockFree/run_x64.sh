#!/bin/bash
# Run the x64 lock-free examples and compare each verdict with the file's
# `# expect:` line. Each `.kl` carries, inside its header comment,
#     # flags: <extra krakenlitmus_x64 flags>
#     # expect: Always|Sometimes|Never
# Usage: run_x64.sh [-slow] [file.kl ...]      (default: every .kl in X64/)
# Prints one table row per example (name, verdict, expected, Configs,
# seconds) and exits non-zero if any verdict differs from the expectation.
# Files with a `# slow` line (more than a couple of minutes) are skipped
# unless `-slow` is given, as in run.sh.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
bin="$root/.lake/build/bin/krakenlitmus_x64"
if [ ! -x "$bin" ]; then
  echo "missing $bin; run: (cd $root && lake build krakenlitmus_x64)" >&2
  exit 2
fi
slow=0
files=()
for a in "$@"; do
  case "$a" in
    -slow) slow=1 ;;
    *) files+=("$a") ;;
  esac
done
if [ ${#files[@]} -eq 0 ]; then files=("$here"/X64/*.kl); fi
status=0
printf '%-20s %-10s %-10s %10s %8s  %s\n' example verdict expected configs seconds flags
for f in "${files[@]}"; do
  name=$(basename "$f" .kl)
  flags=$(sed -n 's/^[[:space:]]*#[[:space:]]*flags:[[:space:]]*//p' "$f" | head -1)
  expect=$(sed -n 's/^[[:space:]]*#[[:space:]]*expect:[[:space:]]*//p' "$f" | head -1)
  if [ $slow -eq 0 ] && grep -q '^[[:space:]]*#[[:space:]]*slow' "$f"; then
    printf '%-20s %-10s %-10s %10s %8s  %s\n' "$name" "-" "$expect" "-" "-" "skipped (slow; use -slow)"
    continue
  fi
  start=$(date +%s.%N)
  # shellcheck disable=SC2086
  out=$("$bin" -v $flags "$f" 2>&1)
  end=$(date +%s.%N)
  secs=$(printf '%.1f' "$(echo "$end - $start" | bc)")
  verdict=$(echo "$out" | sed -n 's/^Observation [^ ]* \([A-Za-z]*\).*/\1/p' | head -1)
  configs=$(echo "$out" | sed -n 's/^Configs \([0-9]*\).*/\1/p' | head -1)
  if echo "$out" | grep -q "^Unsupported\|^Fault"; then verdict="ERROR"; fi
  mark=""
  if [ "$verdict" != "$expect" ]; then mark="  <-- MISMATCH"; status=1; fi
  printf '%-20s %-10s %-10s %10s %8s  %s%s\n' "$name" "$verdict" "$expect" "$configs" "$secs" "$flags" "$mark"
  if [ "$verdict" = "ERROR" ]; then echo "$out" | grep "^Unsupported\|^Fault" | sed 's/^/    /'; fi
done
exit $status
