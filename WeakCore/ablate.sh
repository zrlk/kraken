#!/bin/sh
# Reproduce the ablation results quoted in WeakMem.lean's `Arch` comment.
#
# The point of an ablation here is to stop a rule from being load-bearing only
# in the author's head.  Each run below removes one TSO-specific rule and
# reports which tests then disagree with herd7.  A rule that ablates to "0
# failing" is not justified by the suite -- and since an unjustified
# *strengthening* is what makes a proof unsound against real hardware, that is
# a reason to delete the rule, not to keep it.  (That is exactly what happened
# to the TSO store-publication rule.)
#
# Expected:
#   no vRd in TSO load bound  -> MP, IRIW          (2 failing)
#   ARM mayReorder for TSO    -> MP, LB, IRIW      (3 failing)
#   baseline                  -> 0 failing

set -e
LEAN=${LEAN:-$HOME/.elan/bin/lean}
cd "$(dirname "$0")"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

run() {
  desc=$1
  file=$2
  echo "=== $desc ==="
  "$LEAN" --run "$file" 2>&1 |
    sed -n -e 's/^\(FAIL .*\)$/  \1/p' \
           -e 's/^\([0-9]* tests.*\)$/  \1/p'
}

run "baseline" WeakMem.lean

sed 's/let ordered := if arch = .tso then vs.vRd else 0/let ordered := 0/' \
  WeakMem.lean > "$tmp/NoLoadBound.lean"
run "ablate: no vRd in TSO load bound" "$tmp/NoLoadBound.lean"

sed 's/^  match arch with$/  match Arch.arm with/' \
  WeakMem.lean > "$tmp/ArmReorder.lean"
run "ablate: ARM mayReorder for TSO" "$tmp/ArmReorder.lean"
