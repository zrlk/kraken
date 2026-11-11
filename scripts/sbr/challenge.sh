#!/bin/bash
# The challenge step (ci.sh step 7, optional, SBR_CHALLENGE=1): judges the proof with Lake's
# built-in comparator, `lake challenge`.
#   1. challenge.py: KrakenSbrChallenge/Challenge.lean states exactly the theorems challenge.json
#      names, each with `by sorry`, and nothing else forbidden; Solution.lean has only imports.
#   2. lake build of the two modules (under SBR_CAP_CMD), so that the sandboxed builds below
#      find every module built and only replay them.
#   3. lake challenge --config scripts/sbr/challenge.json: in a bwrap sandbox, builds and exports
#      both modules, checks that each named theorem of the solution has the challenge's
#      statement and uses only the permitted axioms, and replays the solution through the kernel
#      (leanchecker) in a separate process. About 70 minutes, most of it in the replay.
# Needs bwrap (bubblewrap) on PATH, or COMPARATOR_BWRAP.
set -u
. "$(dirname "${BASH_SOURCE[0]}")/common.sh"
OUT=$SBR_OUT/challenge
rm -rf "$OUT"; mkdir -p "$OUT"
python3 "$SBR_DIR/challenge.py" || exit 1
"${CAP[@]}" lake build KrakenSbrChallenge.Challenge KrakenSbrChallenge.Solution \
  > "$OUT/build.log" 2>&1 || { tail -20 "$OUT/build.log"; echo "challenge: build failed"; exit 1; }
"${CAP[@]}" lake challenge --config "$SBR_DIR/challenge.json" > "$OUT/challenge.log" 2>&1; rc=$?
grep -E '^(Running|Lean default|Your solution|error)' "$OUT/challenge.log"
[ $rc = 0 ] && grep -q '^Your solution is okay!' "$OUT/challenge.log" || {
  echo "challenge: lake challenge rc=$rc (log: $OUT/challenge.log)"; exit 1; }
echo "challenge: accepted"
