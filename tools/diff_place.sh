#!/usr/bin/env bash
# The PlaceOK samples of the differential test, with their outcomes pinned.
#
# Usage: tools/diff_place.sh [x64|arm ...]   (default: both)
#
# For each ISA, two runs of Scc/Test/diff.sh -n 300 --seed 70 --place 10
# (30 sampled programs each):
#
# * wide (the default generator): every sampled program that has a stack need
#   table passes stack-passed arguments (`gw`, `w·x`: more than six argument
#   words), which placeOK does not certify yet (A12, x64's `fnOk1` `spills`).
#   The expected outcome is asserted exactly, so that a change, including a fix
#   of A12, must update it deliberately.
# * narrow (--narrow: no function of more than six argument words, see
#   Scc.Test.Gen.program): exercises placeOK on certifiable programs.
#
# Each run must pass diff.sh (no mismatch, rejection or placeOK failure) and its
# place.txt must count exactly the expected certifiable / not-certifiable a12 /
# outside programs; any other outcome is a failure. Diff.sh alone counts not
# certifiable as success, so a drop in coverage would pass as "0 failed".
#
# Expected outcomes ("certifiable a12 outside other"), measured when this script was added; both samples, both ISAs.
EXPECT_x64_wide="0 19 11 0"
EXPECT_arm_wide="0 19 11 0"
EXPECT_x64_narrow="21 0 9 0"
EXPECT_arm_narrow="21 0 9 0"
set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)
archs=("$@"); [ ${#archs[@]} -eq 0 ] && archs=(x64 arm)
status=0
for a in "${archs[@]}"; do
  case "$a" in x64|arm) ;; *) echo "unknown arch $a" >&2; exit 2 ;; esac
  for mode in wide narrow; do
    flag=""; [ "$mode" = narrow ] && flag=--narrow
    var="EXPECT_${a}_${mode}"; want=${!var}
    out=$(bash "$ROOT/Scc/Test/diff.sh" --arch "$a" -n 300 --seed 70 --place 10 $flag 2>&1); rc=$?
    echo "$out" | tail -4
    pt="$ROOT/.lake/scc-diff/$a/place.txt"
    if [ "$rc" -ne 0 ] || [ ! -f "$pt" ]; then
      echo "FAIL: $a $mode: diff.sh failed (exit $rc)"; status=1; continue
    fi
    c=$(grep -c ' certifiable$' "$pt"); n=$(grep -c ' not-certifiable a12$' "$pt")
    o=$(grep -c ' outside no-need-table$' "$pt"); t=$(wc -l <"$pt")
    got="$c $n $o $((t - c - n - o))"
    if [ "$got" = "$want" ]; then
      echo "OK: $a $mode: certifiable a12 outside other = $got"
    else
      echo "FAIL: $a $mode: certifiable a12 outside other = $got, expected $want (see $pt);"
      echo "  if intended, update EXPECT_${a}_${mode} in $0"
      status=1
    fi
    cp "$pt" "$ROOT/.lake/scc-diff/$a/place-$mode.txt"
  done
done
exit $status
