#!/bin/bash
# Regression corpus for x86 non-temporal stores (`movnti`, see
# README.md here): every test of the model-fidelity sweep's x86_64 families
# (../sweep/gen.sh) that uses diy's `NT` annotation, plus the hand-written
# tests in `hand/`. herd7's output on each test is cached as
# `<test>.litmus.herd` (`Time`/`Hash` lines removed); then the independent SDM
# model (`sdm_model.py --write`) writes `<test>.litmus.sdm` wherever the SDM
# allows more than herd (herd treats `movnti` as an ordinary TSO store).
#
# Needs herdtools7 master (7.58+1 or later): herd7 7.58 from opam does not
# know the `NT` annotation.
#
# Usage: gen.sh <herdtools7 install/bin dir>
set -euo pipefail
BIN=${1:?herdtools7 bin dir}
DST=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$DST/../../../.." && pwd)
TMP=$(mktemp -d "$DST/.gen.XXXXXX")
trap 'rm -rf "$TMP"' EXIT

HERD_TIMEOUT=600 "$ROOT/Kraken/Litmus/corpus/sweep/gen.sh" "$BIN" "$TMP" >/dev/null
rm -f "$DST"/*.litmus "$DST"/*.litmus.herd "$DST"/*.litmus.sdm
for t in "$TMP"/x86_64/*/*.litmus; do
  if awk '/movnti/ { found = 1 } END { exit !found }' "$t"; then
    cp "$t" "$DST/"
  fi
done

n=0
for t in "$DST"/*.litmus "$DST"/hand/*.litmus; do
  ( cd "$(dirname "$t")" && "$BIN/herd7" "$(basename "$t")" 2>/dev/null || true ) \
    | grep -v '^Time \|^Hash=' > "$t.herd"
  n=$((n+1))
done
python3 "$DST/sdm_model.py" --write "$DST"/*.litmus "$DST"/hand/*.litmus >/dev/null
echo "x86_64-nt: $n tests, $(ls "$DST"/*.sdm "$DST"/hand/*.sdm | wc -l) SDM oracles"
echo "generated with $("$BIN/herd7" -version)" > "$DST/ORACLE.txt"
