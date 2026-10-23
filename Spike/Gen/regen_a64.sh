#!/usr/bin/env bash
# Regenerate a per-node instance's program data from its source, or check
# that the committed files are what a fresh regeneration writes.
#
# Usage: Spike/Gen/regen_a64.sh NAME MOD [--check]
#   NAME   the program: Spike/Gen/NAME.w
#          (if its first line is "-- Copy of Scc/Test/NAME.w...", the rest
#          must equal Scc/Test/NAME.w, checked first)
#   MOD    the module stem: Spike/Lib/MOD{Code,Place,Rows}.lean
#
# Writes, from `scc --arch arm --code --blocks --cert` and genrows_a64.py:
#   Spike/Lib/MODCode.lean   scc --code's output, verbatim;
#   Spike/Lib/MODPlace.lean  scc --blocks' placement data, its namespace
#                            `SccPlace` renamed `SccPlace.NAME` (one per program);
#   Spike/Lib/MODRows.lean   genrows_a64.py's rows;
#   Spike/Test/Cert/MODCert.lean  scc --cert's certificate, verbatim.
# With --check, writes them under .lake/spike-gen/ instead and fails (exit 1)
# if any differs from the committed file: the generated data is stale.
# `scc` is built first (`lake` from `$LAKE`).
# CERT_FAILS=N (env): the program is known not to satisfy PlaceOK component
# aN (Scc/Test/placediag.sh names it); scc gets `--cert-fails N` and writes
# the negative certificate `prog_not_placeOK` instead of the positive one.
set -eu

if [ $# -lt 2 ] || [ $# -gt 3 ]; then echo "usage: $0 NAME MOD [--check]" >&2; exit 2; fi
NAME=$1; MOD=$2; CHECK=0
if [ $# = 3 ]; then
  if [ "$3" = --check ]; then CHECK=1; else echo "usage: $0 NAME MOD [--check]" >&2; exit 2; fi
fi
LAKE=${LAKE:-lake}
FAILS=()
if [ -n "${CERT_FAILS:-}" ]; then FAILS=(--cert-fails "$CERT_FAILS"); fi
cd "$(dirname "$0")/../.."
# A program copied from Scc/Test says so on its first line; the rest of the
# file must equal the original (in both modes), so the copies cannot drift.
if head -n 1 "Spike/Gen/$NAME.w" | grep -q "^-- Copy of Scc/Test/$NAME.w"; then
  if ! tail -n +2 "Spike/Gen/$NAME.w" | cmp -s - "Scc/Test/$NAME.w"; then
    echo "DRIFT Spike/Gen/$NAME.w differs from Scc/Test/$NAME.w (after its first line)"; exit 1
  fi
fi
"$LAKE" build scc >/dev/null
SCC=.lake/build/bin/scc
T=.lake/spike-gen/$NAME
mkdir -p "$T"
"$SCC" --arch arm -o "$T/$NAME.s" --code "$T/c.lean" --blocks "$T/b.lean" --cert "$T/cert.lean" "${FAILS[@]}" "Spike/Gen/$NAME.w" >/dev/null
sed -e "s/^namespace SccPlace\$/namespace SccPlace.$NAME/" -e "s/^end SccPlace\$/end SccPlace.$NAME/" \
  "$T/b.place.lean" > "$T/place.lean"
cp "$T/c.lean" "$T/code.lean"
python3 Spike/Gen/genrows_a64.py "$NAME" "$T/$NAME.s" "$T/code.lean" "$T/place.lean" "$T/rows.lean" \
  "Spike.Lib.${MOD}Code" >/dev/null

if [ "$CHECK" = 0 ]; then
  cp "$T/code.lean" "Spike/Lib/${MOD}Code.lean"
  cp "$T/place.lean" "Spike/Lib/${MOD}Place.lean"
  cp "$T/rows.lean" "Spike/Lib/${MOD}Rows.lean"
  mkdir -p Spike/Test/Cert
  cp "$T/cert.lean" "Spike/Test/Cert/${MOD}Cert.lean"
  echo "regenerated Spike/Lib/${MOD}{Code,Place,Rows}.lean, Spike/Test/Cert/${MOD}Cert.lean"
else
  st=0
  for k in Code:code Place:place Rows:rows; do
    f="Spike/Lib/${MOD}${k%%:*}.lean"
    if ! cmp -s "$T/${k##*:}.lean" "$f"; then echo "STALE $f (fresh: $T/${k##*:}.lean)"; st=1; fi
  done
  f="Spike/Test/Cert/${MOD}Cert.lean"
  if ! cmp -s "$T/cert.lean" "$f"; then echo "STALE $f (fresh: $T/cert.lean)"; st=1; fi
  [ "$st" = 0 ] && echo "up to date: Spike/Lib/${MOD}{Code,Place,Rows}.lean, $f"
  exit "$st"
fi
