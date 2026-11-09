#!/usr/bin/env bash
# Regenerate Spike/Test/X64Ret0Offs.lean (ret0.w's and hello1.w's x64 block
# offsets and single instructions) from the committed scc --code data, or
# check that the committed file is what a fresh regeneration writes.
#
# Usage: Spike/Gen/regen_offs_x64.sh [--check]
#
# Reads Spike/Lib/X64Ret0Code.lean and Spike/Lib/X64Hello1Code.lean
# (regen_x64.sh's output: the listing, its instruction sizes, its cells and
# scc --code's block table); writes Spike/Gen/GenOffsX64.lean's `render`:
#   ret0Offs, hello1Offs   Scc.Cert.Blocks.offsX64's analysis of the listing;
#   ret0Evs, hello1Evs     per group of the table, the cells of its label's
#                          run in none of its rows (`evsOf`).
# Neither reads the computed placement data (PlaceDataX64's cut), which
# Spike/Test/X64PlaceData.lean compares against them. With --check, writes
# under .lake/spike-gen/ instead and fails (exit 1) if the file differs from
# the committed one: the generated data is stale. Run regen_x64.sh for both
# programs first. Spike.Gen.GenOffsX64 is built first (`lake` from `$LAKE`).
set -eu

if [ $# -gt 1 ]; then echo "usage: $0 [--check]" >&2; exit 2; fi
CHECK=0
if [ $# = 1 ]; then
  if [ "$1" = --check ]; then CHECK=1; else echo "usage: $0 [--check]" >&2; exit 2; fi
fi
LAKE=${LAKE:-lake}
cd "$(dirname "$0")/../.."
"$LAKE" build Spike.Gen.GenOffsX64 >/dev/null
T=.lake/spike-gen/offs.x64
mkdir -p "$T"
F=Spike/Test/X64Ret0Offs.lean
printf 'import Spike.Gen.GenOffsX64\n#eval Spike.Gen.OffsX64.writeTo "%s"\n' "$T/offs.lean" > "$T/drv.lean"
rm -f "$T/offs.lean"
"$LAKE" env lean "$T/drv.lean"
[ -f "$T/offs.lean" ] || { echo "GenOffsX64 wrote nothing" >&2; exit 1; }

if [ "$CHECK" = 0 ]; then
  cp "$T/offs.lean" "$F"
  echo "regenerated $F"
else
  if cmp -s "$T/offs.lean" "$F"; then echo "up to date: $F"
  else echo "STALE $F (fresh: $T/offs.lean)"; exit 1; fi
fi
