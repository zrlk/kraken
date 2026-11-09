#!/usr/bin/env bash
# Regenerate Spike/Test/A64Ret0Offs.lean (ret0.w's and hello1.w's AArch64
# block offsets and single instructions) from the committed scc --code data,
# or check that the committed file is what a fresh regeneration writes; the
# AArch64 counterpart of regen_offs_x64.sh.
#
# Usage: Spike/Gen/regen_offs_a64.sh [--check]
#
# Reads Spike/Lib/A64Ret0Code.lean and Spike/Lib/A64Hello1Code.lean
# (regen_a64.sh's output: the listing, its program and scc --code's block
# table); writes Spike/Gen/GenOffsA64.lean's `render`:
#   ret0Offs, hello1Offs   Scc.Cert.Blocks.offsA64's analysis of the listing;
#   ret0Evs, hello1Evs     per group of the table, the instructions of its
#                          label's run in none of its rows (`evsOf`).
# Neither reads the computed placement data (PlaceDataA64's cut), which
# Spike/Test/A64PlaceData.lean compares against them. With --check, writes
# under .lake/spike-gen/ instead and fails (exit 1) if the file differs from
# the committed one: the generated data is stale. Run regen_a64.sh for both
# programs first. Spike.Gen.GenOffsA64 is built first (`lake` from `$LAKE`).
set -eu

if [ $# -gt 1 ]; then echo "usage: $0 [--check]" >&2; exit 2; fi
CHECK=0
if [ $# = 1 ]; then
  if [ "$1" = --check ]; then CHECK=1; else echo "usage: $0 [--check]" >&2; exit 2; fi
fi
LAKE=${LAKE:-lake}
cd "$(dirname "$0")/../.."
"$LAKE" build Spike.Gen.GenOffsA64 >/dev/null
T=.lake/spike-gen/offs.a64
mkdir -p "$T"
F=Spike/Test/A64Ret0Offs.lean
printf 'import Spike.Gen.GenOffsA64\n#eval Spike.Gen.OffsA64.writeTo "%s"\n' "$T/offs.lean" > "$T/drv.lean"
rm -f "$T/offs.lean"
"$LAKE" env lean "$T/drv.lean"
[ -f "$T/offs.lean" ] || { echo "GenOffsA64 wrote nothing" >&2; exit 1; }

if [ "$CHECK" = 0 ]; then
  cp "$T/offs.lean" "$F"
  echo "regenerated $F"
else
  if cmp -s "$T/offs.lean" "$F"; then echo "up to date: $F"
  else echo "STALE $F (fresh: $T/offs.lean)"; exit 1; fi
fi
