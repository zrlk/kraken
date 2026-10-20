#!/bin/bash
# Regression corpus for AArch64 pair accesses: `LDXP`/`LDAXP`, `STXP`/`STLXP`,
# `CASP`/`CASPA`/`CASPL`/`CASPAL` (W and X forms), with `LDP`/`STP` and
# single-register controls. Kraken: `toEv`'s pair cases and `caspTree` in
# `Kraken/Promising/AArch64.lean`.
#
# Two parts:
# - diycross7 families over diy's pair annotations `Pa` (`LDP`/`STP` of two
#   `W` registers on an `int[2]` array) in MP, S, LB, 2+2W, SB and R: diy has
#   no edges for exclusive pairs or `CASP`, so these only check that the pair
#   shapes around them stay two independent accesses;
# - the hand-written tests in `hand/` (exclusive pairs on a 16-byte location
#   and on arrays, both orders of `CASP`'s halves for every kind, `CASP`
#   failure, `CAS`/`CASP` fail-with-write-back probes, data dependencies of
#   store exclusives, mixed sizes), copied in.
# herd7's output on each test is cached as `<test>.litmus.herd` (`Time`/`Hash`
# lines removed). Tests that type a location wider than its accesses
# (`__int128` read by `LDXP`, `uint64_t` by a `W` pair) need herd's
# `-variant mixed`, without which herd prints no result.
#
# `lse2/` is not generated: hand-argued `.litmus.lse2` oracles for
# `litmus_tests.py --lse2` (FEAT_LSE2 hardware, which herd does not model).
#
# Usage: gen.sh <herdtools7 install/bin dir>
set -euo pipefail
BIN=${1:?herdtools7 bin dir}
DST=$(cd "$(dirname "$0")" && pwd)

gen() {  # <family name> <edge alternatives...>
  ( cd "$DST" && "$BIN/diycross7" -arch AArch64 -name "$@" >/dev/null 2>&1 \
      || echo "diycross7 failed: $*" >&2 )
  rm -f "$DST/@all"
}

# a pair store as the writer, a pair load as the reader
gen MPpa  DMB.SYdWWPPa,DMB.STdWWPPa,PodWWPPa RfePaP DMB.SYdRR,DMB.LDdRR,PodRR Fre
gen MPpb  DMB.SYdWW Rfe DMB.SYdRRPPa,DMB.LDdRRPPa,PodRRPPa FrePaP
gen Spa   DMB.SYdWWPPa,PodWWPPa RfePaP DMB.SYdRW,PodRW Wse
gen LBpa  DMB.SYdRWPPa,PodRWPPa RfePaP DMB.SYdRW,PodRW Rfe
gen 2+2Wpa DMB.SYdWWPPa,PodWWPPa WsePaP DMB.SYdWW Wse
gen SBpa  DMB.SYdWRPPa,PodWRPPa FrePaP DMB.SYdWR Fre
gen Rpa   DMB.SYdWWPPa,PodWWPPa WsePaP DMB.SYdWR Fre

cp "$DST"/hand/*.litmus "$DST"/

n=0
for t in "$DST"/*.litmus; do
  v=()
  if grep -q '__int128\|int64_t' "$t"; then v=(-variant mixed); fi
  ( cd "$DST" && "$BIN/herd7" "${v[@]}" "$(basename "$t")" 2>/dev/null || true ) \
    | grep -v '^Time \|^Hash=' > "$t.herd"
  n=$((n+1))
done
echo "aarch64-pairs: $n tests"
echo "generated with $("$BIN/herd7" -version)" > "$DST/ORACLE.txt"
