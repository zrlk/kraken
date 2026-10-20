#!/bin/bash
# Regression corpus for the thread-local view rules of Promising-ARM
# (`readSuccs`, `afterWrite`, `writeSuccs`, `fenceStep` in
# `Kraken/Promising/Thread.lean`): which earlier accesses `DMB ST`, `DSB ST`,
# `DMB LD`, `DSB LD` and release stores order before which later ones.
#
# Generated with diycross7 around the rules a read's view update feeds (reads
# raise `vrOld` only, so `DMB ST`/`DSB ST` order no earlier read), plus the
# hand-written tests in this directory (`hand/`, copied in; among them the
# pair-store tests `LB+datapair*`, `LB+pair-tworeads*`, `MP+dmb.st+addr-ldp`,
# `MP+dmb.st+stp-wb`, `MP+dmb.st+wb`: per-access data dependencies of `STP`
# and its write-back, `InstrDeps.dataRegsPer`; and `MP+dmb+addr-{CAS,XCL}-rfi-*`,
# `SB+{CAS,CASA,CASL,CASAL,XCL}-rfi-*`: a plain, `LDAPR` or `LDAR` load reading
# the thread's own RMW or store-exclusive write locally, herd's `aob`
# `[Exp & M]; rmw; lrs; [A | Q]`). herd7's output on
# each test is cached as `<test>.litmus.herd` (`Time`/`Hash` lines removed).
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

ST="DMB.STdRW,DSB.STdRW"
# a read, then DMB ST / DSB ST, then a write: not ordered
gen LB   $ST Rfe PodRW,DMB.STdRW,DSB.STdRW,DpAddrdW,DpDatadW,DpCtrldW,DMB.LDdRW,DSB.LDdRW,PodRWPL Rfe
gen S    DMB.STdWW,DSB.STdWW Rfe PodRW,DMB.STdRW,DSB.STdRW,DpDatadW Wse
gen WRC  Rfe $ST Rfe PodRR,DpAddrdR,DMB.LDdRR Fre
gen ISA2 DMB.STdWW Rfe $ST Rfe DpAddrdR Fre
# DSB ST orders earlier writes before later reads, not earlier reads
gen SB   DSB.STdWR Fre PodWR,DMB.STdWR,DSB.STdWR,DSB.LDdWR,DSB.SYdWR Fre
gen R    DMB.STdWW,DSB.STdWW Wse PodWR,DMB.STdWR,DSB.STdWR,DMB.SYdWR Fre
gen MP   DMB.STdWW,DSB.STdWW Rfe PodRR,DpAddrdR,DMB.LDdRR,DSB.LDdRR,DMB.STdRR,DSB.STdRR Fre
gen 2+2W DMB.STdWW,DSB.STdWW Wse PodWW,DMB.STdWW,DSB.STdWW Wse

cp "$DST"/hand/*.litmus "$DST"/

n=0
for t in "$DST"/*.litmus; do
  ( cd "$DST" && "$BIN/herd7" "$(basename "$t")" 2>/dev/null || true ) \
    | grep -v '^Time \|^Hash=' > "$t.herd"
  n=$((n+1))
done
echo "aarch64-views: $n tests"
echo "generated with $("$BIN/herd7" -version)" > "$DST/ORACLE.txt"
