#!/bin/bash
# Generate litmus families with diycross7 and cache herd7's output on each.
#
# Usage: gen.sh <herdtools7 install/bin dir>
#
# Each family is a cycle shape with alternatives at the per-thread edges
# (po, barriers, dependencies, release/acquire annotations); diycross7 emits
# the cross product. The herd7 oracle output is stored as <test>.litmus.herd.
set -euo pipefail
BIN=${1:?herdtools7 bin dir}
DST=$(cd "$(dirname "$0")" && pwd)

gen() {  # <arch> <family name> <edge alternatives...>
  local arch=$1 name=$2; shift 2
  local dir="$DST/$(echo "$arch" | tr 'A-Z' 'a-z')"
  mkdir -p "$dir"
  ( cd "$dir" && "$BIN/diycross7" -arch "$arch" -name "$name" "$@" >/dev/null 2>&1 \
      || echo "diycross7 failed: $arch $name $*" >&2 )
}

# ---- AArch64 ---------------------------------------------------------------
A=AArch64
WW="PodWW,DMB.SYdWW,DMB.STdWW,DMB.LDdWW,PodWWPL"
RR="PodRR,DMB.SYdRR,DMB.LDdRR,DMB.STdRR,DpAddrdR,DpCtrldR,DpCtrlIsbdR,PodRRAP,PodRRQP"
WR="PodWR,DMB.SYdWR,DMB.LDdWR,DMB.STdWR,PodWRLP,PodWRLA,PodWRLQ,PodWRPA"
RW="PodRW,DMB.SYdRW,DMB.LDdRW,DpAddrdW,DpDatadW,DpCtrldW,PodRWAP,PodRWPL,PodRWAL"
gen $A MP   $WW Rfe $RR Fre
gen $A SB   $WR Fre $WR Fre
gen $A LB   $RW Rfe $RW Rfe
gen $A S    $WW Rfe $RW Wse
gen $A R    $WW Wse $WR Fre
gen $A 2+2W $WW Wse $WW Wse
gen $A WRC  Rfe PodRW,DpAddrdW,DpDatadW,DMB.SYdRW,PodRWAP Rfe PodRR,DpAddrdR,DMB.SYdRR,PodRRAP Fre
gen $A IRIW Rfe PodRR,DMB.SYdRR,DpAddrdR,PodRRAP Fre Rfe PodRR,DMB.SYdRR,DpAddrdR,PodRRAP Fre
gen $A RWC  Rfe PodRR,DMB.SYdRR,DpAddrdR Fre PodWR,DMB.SYdWR Fre
gen $A WWC  Rfe PodRW,DpDatadW,DMB.SYdRW Wse PodWR,DMB.SYdWR Fre
gen $A ISA2 PodWW,DMB.SYdWW,PodWWPL Rfe PodRW,DpDatadW,PodRWAP Rfe PodRR,DpAddrdR,PodRRAP Fre
gen $A Z6.3 PodWW,DMB.SYdWW Wse PodWR,DMB.SYdWR Fre PodRW,DpAddrdW Rfe
# same-location and forwarding shapes
gen $A MP+rfi  PodWW,DMB.SYdWW Rfe Rfi PodRR,DpAddrdR,DMB.SYdRR Fre
gen $A SB+rfi  Rfi PodRR,DMB.SYdRR,DpAddrdR Fre Rfi PodRR,DMB.SYdRR,DpAddrdR Fre
gen $A CoRR   Rfe PosRR Fre
gen $A CoWR   PosWR Fre
gen $A LB+rel+ctrl PodRWPL,DpCtrldW Rfe PodRWPL,DpCtrldW Rfe

# ---- X86_64 ----------------------------------------------------------------
X=X86_64
gen $X MP   PodWW,MFencedWW Rfe PodRR,MFencedRR Fre
gen $X SB   PodWR,MFencedWR Fre PodWR,MFencedWR Fre
gen $X LB   PodRW,MFencedRW Rfe PodRW,MFencedRW Rfe
gen $X S    PodWW,MFencedWW Rfe PodRW,MFencedRW Wse
gen $X R    PodWW,MFencedWW Wse PodWR,MFencedWR Fre
gen $X 2+2W PodWW,MFencedWW Wse PodWW,MFencedWW Wse
gen $X WRC  Rfe PodRW,MFencedRW Rfe PodRR,MFencedRR Fre
gen $X IRIW Rfe PodRR,MFencedRR Fre Rfe PodRR,MFencedRR Fre
gen $X RWC  Rfe PodRR,MFencedRR Fre PodWR,MFencedWR Fre
gen $X WWC  Rfe PodRW,MFencedRW Wse PodWR,MFencedWR Fre
gen $X SB+rfi Rfi PodRR,MFencedRR Fre Rfi PodRR,MFencedRR Fre
gen $X MP+rfi PodWW,MFencedWW Rfe Rfi PodRR,MFencedRR Fre
gen $X CoRR  Rfe PosRR Fre

# ---- oracle ----------------------------------------------------------------
for dir in "$DST"/aarch64 "$DST"/x86_64; do
  n=0
  for t in "$dir"/*.litmus; do
    ( cd "$dir" && "$BIN/herd7" "$(basename "$t")" 2>/dev/null || true ) \
      | grep -v '^Time \|^Hash=' > "$t.herd"
    n=$((n+1))
  done
  echo "$(basename "$dir"): $n tests"
done
echo "generated with $("$BIN/herd7" -version)" > "$DST/ORACLE.txt"
