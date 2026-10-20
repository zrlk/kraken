#!/bin/bash
# Model-fidelity sweep: broad diycross7 families over fences, annotations and
# dependencies, on AArch64 and x86_64, with herd7's output cached per test.
#
# NOT run by litmus_tests.py and not checked in: the tests are generated into
# a scratch directory given on the command line. Each family goes to its own
# subdirectory (`<out>/<isa>/<family>/`), so the mismatches can be read per
# family:
#
#   gen.sh <herdtools7 install/bin dir> <out dir>
#   for d in <out>/aarch64/*/; do python3 Kraken/Litmus/litmus_tests.py "$d"; done
#   for d in <out>/x86_64/*/;  do python3 Kraken/Litmus/litmus_tests.py --isa x64 "$d"; done
#
# A family whose herd run exceeds HERD_TIMEOUT seconds per test keeps the
# test without an oracle (litmus_tests.py then reports it as no-oracle).
set -uo pipefail
BIN=${1:?herdtools7 bin dir}
OUT=${2:?output dir}
HERD_TIMEOUT=${HERD_TIMEOUT:-60}
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

gen() {  # <arch> <family dir> <diycross7 cycle with comma alternatives...>
  local arch=$1 fam=$2; shift 2
  local dir="$OUT/$(echo "$arch" | tr 'A-Z' 'a-z')/$fam"
  mkdir -p "$dir"
  local log
  log=$(cd "$dir" && "$BIN/diycross7" ${DIYOPTS:-} -arch "$arch" -name "$fam" "$@" 2>&1)
  case "$log" in
    *"produced 0 tests"*|*"Fatal"*) echo "diycross7 produced nothing: $arch $fam $*: $log" >&2 ;;
  esac
  rm -f "$dir/@all"
}

# ---- AArch64 ---------------------------------------------------------------
A=AArch64
F="DMB.SY DMB.LD DMB.ST DSB.SY DSB.LD DSB.ST ISB"
fences() { local xy=$1 s=""; for f in $F; do s="$s,${f}d$xy"; done; echo "${s#,}"; }
WW="PodWW,$(fences WW),PodWWPL,PodWWLL,PodWWLP"
WR="PodWR,$(fences WR),PodWRLA,PodWRLQ,PodWRLP,PodWRPA,PodWRPQ"
RW="PodRW,$(fences RW),DpAddrdW,DpDatadW,DpCtrldW,DpCtrlIsbdW,DpAddrCseldW,DpDataCseldW,DpCtrlCseldW,PodRWAP,PodRWQP,PodRWPL,PodRWAL"
RR="PodRR,$(fences RR),DpAddrdR,DpCtrldR,DpCtrlIsbdR,DpAddrCseldR,DpCtrlCseldR,DpCtrlIsbCseldR,PodRRAP,PodRRQP"
# a smaller set for the 3- and 4-thread shapes
RWs="PodRW,DMB.SYdRW,DMB.LDdRW,DMB.STdRW,DSB.STdRW,DpAddrdW,DpDatadW,DpCtrldW,DpDataCseldW,PodRWAP,PodRWPL"
RRs="PodRR,DMB.SYdRR,DMB.LDdRR,DSB.LDdRR,ISBdRR,DpAddrdR,DpCtrldR,DpCtrlIsbdR,DpAddrCseldR,PodRRAP,PodRRQP"
WWs="PodWW,DMB.SYdWW,DMB.STdWW,DSB.STdWW,PodWWPL"
WRs="PodWR,DMB.SYdWR,DMB.STdWR,DSB.STdWR,DSB.LDdWR,PodWRLA,PodWRLQ"
RR3="PodRR,DMB.LDdRR,DpAddrdR,DpCtrlIsbdR,PodRRAP"
RW3="PodRW,DMB.STdRW,DpDatadW,PodRWPL"
AMO="Amo.Swp,Amo.SwpAP,Amo.SwpPL,Amo.SwpAL,Amo.Cas,Amo.CasAL,Amo.LdAdd,Amo.LdAddAL,Amo.StAdd,Amo.StAddPL,LxSx,LxSxAL"

gen $A MP   $WW Rfe $RR Fre
gen $A SB   $WR Fre $WR Fre
gen $A LB   $RW Rfe $RW Rfe
gen $A S    $WW Rfe $RW Wse
gen $A R    $WW Wse $WR Fre
gen $A 2+2W $WW Wse $WW Wse
gen $A WRC  Rfe $RWs Rfe $RRs Fre
gen $A ISA2 $WWs Rfe $RWs Rfe $RR3 Fre
gen $A Z6.0 $WWs Rfe $RWs Wse $WRs Fre
gen $A Z6.1 $WWs Wse $WWs Rfe $RWs Wse
gen $A Z6.2 $WWs Rfe $RWs Rfe $RW3 Wse
gen $A Z6.3 $WWs Wse $WWs Rfe $RRs Fre
gen $A IRIW Rfe $RRs Fre Rfe $RRs Fre
gen $A RWC  Rfe $RRs Fre $WRs Fre
gen $A WWC  Rfe $RWs Wse $WRs Fre
# annotated communication edges
gen $A MP-rfe   $WWs Rfe,RfeLA,RfeLQ,RfePA,RfeLP $RR3 Fre,FreAL,FrePL
gen $A SB-fre   $WRs Fre,FreAL,FreQL $WRs Fre,FreAL
# atomics and exclusives at each position
gen $A MP-amo   DMB.SYdWW,PodWWPL Rfe $AMO PodWR,DMB.SYdWR,DMB.LDdWR,DSB.LDdWR Fre
gen $A LB-amo   Rfe $AMO PodWW,DMB.SYdWW,DMB.LDdWW,DMB.STdWW,PodWWPL Rfe DMB.SYdRW,DpDatadW
gen $A SB-amo   PodWR,DMB.SYdWR $AMO PodWR,DMB.SYdWR,DMB.STdWR,DSB.STdWR Fre PodWR,DMB.SYdWR Fre
gen $A S-amo    DMB.SYdWW Rfe $AMO PodWW,DMB.STdWW,DMB.LDdWW Wse
gen $A 2+2W-amo DMB.SYdWR $AMO Wse PodWW,DMB.SYdWW,DMB.STdWW Wse
# same-location (coherence) families
DIYOPTS=-oneloc gen $A CoRR  Rfe,RfeLA,RfeLQ PosRR,PosRRAP,PosRRAA,PosRRQP,DMB.LDsRR,DpAddrsR,DpCtrlsR Fre
DIYOPTS=-oneloc gen $A CoWW  PosWW,PosWWPL,PosWWLP,DMB.STsWW Rfe PosRR,PosRRAP Fre
DIYOPTS=-oneloc gen $A CoRW1 PosRW,PosRWAP,PosRWPL,DpDatasW,DpAddrsW,DpCtrlsW Wse Rfe
DIYOPTS=-oneloc gen $A CoRW2 Rfe PosRW,PosRWAP,PosRWPL,DpDatasW,DpAddrsW Wse
DIYOPTS=-oneloc gen $A CoWR  PosWR,PosWRLA,PosWRLQ,DMB.SYsWR Fre Wse
gen $A SB+rfi Rfi $RRs Fre Rfi $RRs Fre

# ---- X86_64 ----------------------------------------------------------------
X=X86_64
XWW="PodWWNaNa,MFencedWW,SFencedWW,LFencedWW,PodWWNaA,PodWWANa,PodWWAA,PodWWNTNa,PodWWNaNT"
XWR="PodWRNaNa,MFencedWR,SFencedWR,LFencedWR,PodWRANa,PodWRNTNa"
XRW="PodRWNaNa,MFencedRW,SFencedRW,LFencedRW,PodRWNaA,PodRWNaNT"
XRR="PodRRNaNa,MFencedRR,SFencedRR,LFencedRR"
gen $X MP   $XWW Rfe $XRR Fre
gen $X SB   $XWR Fre $XWR Fre
gen $X LB   $XRW Rfe $XRW Rfe
gen $X S    $XWW Rfe $XRW Wse
gen $X R    $XWW Wse $XWR Fre
gen $X 2+2W $XWW Wse $XWW Wse
gen $X WRC  Rfe $XRW Rfe $XRR Fre
gen $X IRIW Rfe $XRR Fre Rfe $XRR Fre
gen $X RWC  Rfe $XRR Fre $XWR Fre
gen $X ISA2 PodWWNaNa,MFencedWW,PodWWNaA Rfe PodRWNaNa,MFencedRW,PodRWNaA Rfe PodRRNaNa,MFencedRR Fre
gen $X MP-xchg $XWW Rfe Exch $XWR Fre
gen $X SB+rfi Rfi $XRR Fre Rfi $XRR Fre
DIYOPTS=-oneloc gen $X CoRR  Rfe PosRRNaNa Fre

# ---- oracle ----------------------------------------------------------------
for isa in aarch64 x86_64; do
  n=0
  for t in "$OUT"/$isa/*/*.litmus; do
    [ -e "$t" ] || continue
    ( cd "$(dirname "$t")" && timeout "$HERD_TIMEOUT" "$BIN/herd7" "$(basename "$t")" 2>/dev/null || true ) \
      | grep -v '^Time \|^Hash=' > "$t.herd"
    [ -s "$t.herd" ] || rm -f "$t.herd"
    n=$((n+1))
  done
  echo "$isa: $n tests"
done
echo "generated with $("$BIN/herd7" -version)" > "$OUT/ORACLE.txt"
