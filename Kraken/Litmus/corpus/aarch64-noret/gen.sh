#!/bin/bash
# Regression corpus for herd's `NoRet` atomics: an AArch64 atomic whose value
# read is discarded (destination `XZR`/`WZR`: every `ST<op>`, `LD<op>`/`SWP`
# to `WZR`, `CAS` with comparand `WZR`). herd tags its read `NoRet`: `DMB LD`
# and `DSB LD` do not order it (`[(Exp & R) \ NoRet]` in `aarch64hwreqs.cat`)
# and it loses its acquire; `DMB SY`, `DSB SY` and later release stores still
# order it. Kraken: `vrOldNR` in `Kraken/Promising/Thread.lean`.
#
# Three parts:
# - diycross7 families over `Amo.StAdd`/`StClr`/`StEor`/`StSet` (the only
#   no-result forms diy emits) in LB, MP, S, WRC, R and 2+2W;
# - gen_zr.py: the zero-destination `LD<op>`/`SWP`/`CAS` forms (with `A`,
#   `L`, `AL`), `STADDL`, and register-destination controls, which diy cannot
#   express;
# - the hand-written tests in `hand/` (failing `CAS` with comparand `WZR`),
#   copied in.
# herd7's output on each test is cached as `<test>.litmus.herd` (`Time`/`Hash`
# lines removed).
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

AMO="Amo.StAdd,Amo.StClr,Amo.StEor,Amo.StSet"
# the ST<op>'s read (from another thread), then a barrier, then an access
gen LB   Rfe $AMO DMB.LDdWW,DMB.SYdWW,DSB.LDdWW,DSB.SYdWW,PodWW,PodWWPL Rfe DMB.SYdRW
gen MP   DMB.SYdWW Rfe $AMO DMB.LDdWR,DMB.SYdWR,DSB.LDdWR,DSB.SYdWR,PodWR Fre
gen S    DMB.SYdWW Rfe $AMO DMB.LDdWW,DMB.SYdWW,PodWW,PodWWPL Wse
gen WRC  Rfe $AMO DMB.LDdWW,DMB.SYdWW Rfe DMB.SYdRR Fre
# the ST<op> as the target of an ordering
gen 2+2W DMB.SYdWR $AMO Wse DMB.SYdWW Wse
gen R    DMB.SYdWW Wse DMB.SYdWR $AMO DMB.LDdWR,DMB.SYdWR Fre

python3 "$DST/gen_zr.py" "$DST"
cp "$DST"/hand/*.litmus "$DST"/

n=0
for t in "$DST"/*.litmus; do
  ( cd "$DST" && "$BIN/herd7" "$(basename "$t")" 2>/dev/null || true ) \
    | grep -v '^Time \|^Hash=' > "$t.herd"
  n=$((n+1))
done
echo "aarch64-noret: $n tests"
echo "generated with $("$BIN/herd7" -version)" > "$DST/ORACLE.txt"
