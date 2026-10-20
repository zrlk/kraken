#!/bin/bash
# Litmus suite for the WeakCore lowering table (`../README.md`, `README.md`
# here): every row of the table, in the combinations lowered programs use,
# on AArch64 (`isaLSE2`) and x64 (TSO).
#
#   core              x64                    AArch64
#   load / load acq   mov / mov              ldr / ldar, ldapr (RCpc)
#   store / store rel mov / mov              str / stlr
#   cas p/acq/rel/ar  lock cmpxchg           cas / casa / casl / casal
#   fence st / full   nothing / mfence       dmb ishst / dmb ish
#   casPair, ldp/stp  cmpxchg16b, movdqa     casp*, LSE2 ldp/stp
#
# Parts:
# - `aarch64/`: diycross7 families (MP, SB, LB, S, R, 2+2W, IRIW, WRC, ISA2
#   over the table's orderings, and CAS as the writer's release or the
#   reader's acquire), then the hand-written tests in `aarch64/hand/`
#   (Treiber push/pop shapes, failing CAS controls, `LDAPR` vs `LDAR`, SB
#   through CAS), copied in. diy has no `DMB ISH`/`DMB ISHST` edges, so the
#   families use `DMB SY`/`DMB ST` and are rewritten to the inner-shareable
#   spellings afterwards (file names `dmb.sy` -> `dmb.ish`, `dmb.st` ->
#   `dmb.ishst`); herd's `aarch64.cat` puts `DMB ISH` in the same full-barrier
#   class as `DMB SY` and `DMB ISHST` with `DMB ST`, and Kraken ignores the
#   shareability domain, so the oracle is computed on the rewritten test.
# - `x64/`: diycross7 families (plain `mov`, `mfence`, `xchg`), then the
#   hand-written tests in `x64/hand/` (`lock cmpxchg`), copied in. Kraken
#   reads AT&T (`lock cmpxchgq %rbx,(x)`); herd 7.58's X86_64 grammar has
#   `cmpxchg` with the memory operand first (`I_CMPXCHG effaddr COMMA reg`,
#   `lib/X86_64Parser.mly`), so herd runs on a twin of each test with the
#   two operands of `cmpxchg` swapped (same semantics: memory destination,
#   register source, comparand in `rax`).
# - Not generated: `aarch64/lse2/` (`.litmus.lse2`, FEAT_LSE2 pairs, which
#   herd does not model) and the vector tests in `x64/` that carry a
#   `.litmus.hand` (`cmpxchg16b`, `movdqa`, which herd 7.58 rejects). Their
#   oracles are hand-argued in `README.md`; this script never touches them.
#
# herd7's output on each test is cached as `<test>.litmus.herd` (`Time` and
# `Hash` lines removed). For `DMB ISH`/`DMB ISHST` herd also prints
# `Flag Assuming-common-inner-shareable-domain` (all threads in one
# inner-shareable domain, which is Kraken's assumption too: it has no
# shareability domains); that line is removed as well, since
# `litmus_tests.py` would read it as a state. Any other flag is kept.
#
# Usage: gen.sh <herdtools7 install/bin dir>
set -euo pipefail
BIN=${1:?herdtools7 bin dir}
TOP=$(cd "$(dirname "$0")" && pwd)

# ---------------------------------------------------------------- AArch64
DST=$TOP/aarch64
gen() {  # <family name> <edge alternatives...>
  ( cd "$DST" && "$BIN/diycross7" -arch AArch64 -name "$@" >/dev/null 2>&1 \
      || echo "diycross7 failed: $*" >&2 )
  rm -f "$DST/@all"
}

WW=PodWWPL,DMB.STdWW,DMB.SYdWW,PodWW          # str;stlr  str;dmb ishst;str  dmb ish  plain
RR=PodRRAP,PodRRQP,DpAddrdR,PodRR             # ldar;ldr  ldapr;ldr  addr dep  plain
WR=PodWRLA,PodWRLQ,DMB.SYdWR,DMB.STdWR,PodWR  # stlr;ldar  stlr;ldapr (RCpc)  dmb ish  dmb ishst  plain
RW=PodRWAP,PodRWQP,PodRWPL,DMB.STdRW,PodRW    # ldar;str  ldapr;str  ldr;stlr  dmb ishst  plain
gen MP   $WW Rfe $RR Fre
gen SB   $WR Fre $WR Fre
gen LB   $RW Rfe $RW Rfe
gen S    PodWWPL,DMB.STdWW,DMB.SYdWW Rfe PodRWAP,PodRWQP,DpDatadW,PodRW Wse
gen R    PodWWPL,DMB.STdWW,DMB.SYdWW Wse PodWRLA,PodWRLQ,DMB.SYdWR,DMB.STdWR Fre
gen 2+2W PodWWPL,DMB.STdWW,DMB.SYdWW Wse PodWWPL,DMB.STdWW,DMB.SYdWW Wse
gen IRIW Rfe PodRRAP,PodRRQP,DMB.SYdRR,PodRR Fre Rfe PodRRAP,PodRRQP,DMB.SYdRR,PodRR Fre
gen WRC  Rfe PodRWPL,PodRWQP,DpDatadW Rfe PodRRAP,PodRRQP,DpAddrdR Fre
gen ISA2 PodWWPL,DMB.STdWW Rfe PodRWQL,PodRWAL Rfe PodRRQP,PodRRAP,DpAddrdR Fre
# CAS as the writer's release (`MPcw`: str; cas/casl/casal) and as the
# reader's acquire (`MPcr`: cas/casa/casal; ldr). diy cannot put a CAS's read
# at the end of an `Fre`, so SB through CAS is in `hand/`.
gen MPcw PodWR Amo.CasPL,Amo.CasAL,Amo.Cas Rfe PodRRAP,PodRRQP,DpAddrdR,PodRR Fre
gen MPcr PodWWPL,DMB.STdWW Rfe Amo.CasAP,Amo.CasAL,Amo.Cas PodWR Fre

# inner-shareable barrier spellings (see above)
for t in "$DST"/*.litmus; do
  n=$(basename "$t")
  m=$(printf '%s' "$n" | sed 's/dmb\.sy/dmb.ish/g; s/dmb\.st/dmb.ishst/g')
  sed -i "s/DMB SY\b/DMB ISH/g; s/DMB ST\b/DMB ISHST/g; 1s/dmb\.sy/dmb.ish/g; 1s/dmb\.st/dmb.ishst/g" "$t"
  if [ "$n" != "$m" ]; then mv "$t" "$DST/$m"; fi
done

cp "$DST"/hand/*.litmus "$DST"/

n=0
for t in "$DST"/*.litmus; do
  ( cd "$DST" && "$BIN/herd7" "$(basename "$t")" 2>/dev/null || true ) \
    | sed '/^Time /d; /^Hash=/d; /^Flag Assuming-common-inner-shareable-domain$/d' > "$t.herd"
  n=$((n+1))
done
echo "lowering/aarch64: $n tests"

# -------------------------------------------------------------------- x64
DST=$TOP/x64
genx() {
  ( cd "$DST" && "$BIN/diycross7" -arch X86_64 -name "$@" >/dev/null 2>&1 \
      || echo "diycross7 failed: $*" >&2 )
  rm -f "$DST/@all"
}
# `fence st` lowers to nothing: TSO keeps W->W, R->R, R->W in order;
# `fence full` is `mfence`, the only W->R order; `xchg` (diy's `A` write) and
# `lock cmpxchg` (hand/) are locked, hence full fences too.
genx MP   PodWW Rfe PodRR Fre
genx SB   PodWR,MFencedWR,PodWRAP Fre PodWR,MFencedWR,PodWRAP Fre
genx LB   PodRW Rfe PodRW Rfe
genx S    PodWW Rfe PodRW Wse
genx R    PodWW Wse PodWR,MFencedWR,PodWRAP Fre
genx 2+2W PodWW Wse PodWW Wse
genx IRIW Rfe PodRR Fre Rfe PodRR Fre
genx WRC  Rfe PodRW Rfe PodRR Fre
genx ISA2 PodWW Rfe PodRW Rfe PodRR Fre
genx RWC  Rfe PodRR Fre PodWR,MFencedWR Fre

cp "$DST"/hand/*.litmus "$DST"/
# out of the regression run (see open/README.md): herd's x86tso-mixed allows a
# state that breaks the atomicity of xchg, which Kraken and the SDM forbid
mkdir -p "$DST/open"
for t in R+po+poana; do mv "$DST/$t.litmus" "$DST/open/"; done

TWIN=$(mktemp -d)
trap 'rm -rf "$TWIN"' EXIT
n=0
for t in "$DST"/*.litmus "$DST"/open/*.litmus; do
  [ -e "$t.hand" ] && continue
  b=$(basename "$t")
  sed 's/\(cmpxchg[bwlq]\{0,1\}\)  *\(%[a-z0-9]*\) *, *\(([^)]*)\)/\1 \3,\2/g' "$t" > "$TWIN/$b"
  ( cd "$TWIN" && "$BIN/herd7" "$b" 2>/dev/null || true ) \
    | sed '/^Time /d; /^Hash=/d' > "$t.herd"
  n=$((n+1))
done
echo "lowering/x64: $n tests with a herd oracle"
echo "generated with $("$BIN/herd7" -version)" > "$TOP/ORACLE.txt"
