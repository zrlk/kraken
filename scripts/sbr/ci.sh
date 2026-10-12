#!/bin/bash
# Checks the ff_aac_sbr_apply proof (see README.md). Sequential by default: one lean process
# at a time. With SBR_JOBS>1 the build step runs up to SBR_JOBS module builds at once, within
# SBR_MEM_BUDGET_GB (default 24) of recorded peaks (pbuild.py, baseline/build_peaks.txt).
# Runs every step; exits 1 if any step failed.
#   1. build       per-module `lake build`, scanned for errors and `sorry`
#   2. axioms      `#print axioms` (Ax.lean) equals baseline/axioms.txt
#   3. tv          tv/tv.sh: translation validation against the objects, data, row-crossing
#                  discipline, mutation test of the checker
#   3b. a2         tv/a2_discipline.py (row-crossing discipline) on its own
#   4. heartbeats  hbscan.py against baseline/hb_table.txt and baseline/hb_baseline.txt
#   5. srcscan     srcscan.py against baseline/srcscan_baseline.txt, and which baseline
#                  files are imported by Link/Witness/Linked (closure.py)
#   5a. regen      apply/ and hfasm/check_regen.sh: the generators reproduce the checked-in files
#   5b. tcb        Tcb.lean: the trusted closure of the linked theorem (what a reviewer
#                  reads); its fingerprint equals baseline/tcb_fingerprint.txt
#   6. real        OPTIONAL, only with SBR_REAL=1: real/check.sh, the proofs about a real
#                  linked binary (SBR_BIN) and their check against it
# Env: SBR_OBJ_DIR (required), LLVM_BIN, SBR_OUT, SBR_CAP_CMD, SBR_SKIP_BUILD=1,
#      SBR_JOBS, SBR_MEM_BUDGET_GB, SBR_MEM_RESERVE_GB (see pbuild.py),
#      SBR_REAL=1 with SBR_BIN (optional step 6).
set -u
. "$(dirname "${BASH_SOURCE[0]}")/common.sh"
OUT=$SBR_OUT/ci
rm -rf "$OUT"; mkdir -p "$OUT"
P=Kraken.X64.Examples.Sbr
declare -A RES
fail=0
mark() { RES[$1]=$2; [ "$2" = ok ] || fail=1; }
cap_note
if [ -z "${SBR_OBJ_DIR:-}" ]; then
  echo "ci: SBR_OBJ_DIR is not set: point it at the directory holding aacsbr.rela.o," \
       "aacsbr.pic.o, aacsbr.g.o, sbrdsp.o and float_dsp.o (see scripts/sbr/README.md)"; exit 2
fi

# ---- 1. build (dependency order; each module on its own)
MODS="Spec DequantFloat
 Dsp.NegOdd64 Dsp.Sum64x5 Dsp.SumSquare Dsp.QmfPreShuffle Dsp.QmfPostShuffle Dsp.QmfDeintNeg
 Dsp.QmfDeintBfly Dsp.Autocorrelate Dsp.HfGen Dsp.HfGFilt Dsp.HfApplyNoise Dsp
 Dsp.FloatDspCommon Dsp.VectorFmul Dsp.VectorFmulAdd Dsp.VectorFmulRev FloatDsp
 LfGen HfInverseFilter XGen QmfSynthesis
 HfAssemble.Cells HfAssemble.Base HfAssemble.Part1 HfAssemble.Part2 HfAssemble
 ApplySpec ApplyTable
 Apply.Trap Apply.EntrySyn Apply.DqCpl Apply.DqSce Apply.AnaHf Apply.EnvALem Apply.EnvA1
 Apply.EnvA2 Apply.EnvA3 Apply.EnvBLem Apply.EnvB1 Apply.EnvB2 Apply.EnvB3 Apply.MapALem
 Apply.MapA1 Apply.MapA2 Apply.MapA3 Apply.MapA4 Apply.MapA5 Apply.MapBLem Apply.MapB1
 Apply.MapB2 Apply.MapB3 Apply.MapB4 Apply.MapB5 Apply.MapB6 Apply.MapB7 Apply.MapB8
 Apply.MapB9 Apply.MapB10 Apply.MapB11 Apply.MapB12 Apply.MapB13 Apply.GainAsm Apply
 Link Witness Placement Linked"
# tv/Export.lean imports Kraken.X64.PrintIntel (tv/Fresh.lean checks its olean), which no
# module in MODS imports: build it first, alone, so it never races with the module builds
tvlib=ok
if [ "${SBR_SKIP_BUILD:-0}" != 1 ]; then
  "${CAP[@]}" lake build Kraken.X64.PrintIntel > "$OUT/build_tvlib.txt" 2>&1 || tvlib=FAIL
  echo "Kraken.X64.PrintIntel (tv) build: $tvlib"
fi
if [ "${SBR_SKIP_BUILD:-0}" != 1 ] && [ "${SBR_JOBS:-1}" -gt 1 ]; then
  # memory-aware parallel build (pbuild.py): same per-module logs, caps and scans
  python3 "$SBR_DIR/pbuild.py" "$OUT" "$P" $MODS > "$OUT/build_sched.log" 2>&1
  rc=$?
  cat "$OUT/build.txt" 2>/dev/null; tail -1 "$OUT/build_sched.log"
  [ $rc = 0 ] && [ $tvlib = ok ] && mark build ok || mark build FAIL
elif [ "${SBR_SKIP_BUILD:-0}" != 1 ]; then
  bfail=0
  : > "$OUT/build.txt"
  for m in $MODS; do
    L=$OUT/build_$m.txt
    TIMER=(); [ -x /usr/bin/time ] && TIMER=(/usr/bin/time -f "%e s %M KB" -o "$L.time")
    "${TIMER[@]}" "${CAP[@]}" lake build "$P.$m" > "$L" 2>&1
    rc=$?
    e=$(grep -c '^error' "$L"); s=$(grep -cE 'declaration uses .sorry.' "$L")
    echo "$m rc=$rc $(tail -1 "$L.time" 2>/dev/null) errors=$e sorry=$s" >> "$OUT/build.txt"
    { [ $rc -ne 0 ] || [ "$e" -ne 0 ] || [ "$s" -ne 0 ]; } && bfail=1
  done
  cat "$OUT/build.txt"
  [ $bfail = 0 ] && [ $tvlib = ok ] && mark build ok || mark build FAIL
else
  RES[build]=skipped
fi

# ---- 2. axioms
"${CAP[@]}" lake env lean "$SBR_DIR/Ax.lean" > "$OUT/axioms.txt" 2>&1
rc=$?
cat "$OUT/axioms.txt"
if [ $rc = 0 ] && diff "$SBR_DIR/baseline/axioms.txt" "$OUT/axioms.txt" > "$OUT/axioms.diff"; then
  echo "axioms: output equals baseline/axioms.txt ($(wc -l < "$OUT/axioms.txt") theorems)"
  mark axioms ok
else
  echo "axioms: differs from baseline/axioms.txt (rc=$rc):"; cat "$OUT/axioms.diff"
  mark axioms FAIL
fi

# ---- 3. tv
bash "$SBR_DIR/tv/tv.sh" > "$OUT/tv.txt" 2>&1; rc=$?
grep -E '^(objects|oleans|programs|data checks|ok a2|FAIL|mutation|tv:)|FINDING|LINK' "$OUT/tv.txt"
[ $rc = 0 ] && mark tv ok || mark tv FAIL

# ---- 3b. row-crossing discipline (also part of tv.sh; listed on its own)
python3 "$SBR_DIR/tv/a2_discipline.py" > "$OUT/a2.txt" 2>&1; rc=$?
cat "$OUT/a2.txt"
[ $rc = 0 ] && mark a2 ok || mark a2 FAIL

# ---- 4. heartbeats
python3 "$SBR_DIR/hbscan.py" > "$OUT/hbscan.txt" 2>&1; rc=$?
cat "$OUT/hbscan.txt"
[ $rc = 0 ] && mark heartbeats ok || mark heartbeats FAIL

# ---- 5. source scan
python3 "$SBR_DIR/srcscan.py" > "$OUT/srcscan.txt" 2>&1; rc=$?
python3 "$SBR_DIR/closure.py" $P.Link $P.Witness $P.Linked >> "$OUT/srcscan.txt" 2>&1
cat "$OUT/srcscan.txt"
[ $rc = 0 ] && mark srcscan ok || mark srcscan FAIL

# ---- 5a. the Apply and HfAssemble generators reproduce the checked-in files (no Lean)
bash "$SBR_DIR/apply/check_regen.sh" > "$OUT/regen.txt" 2>&1; rc=$?
bash "$SBR_DIR/hfasm/check_regen.sh" >> "$OUT/regen.txt" 2>&1; rc2=$?
cat "$OUT/regen.txt"
[ $rc = 0 ] && [ $rc2 = 0 ] && mark regen ok || mark regen FAIL

# ---- 5b. trusted closure: changes exactly when the meaning of the statement can change
"${CAP[@]}" lake env lean "$SBR_DIR/Tcb.lean" > "$OUT/tcb.txt" 2>&1; rc=$?
tail -2 "$OUT/tcb.txt"
fpn=$(sed -n 's/^FINGERPRINT //p' "$OUT/tcb.txt"); fpb=$(cat "$SBR_DIR/baseline/tcb_fingerprint.txt" 2>/dev/null)
if [ $rc = 0 ] && [ -n "$fpn" ] && [ "$fpn" = "$fpb" ]; then
  echo "tcb: fingerprint equals baseline/tcb_fingerprint.txt"; mark tcb ok
else
  echo "tcb: fingerprint $fpn differs from baseline/tcb_fingerprint.txt ($fpb), rc=$rc: the statement's"
  echo "     specification, machine model or a program text changed; review it, then re-record"
  mark tcb FAIL
fi

# ---- 6. real (optional)
STEPS="build axioms tv a2 heartbeats srcscan regen tcb"
if [ "${SBR_REAL:-0}" = 1 ]; then
  bash "$SBR_DIR/real/check.sh" > "$OUT/real.txt" 2>&1; rc=$?
  cat "$OUT/real.txt"
  [ $rc = 0 ] && mark real ok || mark real FAIL
  STEPS="$STEPS real"
fi

echo
echo "== CI summary"
for k in $STEPS; do printf "%-11s %s\n" "$k" "${RES[$k]:-?}"; done
echo "ci: exit $fail"
exit $fail
