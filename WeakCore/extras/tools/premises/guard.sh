#!/bin/bash
# tools/premises/guard.sh -- gate hook: fail if the MEANING of any final's premises or conclusion
# changed (the transitive definition closure of each final's statement; see CheckPremises.lean).
# usage: WM_BUILD=<olean dir> [WM_LEAN=<lean>] tools/premises/guard.sh
# Approve a change (after the design-decision entry exists in the decisions log):
#   WM_APPROVE_PREMISES="<entry, e.g. a decision label>" ... guard.sh
set -u
# (M0) strict lang roots: an absent root fails unless listed in lang_absent_ok.txt
export WM_GUARD_STRICT=1
# (M0) approval preconditions: bodyloss vs the pre-M0 baseline, and the expected new-set md5
m0_approve_pre() {
  for f in bodyloss.py bodyloss_allow.txt bodyloss_base/premises.md5; do
    if [ ! -f "$f" ]; then echo "FAIL: not approved: tools/premises/$f is missing (approval precondition)"; return 1; fi
  done
  if ! (cd bodyloss_base && md5sum -c --quiet premises.md5); then
    echo "FAIL: not approved: bodyloss_base does not match its premises.md5 (approval precondition)"; return 1
  fi
  echo "bodyloss (approval precondition): bodyloss_base -> new"
  if ! python3 bodyloss.py bodyloss_base "$OUT" bodyloss_allow.txt; then
    echo "FAIL: not approved: the new premise text loses a body or constant (bodyloss)"; return 1
  fi
  local got
  got=$(md5sum < "$OLEANS/premises.new.md5" | cut -c1-32)
  echo "expected premises set md5: ${WM_EXPECT_PREMISES:-<unset>}"
  echo "new      premises set md5: $got"
  if [ "${WM_EXPECT_PREMISES:-}" != "$got" ]; then
    echo "FAIL: not approved: set WM_EXPECT_PREMISES to the reviewed set md5 (it must equal the new one)"; return 1
  fi
}
# (M0) keep the precondition output: every approval attempt -> approvals_detail/<UTC>.txt (also printed)
m0_approve_logged() {
  local det rc
  mkdir -p approvals_detail
  det=approvals_detail/$(date -u +%Y%m%dT%H%M%SZ).txt
  { echo "approval attempt $(date -u +%FT%TZ): ${WM_APPROVE_PREMISES:-<unset>}"
    echo "expected: ${WM_EXPECT_PREMISES:-<unset>}"; m0_approve_pre; } > "$det" 2>&1
  rc=$?
  echo "rc=$rc" >> "$det"
  cat "$det"
  echo "precondition detail: tools/premises/$det"
  return $rc
}
OLEANS=${WM_BUILD:?WM_BUILD olean dir}
LEAN=${WM_LEAN:-$HOME/.elan/bin/lean}
cd "$(dirname "$0")"
OUT=${OLEANS}/premises.out
rm -rf "$OUT"
sed "s|\"premises.out\"|\"$OUT\"|" CheckPremises.lean > "$OLEANS/CheckPremises.lean"
if ! LEAN_PATH=$OLEANS "$LEAN" "$OLEANS/CheckPremises.lean" > "$OLEANS/premises.log" 2>&1; then
  echo "FAIL: CheckPremises.lean did not run"; tail -20 "$OLEANS/premises.log"; exit 1
fi
( cd "$OUT" && md5sum *.txt ) > "$OLEANS/premises.new.md5"
if [ ! -f premises.md5 ]; then
  # (M0) freezing a baseline is a re-freeze: token + expected md5 + bodyloss, logged
  if [ -z "${WM_APPROVE_PREMISES:-}" ] || [ -z "${WM_EXPECT_PREMISES:-}" ]; then
    echo "FAIL: no premises.md5: freezing a baseline needs WM_APPROVE_PREMISES and WM_EXPECT_PREMISES"; exit 1
  fi
  m0_approve_logged || exit 1
  echo "$(date -u +%FT%TZ) BASELINE $WM_APPROVE_PREMISES" >> approvals.log
  echo "no premises.md5: freezing baseline"; cp "$OLEANS/premises.new.md5" premises.md5
  rm -rf frozen; cp -r "$OUT" frozen; exit 0
fi
if diff -q premises.md5 "$OLEANS/premises.new.md5" > /dev/null; then
  echo "premises: meaning unchanged ($(wc -l < premises.md5) finals/premises)"; exit 0
fi
echo "PREMISE MEANING CHANGED:"; diff premises.md5 "$OLEANS/premises.new.md5" | awk '/^[<>]/{print "  "$0}'
for f in $(diff premises.md5 "$OLEANS/premises.new.md5" | awk '/^>/{print $3}'); do
  echo "--- $f"; diff "frozen/$f" "$OUT/$f" | head -40
done
if [ -n "${WM_APPROVE_PREMISES:-}" ]; then
  m0_approve_logged || exit 1
  echo "APPROVED: $WM_APPROVE_PREMISES"
  echo "$(date -u +%FT%TZ) $WM_APPROVE_PREMISES" >> approvals.log
  cp "$OLEANS/premises.new.md5" premises.md5; rm -rf frozen; cp -r "$OUT" frozen; exit 0
fi
echo "FAIL: the meaning of a final's premises changed; set WM_APPROVE_PREMISES=<entry> once the user has approved it"
exit 1
