#!/bin/bash
# tools/premises/guard.sh -- gate hook: fail if the MEANING of any final's premises or conclusion
# changed (the transitive definition closure of each final's statement; see CheckPremises.lean).
# usage: WM_BUILD=<olean dir> [WM_LEAN=<lean>] tools/premises/guard.sh
# Approve a change (after the design-decision entry exists in the decisions log):
#   WM_APPROVE_PREMISES="<entry, e.g. a decision label>" ... guard.sh
# Exit codes: 0 meaning unchanged; 1 PREMISE MEANING CHANGED (a text moved, or "structural": a final, language
# root or forced constant is missing or renders without its text, or a recursive definition has no unfolding
# equation; also: no frozen baseline yet and no baseline approval); 2 GUARD ERROR (the check did not complete;
# a meaning change cannot be excluded).
# (per-toolchain sets; the label covers the module layout too) Frozen sets by toolchain AND module layout:
# `sets/toolchains.txt` maps the FULL `lean --version`
# line plus the layout of the run ("source": modules named `<M>`; "vendored": modules named `WeakCore.<M>`;
# CheckPremises writes it to premises.out/.layout) to a set dir ("." = `premises.md5` + `frozen/` here;
# "sets/<name>" = `sets/<name>/{premises.md5,frozen/,crossset.spec}`).  The layout matters because derived
# instances are named differently: the source layout adds a `_<module>` suffix (e.g. `instDecidableEqExpr_termLiveCert`)
# and the vendored layout adds none, so the same roots render with different names in the two layouts (and a
# shorter name can let a wrapped line fit on one line); the toolchain can change the printing as well (e.g. the
# `Decidable` match arms; crossset.py rules).  Every frozen set must equal the
# default set modulo its crossset.spec (crossset.py: rename pairs with identical bodies and exact rendering
# rules; OTHER 0), checked on every run.  Sets are frozen only together, with the default set's toolchain and
# layout, in one approval: WM_APPROVE_SETS_DIR=<dir with <name>/ = a premises.out draft from that set's toolchain
# and layout plus the set's crossset.spec> and WM_EXPECT_SETS="<name>=<texts>:<spec> ..." (<texts> =
# `md5sum *.txt | md5sum` in the draft, i.e. the checksum of that run's `premises.new.md5` list; <spec> =
# `md5sum < crossset.spec`).  The draft's .version and .layout (written by every run) must be the set's line in
# sets/toolchains.txt.  python3 is required on every run once a non-default set is listed.
set -u
# (guard tool fix) tool errors: rc 2, never reported as unchanged or as a meaning change
gerr() { echo "GUARD ERROR: $*"; echo "GUARD ERROR: the premise check did not complete; a premise meaning change cannot be excluded"; exit 2; }
# (M0) strict lang roots: an absent root fails unless listed in lang_absent_ok.txt
export WM_GUARD_STRICT=1
# (per-toolchain sets) the non-default sets listed in sets/toolchains.txt
other_sets() { [ -f sets/toolchains.txt ] && awk -F'\t' '!/^#/ && NF == 3 && $1 != "." { print $1 }' sets/toolchains.txt; }
# (per-toolchain sets) set approval precondition: every non-default set has a draft from its toolchain and layout with the reviewed
# checksum, and equals the new default text modulo its crossset.spec (renames with identical bodies)
sets_approve_pre() {
  local s n d got want tv tl rc
  [ -z "$(other_sets)" ] || command -v python3 > /dev/null || { echo "FAIL: not approved: python3 is required when premise sets are listed"; return 1; }
  for s in $(other_sets); do
    n=$(basename "$s"); d=${WM_APPROVE_SETS_DIR:-}/$n
    if [ -z "${WM_APPROVE_SETS_DIR:-}" ] || [ ! -f "$d/.expected" ]; then
      echo "FAIL: not approved: set $s needs its draft in WM_APPROVE_SETS_DIR/$n (premises.out of a guard run on its toolchain and layout)"; return 1
    fi
    [ "$(cd "$d" && ls *.txt | sort)" = "$(sort "$d/.expected")" ] || { echo "FAIL: not approved: the $n draft's files differ from its .expected"; return 1; }
    # the draft was rendered by the set's toolchain, in the set's layout
    tv=$(awk -F'\t' -v s="$s" '!/^#/ && NF == 3 && $1 == s { print $2 }' sets/toolchains.txt)
    tl=$(awk -F'\t' -v s="$s" '!/^#/ && NF == 3 && $1 == s { print $3 }' sets/toolchains.txt)
    echo "set $n: toolchain ${tv:-<none>}, layout ${tl:-<none>}; draft rendered by $(cat "$d/.version" 2>/dev/null || echo '<no .version>'), layout $(cat "$d/.layout" 2>/dev/null || echo '<no .layout>')"
    [ -f "$d/.version" ] && [ -n "$tv" ] && [ "$(cat "$d/.version")" = "$tv" ] \
      || { echo "FAIL: not approved: the $n draft was not rendered by the toolchain listed for $s (.version)"; return 1; }
    [ -f "$d/.layout" ] && [ -n "$tl" ] && [ "$(cat "$d/.layout")" = "$tl" ] \
      || { echo "FAIL: not approved: the $n draft was not rendered in the layout listed for $s (.layout)"; return 1; }
    [ -f "$d/crossset.spec" ] || { echo "FAIL: not approved: the $n draft has no crossset.spec (put the set's spec next to the draft)"; return 1; }
    got=$(cd "$d" && md5sum *.txt | md5sum | cut -c1-32):$(md5sum < "$d/crossset.spec" | cut -c1-32)
    want=$(printf '%s\n' ${WM_EXPECT_SETS:-} | awk -F= -v n="$n" '$1 == n { print $2 }')
    echo "set $n: expected ${want:-<unset>}, draft $got"
    [ -n "$want" ] && [ "$want" = "$got" ] || { echo "FAIL: not approved: WM_EXPECT_SETS has no matching <texts>:<spec> checksum for $n"; return 1; }
    echo "crossset (approval precondition): new default text -> $n draft ($d/crossset.spec)"
    python3 crossset.py "$OUT" "$d" "$d/crossset.spec"; rc=$?
    case $rc in
      0) ;;
      1) echo "FAIL: not approved: the $n draft is not cross-set equal to the new default text"; return 1 ;;
      *) echo "FAIL: not approved: crossset.py could not check the $n draft (rc $rc)"; return 1 ;;
    esac
  done
}
# freeze every non-default set from its (checked) draft; each frozen set is logged in approvals.log
sets_freeze() {
  local s n d m
  for s in $(other_sets); do
    n=$(basename "$s"); d=$WM_APPROVE_SETS_DIR/$n
    rm -rf "$s/frozen"; mkdir -p "$s/frozen"; cp "$d"/*.txt "$s/frozen/"
    cp "$d/crossset.spec" "$s/crossset.spec"
    (cd "$s/frozen" && md5sum *.txt) > "$s/premises.md5"
    m=$(md5sum < "$s/premises.md5" | cut -c1-32):$(md5sum < "$s/crossset.spec" | cut -c1-32)
    echo "$(date -u +%FT%TZ) SET $s $m ($WM_APPROVE_PREMISES)" >> approvals.log
    echo "froze set $s: $m"
  done
}
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
  sets_approve_pre
}
# (M0) keep the precondition output: every approval attempt -> approvals_detail/<UTC>.txt (also printed)
m0_approve_logged() {
  local det rc
  mkdir -p approvals_detail
  det=approvals_detail/$(date -u +%Y%m%dT%H%M%SZ).txt
  { echo "approval attempt $(date -u +%FT%TZ): ${WM_APPROVE_PREMISES:-<unset>}"
    echo "expected: ${WM_EXPECT_PREMISES:-<unset>} sets: ${WM_EXPECT_SETS:-<unset>}"; ${1:-m0_approve_pre}; } > "$det" 2>&1
  rc=$?
  echo "rc=$rc" >> "$det"
  cat "$det"
  echo "precondition detail: tools/premises/$det"
  return $rc
}
OLEANS=${WM_BUILD:-}
[ -n "$OLEANS" ] || gerr "WM_BUILD (the olean dir) is not set"
[ -d "$OLEANS" ] || gerr "WM_BUILD=$OLEANS is not a directory"
OLEANS=$(cd "$OLEANS" && pwd)
LEAN=${WM_LEAN:-$HOME/.elan/bin/lean}
cd "$(dirname "$0")"
OUT=${OLEANS}/premises.out
rm -rf "$OUT" "$OLEANS/premises.new.md5"
# (per-toolchain sets) the frozen set is selected by the full `lean --version` line (exact match, commit hash included)
# and the layout of the run (premises.out/.layout), after the elaboration; the toolchain is checked here already
SD=.
# the first line of `lean --version`; written to premises.out/.version (a set's draft must come from its toolchain)
V=$("$LEAN" --version 2>/dev/null | head -1)
if [ -f sets/toolchains.txt ]; then
  [ -n "$V" ] || gerr "cannot read the version of $LEAN"
  awk -F'\t' '!/^#/ && NF && !(NF == 3 && ($3 == "source" || $3 == "vendored")) { exit 1 }' sets/toolchains.txt \
    || gerr "sets/toolchains.txt has a line that is not <set dir> TAB <lean --version line> TAB <source|vendored>"
  awk -F'\t' -v v="$V" '!/^#/ && NF == 3 && $2 == v { n++ } END { exit n >= 1 ? 0 : 1 }' sets/toolchains.txt \
    || gerr "this toolchain is not listed in sets/toolchains.txt (for any layout): $V"
  [ -z "$(other_sets)" ] || command -v python3 > /dev/null || gerr "python3 is required when premise sets are listed"
  # every frozen set matches its checksum list and equals the default set modulo its crossset.spec (skipped when
  # no default set is frozen yet: the baseline approval below freezes every set again)
  [ ! -f premises.md5 ] || (cd frozen && md5sum -c --quiet ../premises.md5) > /dev/null 2>&1 || gerr "frozen/ does not match premises.md5"
  [ -f premises.md5 ] && for s in $(other_sets); do
    [ -f "$s/premises.md5" ] || continue
    (cd "$s/frozen" && md5sum -c --quiet ../premises.md5) > /dev/null 2>&1 || gerr "$s/frozen does not match $s/premises.md5"
    CL=$OLEANS/crossset.$(basename "$s").log
    python3 crossset.py frozen "$s/frozen" "$s/crossset.spec" > "$CL" 2>&1; rc=$?
    case $rc in
      0) ;;
      1) tail -8 "$CL"; gerr "the frozen set $s is not cross-set equal to the default set" ;;
      *) tail -8 "$CL"; gerr "crossset.py could not check set $s (rc $rc)" ;;
    esac
    echo "set $s ($(md5sum < "$s/premises.md5" | cut -c1-32)): cross-set equal to the default set ($(tail -1 "$CL"))"
  done
fi
# the input: CheckPremises.lean (this tree) or CheckPremises.lean.txt (the export stores every Lean file as .lean.txt)
if [ -f CheckPremises.lean ] && [ -f CheckPremises.lean.txt ] && ! cmp -s CheckPremises.lean CheckPremises.lean.txt; then
  gerr "both CheckPremises.lean and CheckPremises.lean.txt exist and they differ"
elif [ -f CheckPremises.lean ]; then CP=CheckPremises.lean
elif [ -f CheckPremises.lean.txt ]; then CP=CheckPremises.lean.txt
else gerr "input missing: neither CheckPremises.lean nor CheckPremises.lean.txt is in $(pwd)"; fi
[ -s "$CP" ] || gerr "input $CP is empty"
sed "s|\"premises.out\"|\"$OUT\"|" "$CP" > "$OLEANS/CheckPremises.lean" || gerr "cannot write $OLEANS/CheckPremises.lean"
[ "$(grep -cF "\"$OUT\"" "$OLEANS/CheckPremises.lean")" = 1 ] || gerr "$CP must name the output dir \"premises.out\" exactly once"
LOG=$OLEANS/premises.log
if ! LEAN_PATH=$OLEANS "$LEAN" "$OLEANS/CheckPremises.lean" > "$LOG" 2>&1; then
  tail -20 "$LOG"
  # structural meaning changes: CheckPremises' own errors (a missing final / language root / forced constant, a
  # hidden body (h2), a root rendering empty, a recursive def without its unfolding equation), or an unknown
  # name in the finals list (the ``Name`` literals after the #eval line)
  S=$(grep -m1 -E 'missing final |missing language root |missing forced |premise guard|no unfold equation for ' "$LOG")
  EV=$(grep -n '^#eval CheckPremises.freeze' "$OLEANS/CheckPremises.lean" | head -1 | cut -d: -f1)
  if [ -z "$S" ] && [ -n "$EV" ]; then
    S=$(awk -F: -v ev="$EV" '/: error(\([^)]*\))?: [Uu]nknown (constant|identifier)/ && $2 + 0 >= ev + 0 { print; exit }' "$LOG")
  fi
  if [ -n "$S" ]; then
    echo "PREMISE MEANING CHANGED (structural: $S)"
    echo "FAIL: a final, language root or forced constant is missing or renders without its text, or a recursive definition has no unfolding equation; no premise text was produced (log: $LOG)"
    exit 1
  fi
  gerr "elaboration of $CP failed (log: $LOG)"
fi
[ -d "$OUT" ] || gerr "$CP elaborated but wrote no $OUT"
# completion marker, written last by CheckPremises.freeze: the files of this run, one per line
[ -s "$OUT/.expected" ] || gerr "$CP elaborated but wrote no completion marker $OUT/.expected (the freeze did not finish)"
while IFS= read -r f; do [ -s "$OUT/$f" ] || gerr "$OUT/$f (listed in .expected) is missing or empty"; done < "$OUT/.expected"
X=$(ls "$OUT" | grep '\.txt$' | grep -vxF -f "$OUT/.expected" | head -1)
[ -z "$X" ] || gerr "$OUT/$X is not listed in $OUT/.expected"
( cd "$OUT" && md5sum *.txt ) > "$OLEANS/premises.new.md5" || gerr "md5sum over $OUT failed"
printf '%s\n' "$V" > "$OUT/.version" || gerr "cannot write $OUT/.version"
# (per-toolchain sets) the layout of this run (written by CheckPremises.freeze) and the set of (toolchain, layout)
L=$(cat "$OUT/.layout" 2>/dev/null)
if [ -f sets/toolchains.txt ]; then
  case $L in source|vendored) ;; *) gerr "$CP wrote no valid layout to $OUT/.layout (got: '${L}'; want source or vendored)" ;; esac
  SD=$(awk -F'\t' -v v="$V" -v l="$L" '!/^#/ && NF == 3 && $2 == v && $3 == l { print $1; n++ } END { exit n == 1 ? 0 : 1 }' sets/toolchains.txt) \
    || gerr "this toolchain and layout are not listed exactly once in sets/toolchains.txt: lean '$V', layout '$L'"
  [ "$SD" = . ] || [ -f "$SD/premises.md5" ] || gerr "the premise set $SD for this toolchain and layout is not frozen yet: lean '$V', layout '$L'"
  echo "premise set: $SD ($( [ -f "$SD/premises.md5" ] && md5sum < "$SD/premises.md5" | cut -c1-32 || echo 'no premises.md5'); lean: $V; layout: $L)"
fi
if [ ! -f premises.md5 ]; then
  # (M0) freezing a baseline is a re-freeze: token + expected md5 + bodyloss, logged
  if [ -z "${WM_APPROVE_PREMISES:-}" ] || [ -z "${WM_EXPECT_PREMISES:-}" ]; then
    echo "FAIL: no premises.md5: freezing a baseline needs WM_APPROVE_PREMISES and WM_EXPECT_PREMISES"; exit 1
  fi
  [ "$SD" = . ] || gerr "a baseline is frozen with the default set's toolchain and layout only"
  m0_approve_logged || exit 1
  echo "$(date -u +%FT%TZ) BASELINE $WM_APPROVE_PREMISES" >> approvals.log
  echo "no premises.md5: freezing baseline"; cp "$OLEANS/premises.new.md5" premises.md5
  rm -rf frozen; cp -r "$OUT" frozen; rm -f frozen/.expected frozen/.version frozen/.layout; sets_freeze; exit 0
fi
if diff -q "$SD/premises.md5" "$OLEANS/premises.new.md5" > /dev/null; then
  if [ "$SD" = . ] && [ -n "${WM_APPROVE_PREMISES:-}" ] && [ -n "${WM_APPROVE_SETS_DIR:-}" ]; then
    # (per-toolchain sets) the default text is unchanged; freeze the other sets' drafts (the first freeze of a set, or a re-render)
    m0_approve_logged sets_approve_pre || exit 1
    echo "$(date -u +%FT%TZ) SETS $WM_APPROVE_PREMISES (${WM_EXPECT_SETS:-})" >> approvals.log
    sets_freeze; echo "APPROVED (sets): $WM_APPROVE_PREMISES"; exit 0
  fi
  echo "premises: meaning unchanged ($(wc -l < "$SD/premises.md5") finals/premises; set $SD $(md5sum < "$SD/premises.md5" | cut -c1-32))"; exit 0
fi
echo "PREMISE MEANING CHANGED:"; diff "$SD/premises.md5" "$OLEANS/premises.new.md5" | awk '/^[<>]/{print "  "$0}'
for f in $(diff "$SD/premises.md5" "$OLEANS/premises.new.md5" | awk '/^>/{print $3}'); do
  echo "--- $f"; diff "$SD/frozen/$f" "$OUT/$f" | head -40
done
if [ -n "${WM_APPROVE_PREMISES:-}" ]; then
  [ "$SD" = . ] || { echo "FAIL: not approved: approve with the default set's toolchain and layout (set .), with every other set's draft in WM_APPROVE_SETS_DIR"; exit 1; }
  m0_approve_logged || exit 1
  echo "APPROVED: $WM_APPROVE_PREMISES"
  echo "$(date -u +%FT%TZ) $WM_APPROVE_PREMISES" >> approvals.log
  cp "$OLEANS/premises.new.md5" premises.md5; rm -rf frozen; cp -r "$OUT" frozen; rm -f frozen/.expected frozen/.version frozen/.layout; sets_freeze; exit 0
fi
echo "FAIL: the meaning of a final's premises changed; set WM_APPROVE_PREMISES=<entry> once the user has approved it"
exit 1
