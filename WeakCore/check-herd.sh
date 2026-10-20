#!/bin/sh
# Validate the model's declared expectations against the official ARM and
# x86-TSO memory models.
#
# This closes the loop that used to be open.  Previously each test was written
# twice -- as `Instr` lists in WeakMem.lean and as assembly here -- with nothing
# forcing the two to describe the same test.  Now:
#
#   WeakMem.lean  --emit-->  litmus/{aarch64,x86_64}/*.litmus  --herd7-->  verdicts
#                 --emit-->  litmus/{aarch64,x86_64}/expected.txt
#                                          |
#                                          +--> compared here
#
# so the assembly herd7 checks is generated from the same `Instr` lists the
# model executes, and `expected.txt` is generated from the same `archAllows` /
# `states` fields the model is tested against.  A disagreement between the model
# and the architecture can no longer hide behind two descriptions that have
# quietly drifted apart.
#
# litmus/{aarch64,x86_64,aarch64-pair,aarch64-wide}/ are GENERATED from
# WeakMem.lean.  Do not hand-edit them; edit the `Litmus` values and re-run this
# script.
#
# litmus/gen/, litmus/gen-x86/ and litmus/aarch64-lse2/ are NOT.  The first two
# came out of `diy7' -- AArch64 and x86-64 respectively -- are checked in as
# source, and `emit' does not touch them.  Their
# expected.txt is herd7's answer rather than the model's claim, so for those two
# groups this script re-derives the oracle rather than validating a prediction.
#
# litmus/aarch64-lse2/ is hand-written rather than diy7-generated, but has the
# same standing: it probes a property of the *model file*
# cats/aarch64-lse2.cat, not of WeakMem.lean, so its expected.txt is likewise
# herd7's answer and this script is what keeps that answer honest.
#
# litmus/aarch64-acq/ is hand-written with herd7's answer as expected.txt, the
# same standing as aarch64-lse2 but under the stock aarch64.cat.
#
# Exits nonzero on any mismatch, so it is usable as a test.
#
# Usage:
#   ./check-herd.sh              # all seven groups
#   ./check-herd.sh aarch64      # just one
#   ./check-herd.sh gen gen-x86  # re-derive the two diy7 oracles

set -e
# Default to a herdtools7 built from github master (see WeakMem.lean's header
# for the revision the verdicts were last checked against); the opam release
# is the fallback.
if [ -z "$HERD" ] && [ -x "$HOME/.local/herd-master/bin/herd7" ]; then
  HERD=$HOME/.local/herd-master/bin/herd7
fi
HERD=${HERD:-$HOME/.opam/default/bin/herd7}
LEAN=${LEAN:-$HOME/.elan/bin/lean}
# Where herd7's bundled .cat files live; our x86 model `include's several.
SHARE=${SHARE:-$(dirname "$HERD")/../share/herdtools7/herd}

if [ ! -x "$HERD" ]; then
  echo "herd7 not found at $HERD; set HERD=/path/to/herd7" >&2
  exit 1
fi

cd "$(dirname "$0")"

# Regenerate, so a stale .litmus file can never be what gets checked.
"$LEAN" --run WeakMem.lean emit litmus

status=0
for a in ${*:-aarch64 x86_64 aarch64-pair aarch64-lse2 aarch64-wide gen gen-x86 aarch64-acq}; do
  # aarch64 uses herd7's bundled model unchanged.  x86 does not: neither
  # x86tso.cat nor x86tso-mixed.cat places `rmw' in its ordering relation, so
  # both admit two concurrent swaps of one location each reading the other's
  # value.  cats/x86tso-mixed-rmw.cat is the bundled mixed model with `rmw'
  # added to `lob', transcribed from aarch64's `aob'; see the header comment
  # there.  -I supplies the bundled files it includes.
  #
  # aarch64-pair needs both a different model and `-variant mixed'.  Stock
  # aarch64.cat decomposes a CASP into independent per-word events and lets a
  # *successful* one partially commit; cats/aarch64-pair.cat adds two axioms
  # that stop it.  `-variant mixed' is not optional -- herd7 rejects a pair
  # access outright without it -- and it must NOT be applied to the plain
  # `aarch64' and `gen' groups, which is the whole reason this is a separate
  # directory.
  #
  # aarch64-lse2 is the same arrangement one step further out.  Both of
  # cats/aarch64-pair.cat's axioms are stated over `range(rmw)', so they say
  # nothing about a plain LDP/STP; cats/aarch64-lse2.cat drops that restriction
  # to model FEAT_LSE2, under which an aligned LDP/STP that does not cross a
  # 16-byte boundary is single-copy atomic.  It likewise needs `-variant mixed'
  # (same reason: pair accesses), and it likewise must not be the model for any
  # other group -- aarch64-pair.cat's header explains at length why it declines
  # to make this change, and that refusal is only meaningful if the two models
  # stay separate files checked against separate directories.
  #
  # `gen' and `gen-x86' run the other way round (as does `aarch64-lse2', for
  # the different reason given above).  The four emitted directories are
  # emitted from WeakMem.lean and their expected.txt is what *the model*
  # claims; herd7 is the thing being asked to agree.  They were produced by
  # diy7, which knows nothing about this model, and their expected.txt is what
  # *herd7* says.  Re-deriving it here is what lets gate item 30 compare the
  # model against a checked-in file in five seconds instead of re-running herd7
  # every time: the file is a cache of this command, and this command is how the
  # cache is invalidated.  A herd7 upgrade that changes a verdict shows up here.
  #
  # `gen-x86' gets the same model as `x86_64', and unlike when this directory
  # was first written that is no longer a free choice.  The eleven `Exch'
  # tests are RMW cycles, so the axiom cats/x86tso-mixed-rmw.cat adds does
  # fire, and it changes the answer: stock x86tso.cat reports 5 states for
  # Exch+rmw-pos where this file reports 3, the two extra being outcomes in
  # which a swap reads from a write that is coherence-after the swap's own.
  # The verdict is Never either way, so a run that compared only verdicts
  # would see nothing.
  case "$a" in
    x86_64|gen-x86) model="-I $SHARE -model $PWD/cats/x86tso-mixed-rmw.cat" ;;
    aarch64-pair)
      model="-I $SHARE -model $PWD/cats/aarch64-pair.cat -variant mixed" ;;
    aarch64-lse2)
      model="-I $SHARE -model $PWD/cats/aarch64-lse2.cat -variant mixed" ;;
    aarch64-wide)
      model="-I $SHARE -model $PWD/cats/aarch64-lse2.cat -variant mixed" ;;
    *)   model="" ;;
  esac

  # shellcheck disable=SC2086
  "$HERD" $model litmus/"$a"/*.litmus 2>&1 |
    awk '/^States [0-9]+$/ { s = $2 }
         /^Observation / { print $2, ($3 == "Never" ? "forbidden" : "allowed"), s }' |
    sort > "/tmp/herd-actual-$a.txt"
  sort "litmus/$a/expected.txt" > "/tmp/herd-expected-$a.txt"

  n=$(wc -l < "/tmp/herd-expected-$a.txt")
  if diff -u "/tmp/herd-expected-$a.txt" "/tmp/herd-actual-$a.txt" \
       > "/tmp/herd-diff-$a.txt"; then
    echo "$a: $n tests agree with herd7 (verdict and state count)"
  else
    echo "$a: MISMATCH between WeakMem.lean and herd7"
    echo "  (- expected by WeakMem.lean, + reported by herd7)"
    sed -n '3,$p' "/tmp/herd-diff-$a.txt" | sed 's/^/  /'
    status=1
  fi
done

exit $status
