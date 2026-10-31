#!/bin/sh
# Build and run the promise machine (Stage 2, take two).
#
# Also builds Tutorial.lean and CoreLang.lean, which check themselves; those
# are not numbered items below, and are explained where they run.
#
# Checks the numbered items listed below, and exits nonzero if any of them
# regress.  The count is deliberately not written here: item 28 computes it,
# and a number written down is a number that goes stale.
# Almost every one is a *control* rather than a test: it runs the same program
# under the same oracle with one thing removed, and requires that it break.
#
#  1. All 40 litmus tests agree with herd7 under in-order issue + promises,
#     AND reach the same *set* of final states as WeakMem.lean's machine.  The
#     state-set check is the strong one: it says promises are a faithful
#     replacement for out-of-order issue, not merely one that happens to get
#     the target outcome right.
#  2. Every new rule is load-bearing -- the ablation table must show a nonzero
#     failure count for each row.  A rule that ablates to zero failures is
#     unjustified and should be deleted, not kept for comfort.
#  3. The file compiles, which includes `load_reads_own_write` -- the `mvcgen`
#     proof of read-own-write coherence over the `do`-notation front-end.
#  4. Remote is not inert.  Every §7 privacy theorem is satisfied by an
#     environment that does nothing, so the two scenarios must disagree.
#  5. Publication is not vacuous.  §8 proves the fenced reader cannot see a
#     stale value; the unfenced reader must still be able to, or the fence is
#     not what is doing the work.
#  6. Ownership is not inert.  §9's `rdisowned` guard could have disabled the
#     whole environment, which would satisfy `owned_load_reads_own_write`
#     vacuously; the *unowned* run must still be clobbered by Remote.
#  7. Publication and ownership actually compose.  §9.1 proves a receiver's
#     *second* read of a transferred object still returns the published value;
#     removing only the ownership declaration must break it, or coherence was
#     doing all the work and the theorem is §8 restated.
#  8. `undef` is a value and not a fault (D1), on both sides.  An
#     allocated-but-unwritten cell must read as `undef` *without* getting stuck,
#     and a load outside every allocation must still get stuck.  Collapsing the
#     two in either direction silently removes the distinction §10 exists to
#     make.  A store outside every allocation must be flagged too -- and must
#     still be *recorded*, because the store rule has no branch on which nothing
#     happens.  Reading that cell back must stay stuck, which holds only because
#     `stuck` is sticky; that composition is the easiest of these to break.
#  9. Neither of the copy loop's claims is vacuous.  For privacy: §10 proves a
#     freshly allocated buffer stays unreachable across the whole copy, so the
#     same copy into a *published* buffer, under the same oracle, must get
#     clobbered.  For correctness: an uninterfered copy must be a word-for-word
#     duplicate, because `copy_is_exact` is a safety property and a copy that
#     wrote nothing would satisfy it.  And clobbering the *source* after a cell
#     has been read must leave the buffer unchanged but the source cell
#     two-valued -- the first is `copy_copies_something` surviving interference,
#     the second is the frozen-source hypothesis failing, which is the only
#     reason `copy_is_exact` has an antecedent.
# 10. Atomicity restricts something.  §11's CAS must refuse a stale read that a
#     plain load, on the same memory and the same oracle, is allowed to take --
#     and the plain load must still take it, or the control is vacuous.
# 11. The derived lock excludes, and not by doing nothing.  §11.1 proves that a
#     held lock cannot be acquired by the environment; the *free* lock must
#     still be acquirable by it, and acquirable only once.
# 12. The lock protects the *data*, and the protection comes from winning the
#     CAS rather than from `rdisowned`.  §11.2 proves it; the control differs by
#     one instruction -- local reads the lock instead of taking it -- and must
#     show the data being clobbered.
# 13. The seqlock detects.  §11.3 has no exclusion at all, so the property is
#     that the reader *notices*.  Both fences must be load-bearing: dropping
#     the reader's `dmb ishld` must let it accept a pre-transaction counter
#     while holding mid-transaction data, dropping the writer's `dmb ishst`
#     must do the same by a different route (the data word carries no view),
#     and putting both back must stop it.
# 14. TSO stays inside ARM, which is what lets an `arm` proof be a claim about
#     x86.  Every one of the 40 shapes is run under both rule sets and no
#     outcome may be reachable under `tso` but not under `arm`.  The same table
#     guards against the check being vacuous: ARM must be strictly weaker
#     somewhere, or the two rule sets agree everywhere tested and containment
#     is free.
# 15. The address dependency does the reader's ordering, and a reader barrier
#     does not.  §12 runs the same 3-link traversal four times.  With the
#     writer's `dmb ishst` and no reader barrier it must reach the payload;
#     without it, it must stall on `undef` at the first node.  Adding a
#     `dmb ishld` before every load must change *neither* row -- it must not
#     rescue the unfenced writer, and it must be redundant when the writer
#     fenced.  Those last two are the whole "cheaper than dmb" claim, and each
#     is a separate way for the section to become a lie.
# 16. The capacity/length split is real, and the bounds check bites.  §13's
#     growable array reads three regimes off one run: inside the length gives
#     the pushed value (so the data survived two reallocations), inside the
#     capacity gives a clean `undef` (which is the whole point of the split,
#     and which §6.8's allocation rule could not express), and past the
#     capacity is stuck.  The control is the same push loop with the growth
#     test deleted; it must overrun and get stuck, or `vpushes_never_stick` is
#     a statement about a lenient model rather than about `vpush`.
# 17. The two-word compare-and-swap reads its pair atomically, and is not
#     derivable from two single-word ones.  §11.4 runs both on the same memory
#     with the same comparand -- one that fails on purpose, because a winning
#     CAS cannot read stale and so cannot tear.  Two independent CASes must
#     come away with a pair that was never in memory; the pair CAS must admit
#     no such snapshot, asserted over the whole outcome list rather than one
#     oracle choice.  Both rows are required: without the first, the second
#     could be passing because the scenario cannot tear at all.
# 18. A per-location protocol's knowledge clause is bought by the writer's
#     fence and by nothing else.  §14 runs the publication program twice and
#     evaluates `pubProto.knows` at the view the root's message actually
#     carries: with `dmb ishst` the descriptor's initialising write is covered,
#     without it the root carries view 0 and the clause is false.  Both rows
#     are required -- a protocol that held in both would be recording
#     something other than the ordering.
# 19. A protocol survives arbitrary environment interference, and it survives
#     it *because* of the exclusion and not by luck.  §14 runs the same
#     publication with one Remote step interposed, the oracle taking the worst
#     option open to it -- write at the root, and write a pointer rather than
#     null, since null satisfies `wf` and would prove nothing.  With the root
#     disowned the write is dropped and `Governs` holds; without it Remote
#     lands the wrong pointer and `Governs` fails.  Both rows are required:
#     the positive one alone is consistent with the environment having been
#     harmless.
# 20. Two protocols compose to *pin* the dereferenced value, and the
#     descriptor-side hypothesis is the one doing it.  §14 publishes with the
#     fence and dereferences the root carrying the dependency; the second row
#     overwrites the descriptor after publishing.  Both the hypothesis
#     (`settled`, the Bool image of `GovernsFrom (immProto v) d t₀`) and the
#     conclusion (`deref`) are printed, and both rows are required because
#     they must fail *together* -- a control that only broke the conclusion
#     would not show which hypothesis was responsible.
# 21. The architecture refinement is about something.  §15's monotonicity
#     lemmas would all be true and useless if `arm` and `tso` computed the
#     same bounds, so the gate asserts that at a state which has already read,
#     the read bound is *strictly* smaller under `arm`; and that a fence moves
#     `vPreBase`, which is what rules out the simpler refinement (identity on
#     states) and forces `ThreadLe_of_fence_right`.  Both are one-line
#     consequences of definitions that the containment run (item 14) exercises
#     end to end, so this is the cheap local witness for the expensive global
#     one.
# 22. The simulation is a proof and not a promise.  §16 proves that every TSO
#     outcome is an ARM outcome for *every* program, which is the general form
#     of what item 14 measures on 40 shapes.  A proof is only worth the axioms
#     it rests on, so the build output is captured and `#print axioms` is read
#     back: the theorem must be there, and `sorryAx` must not.  This is the one
#     check that reads the compiler rather than the report, because a `sorry`
#     is not a runtime behaviour and nothing the report prints could reveal it.
# 23. The ladder's third row costs something, and the cost is the point.  §17
#     derives a three-word atomic update from the lock, and the gate asserts
#     five rows rather than one, because the interesting comparison is between
#     them.  The naive lock-free attempt and the derived one must expose the
#     *same* intermediate to an observer that is not running the protocol --
#     if those two rows ever differ, the claim "a lock is atomic only against
#     participants" is wrong and §17's headline goes with it.  The third row
#     is the non-vacuity control: an observer that does run the protocol is
#     excluded, so the lock is doing something.  The last two are the reader's
#     side of the same statement.
#
# 24. A pair RMW is single-copy atomic against an observer that is not itself a
#     pair access: two ordinary loads of the two words, separated by a full
#     barrier, may not see the new value of one and the old value of the other.
#     Asserted in *both* word orders, and the two are not redundant -- the
#     model forbade one order and allowed the other, and the order it forbade
#     it forbade by accident of timestamp layout.
# 25. Both sides of §17 are proofs and not demos.  Item 23's rows *exhibit* an
#     atomic update and a consistent snapshot; `sync_write_is_atomic` and
#     `sync_read_is_a_snapshot` state them for any width, and like item 22
#     this is read out of the compiler rather than the report, for the same
#     reason.  Both are named, because the writer's conclusion is the reader's
#     hypothesis: weakening either one silently unhooks the pair.
# 26. Rule 3 of §2.3 is enforced in the `do`-notation front end.  §11.3's
#     promised-writer rows tear *identically* with and without the writer's
#     dmb ishst -- the fence is invisible to a reader -- and differ only in
#     whether the promise could be kept.  All three greps are needed: two fix
#     the rows as identical, and the third fixes the fenced one as not a
#     behaviour.  Without the last, the front end reports a run the machine of
#     §2 would have discarded, and the fence looks inert.
# 27. And the fenced row is a *theorem*, not a row.  Item 26 pins one oracle
#     and two addresses; `fenced_writer_cannot_discharge` says no run of that
#     writer exists for any of them.  Read out of the compiler, like items 22
#     and 25.  The `#guard` next to it -- which the build enforces -- is the
#     non-vacuity control: drop the fence and the promise *is* discharged, so
#     the theorem is not true for uninteresting reasons.
# 28. The documents do not quote a number about this artifact that the
#     artifact does not have.  Markdown cannot compute, so the gate computes
#     -- suite size, gate-item count, the litmus/ group sizes, and
#     §4.1's strictly-weaker count -- and each document quoting one carries an invisible
#     marker at each site saying which number is which: `52<!--@suite-->`
#     renders as "52" and is checked as the suite size.  The two Lean files
#     quote the suite size in their prose as well,
#     so they are scanned for the same markers.
#     So are cats/*.cat, which were not until one of them had rotted from 22
#     to 25 and from 6 to 9.  A comment is a cache too.
#     Only a count that claims something about the *present* should be marked:
#     a validation block recording what was measured on some past day is not
#     stale, and marking it would back-date the measurement.
#     A marker name that nothing carries any more is also a failure,
#     because deleting the last one would otherwise switch the check off.
#     Three independent sources of the suite size are cross-checked first, so
#     the number being propagated is not itself wrong.
# 29. Every line quoted from the report is a line the report
#     prints.  Blocks opt in with a ```report fence; `…` abbreviates and
#     whitespace runs are ignored, so a quote may be shortened and aligned,
#     but a value or a flag that changed will not match.  A bare block whose
#     first line looks like output (`word=`) must be tagged, so forgetting is
#     a failure rather than a silent exemption.
#
#     28 and 29 exist because four stale numbers were found in four
#     consecutive sweeps by hand, and 29 found eleven more the hour it was
#     written.  Documentation that nothing checks is documentation that is
#     wrong; the only question is when somebody notices.
#
# 30. The model agrees with herd7 on litmus tests **nobody here wrote**.
#     litmus/gen/ and litmus/gen-x86/ are `diy7' output for AArch64 and x86-64
#     -- eleven families each, crossed over every ordering mechanism the
#     emitter can express, at one, two, three and four threads -- and each
#     directory's expected.txt is herd7's verdict and state count for each
#     test.  §10's parser reads the assembly back into a `Litmus`, the model
#     runs it, and the two must agree exactly: verdict *and* number of final
#     states.
#
#     Every other check in this file, and every test in the hand-written
#     suite, was written by somebody who already knew what the model did.
#     This is the only one that was not.  It earned its place immediately:
#     eight of the first eighty disagreed, all for one reason, and the fix changed a
#     rule in both model files.  A rule tuned to the
#     examples in front of it passes the examples in front of it.
#
#     herd7 is not re-run here -- expected.txt is a cache of it, and
#     `./check-herd.sh gen gen-x86` is how that cache is invalidated.  The
#     parser is load-bearing, and there are now two of them, so each is checked
#     against the hand-written suite for its own architecture: round-tripping
#     litmus/aarch64/ and litmus/x86_64/ must reproduce those directories'
#     expected.txt exactly.  Without that, a parser that quietly dropped
#     dependencies would make this item agree with herd7 about a program
#     neither of them was reading.
#
#     The round trip is the *only* check on two x86 mnemonics.  `diy7' can
#     generate an `xchg' cycle but has no edge that emits
#     `cmpxchg', so `lock cmpxchg' reaches the reader from litmus/x86_64/ and
#     nowhere else.
#
# 31. Certification is free, and it is what makes progress true.  §2.4 adds the
#     condition Promising Semantics has and this model did not -- a step is only
#     allowed if the stepping thread can still discharge its own promises
#     running alone -- as a *separate* relation, so nothing above it moves.
#     §4.2 measures four things, and each could have failed differently:
#
#       * no shape reaches a different set of states, so no herd7 evidence has
#         to be re-derived and no verdict in any document changes;
#       * certification rejects something, or the first bullet is true for the
#         boring reason;
#       * stuck configurations -- every program finished, a promise still
#         outstanding, which is a counterexample to progress -- are reachable
#         without it, or there was nothing to fix;
#       * and none of them is reachable with it.
#
#     The fourth is stronger than the condition literally buys.  Certification
#     is re-checked for the stepping thread only, so in principle thread `j'
#     could be stranded by thread `i' moving afterwards.  This item is the
#     evidence that it does not happen here, and it is the empirical half of
#     the certification bridge theorem needs.
#
# Usage:
#   ./check-promises.sh
#   LEAN=/path/to/lean ./check-promises.sh     # LEANC defaults to the leanc next to it

set -e

cd "$(dirname "$0")"

LEAN="${LEAN:-$HOME/.elan/bin/lean}"
BUILD="${BUILD:-build}"

mkdir -p "$BUILD"

# --- Native code ---------------------------------------------------------------
# `lean` runs `#eval`, `#guard` and `--run` through its IR interpreter unless the
# imported modules' compiled code is loaded, and the machine runs here (the
# explorer, the type checker, the litmus suite) are 10-50x slower interpreted:
# the largest checked document took 23 minutes to check and takes 17 seconds.  So every
# module is also compiled to C and into one shared library, $BUILD/libwm.so,
# which every later `lean` run loads.  The library is rebuilt from scratch each
# run, so it can never be older than the oleans next to it.
LEANC="${LEANC:-$(dirname "$LEAN")/leanc}"
DYNLIB="$BUILD/libwm.so"
rm -f "$BUILD"/*.o "$BUILD"/*.c "$DYNLIB"
dyn() { if [ -f "$DYNLIB" ]; then echo "--load-dynlib=$DYNLIB"; fi; }
# leanb M: build M.olean (and M.c), then add M to the native library.
leanb() {
  LEAN_PATH="$BUILD" "$LEAN" $(dyn) -o "$BUILD/$1.olean" -c "$BUILD/$1.c" "$1.lean" || return $?
  "$LEANC" -c -w -O3 -DNDEBUG -DLEAN_EXPORTING -fPIC -o "$BUILD/$1.o" "$BUILD/$1.c" >&2 || return $?
  "$LEANC" -shared -o "$DYNLIB.tmp" "$BUILD"/*.o >&2 && mv "$DYNLIB.tmp" "$DYNLIB"
}
# leanr ARGS: run `lean ARGS` against the build, with the native library.
# Not for a file that is itself in the library: the interpreter resolves a
# declaration by its symbol name, so `--run WeakMem.lean` would call WeakMem's
# compiled code without its module initialiser having run (a segfault), and any
# file's `main` would resolve to WeakMem's.  The litmus suites below therefore
# run `WeakMem.lean` without it, as before.
leanr() { LEAN_PATH="$BUILD" "$LEAN" $(dyn) "$@"; }

echo "building WeakMem.olean ..."
leanb WeakMem

echo "building Promises.olean ..."
# Captured, not just echoed: §16's `#print axioms` is compiler output, and the
# axiom check below is the only evidence that the simulation has no `sorry` in
# it.  `set -e` still applies -- a failed build exits before the capture is read.
build_out=$(leanb Promises)

echo "$build_out"

echo "running Report.lean ..."
out=$(leanr Report.lean)

echo "$out"

fail=0

# --- Tutorial.lean -----------------------------------------------------------
# Not a numbered item: the tutorial proves nothing the 24 below do not already
# cover.  It is built for two reasons.  A tutorial that stops compiling is worse
# than no tutorial; and every output its prose quotes is stated next to that
# prose as a `#guard`, so a claim the model no longer satisfies is an
# *elaboration error* and this build is what catches it.
#
# The expected outputs deliberately do *not* appear here.  Restating them in
# this script would be a second hand-written description of the same thing, and
# two descriptions drift, applied to documentation
# instead of to litmus tests.  An earlier version of this step did restate them,
# and a deliberate mutation (an oracle that declines to fulfil a promise) walked
# straight through it: the broken output contained the expected string as a
# prefix.  The in-file guards state the claim structurally -- *which timestamps
# hold the value* -- and reject that mutation.
echo "building Tutorial.lean ..."
if ! tut_out=$(leanr Tutorial.lean 2>&1); then
  echo "$tut_out"
  echo 'FAIL: Tutorial.lean does not compile.  A failing #guard is an error,'
  echo "      so this is either a broken proof or a claim the prose makes that"
  echo "      the model no longer satisfies."
  fail=1
fi

# The one thing the build cannot catch for itself: a `sorry` is a *warning*, and
# warnings do not fail a build.  Same reason numbered item 22 exists.
case "$tut_out" in
  *sorryAx*)
    echo "FAIL: Tutorial.lean's theorem has a sorry"
    fail=1 ;;
esac

# --- Reorder.lean, ReorderSlow.lean -----------------------------------------
# May a compiler swap two adjacent independent plain accesses?
# Every such swap in the suite, and generated pair-vs-observer tests, compared by
# full final-state sets on the promise machine: all sound on ARM; on TSO exactly
# the non-store->load swaps add states.  ReorderSlow.lean runs the full
# generated set (1536 swaps; about 30 s with the native library, 8 min without,
# which is why it is a separate file).
echo "building Reorder.lean ..."
if ! ro_out=$(leanb Reorder 2>&1); then
  echo "$ro_out"
  echo 'FAIL: Reorder.lean: which access swaps the machine permits has changed.'
  fail=1
else
  echo "running ReorderSlow.lean ..."
  if ! ros_out=$(leanr ReorderSlow.lean 2>&1); then
    echo "$ros_out"
    echo 'FAIL: ReorderSlow.lean: the full generated reordering check changed.'
    fail=1
  fi
fi

# --- CoreLang.lean -----------------------------------------------------------
# Not a numbered item, for the same reason as the tutorial: it checks itself.
# Every specification table that the type layer computes is stated as
# a `#guard`, so a function drifting from the note -- or the note from the
# function -- is an elaboration error.  It imports nothing; its .olean is
# built because CoreTerm.lean imports it.
echo "building CoreLang.lean ..."
if ! cl_out=$(leanb CoreLang 2>&1); then
  echo "$cl_out"
  echo 'FAIL: CoreLang.lean does not compile.  A failing #guard is an error,'
  echo "      so either a type-layer function changed or a type-layer table"
  echo "      row it pins no longer holds."
  fail=1
fi

case "$cl_out" in
  *sorryAx*)
    echo "FAIL: a CoreLang.lean theorem has a sorry"
    fail=1 ;;
esac

# --- CoreTerm.lean -----------------------------------------------------------
# The term layer's checker.  Also checks
# itself: Mutex and SeqLock are written as library code and must be accepted,
# and every hazard is a variant that must be rejected *for its stated reason*,
# each a `#guard`.
echo "building CoreTerm.lean ..."
if ! ct_out=$(leanb CoreTerm 2>&1); then
  echo "$ct_out"
  echo 'FAIL: CoreTerm.lean does not compile.  A failing #guard is an error,'
  echo "      so either a typing rule changed or a library program (Mutex,"
  echo "      SeqLock) or one of its rejected variants no longer checks as stated."
  fail=1
fi

case "$ct_out" in
  *sorryAx*)
    echo "FAIL: a CoreTerm.lean theorem has a sorry"
    fail=1 ;;
esac

# --- Scope.lean --------------------------------------------------------------
# Which index variables are in scope at each point of a code block, followed
# with the checker's own context (a load of a protocol word binds one).  Used by
# the formatter and the concrete syntax; its guards check that it follows the
# checker through every library block.
echo "building Scope.lean ..."
if ! sco_out=$(leanb Scope 2>&1); then
  echo "$sco_out"
  echo 'FAIL: Scope.lean: the index scope no longer follows the checker.'
  fail=1
fi

# --- Robust.lean -------------------------------------------------------------
# Crash-robustness of protocols (held states, repeating values) and the opt-in
# local-token discipline, a pass after the checker.  Its guards classify the
# library protocols and accept/refuse the window examples.
echo "building Robust.lean ..."
if ! rob_out=$(leanb Robust 2>&1); then
  echo "$rob_out"
  echo 'FAIL: Robust.lean: the robustness classification or the local-token discipline changed.'
  fail=1
fi

# --- CoreUtils.lean ----------------------------------------------------------
# The LaTeX formatter.  Its `#guard`s pin the notation for a few library types
# and one code block, so a change in how programs print is a deliberate edit.
echo "building CoreUtils.lean ..."
if ! cu_out=$(leanb CoreUtils 2>&1); then
  echo "$cu_out"
  echo 'FAIL: CoreUtils.lean does not compile, or its pinned LaTeX changed.'
  fail=1
fi

# --- CoreTyping.lean ---------------------------------------------------------
# T1b: the declarative judgement, and `checkProg_sound` -- the checker is sound
# for it -- plus the six library programs proved well typed by the kernel.  A
# `sorry` is only a warning, so both the warning and `sorryAx` are looked for,
# and the axiom report for the soundness theorem must be there to be read.
echo "building CoreTyping.lean ..."
if ! cty_out=$(leanb CoreTyping 2>&1); then
  echo "$cty_out"
  echo 'FAIL: CoreTyping.lean does not compile: a soundness proof no longer'
  echo "      goes through, or a library program is no longer accepted."
  fail=1
fi
case "$cty_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a CoreTyping.lean theorem has a sorry"
    fail=1 ;;
esac
if ! echo "$cty_out" | grep -q "'CoreTyping.checkProg_sound' depends on axioms"; then
  echo "FAIL: CoreTyping.lean's '#print axioms checkProg_sound' is missing, so"
  echo "      the soundness theorem was renamed or is no longer checked here."
  fail=1
fi

# --- Complete.lean -----------------------------------------------------------
# How far the checker is from `Typed`: kernel-checked witnesses of terms that
# are `Typed` and refused (`typed_not_checked`), and the algorithmic judgement.
echo "building Complete.lean ..."
if ! cmp_out=$(leanb Complete 2>&1); then
  echo "$cmp_out"
  echo 'FAIL: Complete.lean does not compile: a witness is no longer typed or'
  echo "      no longer refused, or a completeness proof no longer goes through."
  fail=1
fi
case "$cmp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a Complete.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in typed_not_checked progT_not_checked progTA_strict subA_iff tyEqA_iff checkProg_complete ProgTA.toProgT checkProg_iff check_iff check_alg check_complete; do
  if ! echo "$cmp_out" | grep -q "'Complete.$thm' depends on axioms"; then
    echo "FAIL: Complete.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermRun.lean ------------------------------------------------------------
# T2: the term language run on the promise machine.  The `#guard`s are the
# stage's acceptance check -- MP with a plain store of an owned pointer is
# rejected by the checker and *does* read `undef` on ARM; the `publish` repair
# is accepted and never does -- so a compile failure is a failed check.
echo "building TermRun.lean ..."
if ! trun_out=$(leanb TermRun 2>&1); then
  echo "$trun_out"
  echo 'FAIL: TermRun.lean does not compile: an MP acceptance guard failed,'
  echo "      or the semantics no longer builds against CoreTerm/Promises."
  fail=1
fi
case "$trun_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermRun.lean theorem has a sorry"
    fail=1 ;;
esac
if ! echo "$trun_out" | grep -q "'TermRun.freshLabel_inj' depends on axioms"; then
  echo "FAIL: TermRun.lean's '#print axioms freshLabel_inj' is missing."
  fail=1
fi

# new theorems of TermRun.lean (extern steps under outstanding promises): std axioms only
for thm in TermRun.extSteps_elim TermRun.extSteps_intro TermRun.extSteps_frame TermRun.extSteps_shape TermRun.extSteps_thread TermRun.set_self TermRun.extSteps_mem TermRun.extSteps_pairs TermRun.extSteps_cap TermRun.extSteps_lbase TermRun.extSteps_boxFence TermRun.extSteps_size TermRun.extSteps_n TermRun.extSteps_ne TermRun.extSteps_self TermRun.extSteps_stOf TermRun.extSteps_promises TermRun.gOf_ext TermRun.set_get_cases TermRun.extSteps_nil TermRun.extSteps_noPromises; do
  if ! echo "$trun_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermRun.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# (M0) new lemmas of TermRun.lean: std axioms only
for thm in "TermRun.Cfg.size_le_n" "TermRun.Cfg.lt_n" "TermRun.Cfg.n_of_cap0"; do
  if ! echo "$trun_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermRun.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnStep.lean -----------------------------------------------
# (2b) StepX/Spawn: the configuration-level spawn step.
echo "building TermSpawnStep.lean ..."
if ! b2_termspawnstep_out=$(leanb TermSpawnStep 2>&1); then
  echo "$b2_termspawnstep_out"
  echo 'FAIL: TermSpawnStep.lean does not compile.'
  fail=1
fi
case "$b2_termspawnstep_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnStep.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermSpawnStep.lean (extern steps under outstanding promises): std axioms only
for thm in TermSpawnStep.atSite_extSteps; do
  if ! echo "$b2_termspawnstep_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# (2b) TermSpawnStep: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnStep.StepsG.single" \
    "TermSpawnStep.StepsG.trans" \
    "TermSpawnStep.StepsG.tail" \
    "TermSpawnStep.StepsG.ofStep" \
    "TermSpawnStep.StepsG.ofSp" \
    "TermSpawnStep.StepsG.mono" \
    "TermSpawnStep.StepsX.single" \
    "TermSpawnStep.StepsX.trans" \
    "TermSpawnStep.StepsX.ofStep" \
    "TermSpawnStep.StepsX.ofSpawn" \
    "TermSpawnStep.stepsG_pres" \
    "TermSpawnStep.stepsX_pres" \
    "TermSpawnStep.Spawn.elim" \
    "TermSpawnStep.substTs_tb" \
    "TermSpawnStep.close_tb0" \
    "TermSpawnStep.tstep_spawn" \
    "TermSpawnStep.threadSteps_spawn" \
    "TermSpawnStep.promise_ths" \
    "TermSpawnStep.solo_stuck" \
    "TermSpawnStep.cert_stuck" \
    "TermSpawnStep.solo_site" \
    "TermSpawnStep.cert_site" \
    "TermSpawnStep.threadSteps_ths_ne" \
    "TermSpawnStep.promise_ths_ne" \
    "TermSpawnStep.siteNoProm_step" \
    "TermSpawnStep.siteNoProm_spawn" \
    "TermSpawnStep.site_noProm"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnstep_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermExtStep.lean -----------------------------------------------
# (E1) Ext: the trusted extern configuration step.
echo "building TermExtStep.lean ..."
if ! b2_termextstep_out=$(leanb TermExtStep 2>&1); then
  echo "$b2_termextstep_out"
  echo 'FAIL: TermExtStep.lean does not compile.'
  fail=1
fi
case "$b2_termextstep_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermExtStep.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermExtStep.lean (extern steps under outstanding promises): std axioms only
for thm in TermExtStep.extCfg_noPromises TermExtStep.Ext.ofNoProm; do
  if ! echo "$b2_termextstep_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermExtStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# (E1) TermExtStep: every #print axioms theorem, std axioms only.
for thm in \
    "TermExtStep.Ext.elim" \
    "TermExtStep.extCfg_mem" \
    "TermExtStep.extCfg_pairs" \
    "TermExtStep.extCfg_cap" \
    "TermExtStep.extCfg_lbase" \
    "TermExtStep.extCfg_size" \
    "TermExtStep.extCfg_n" \
    "TermExtStep.extCfg_trace" \
    "TermExtStep.extCfg_ths_self" \
    "TermExtStep.extCfg_ths_ne" \
    "TermExtStep.Ext.frame" \
    "TermExtStep.tstep_ext" \
    "TermExtStep.threadSteps_ext" \
    "TermExtStep.StepsE.ofStepsX"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termextstep_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermExtStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPermit.lean ---------------------------------------------------------
# (D4) the permit is invisible to certification: tstep_permit, certified_wake (O6), park_site_step (O5).
echo "building TermPermit.lean ..."
if ! d4_permit_out=$(leanb TermPermit 2>&1); then
  echo "$d4_permit_out"
  echo 'FAIL: TermPermit.lean does not compile.'
  fail=1
fi
case "$d4_permit_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermPermit.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermPermit: every #print axioms theorem, std axioms only.
for thm in \
    "TermPermit.tstep_permit" \
    "TermPermit.certified_wake" \
    "TermPermit.park_site_step"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${d4_permit_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPermit.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- SpawnShapeZ.lean -------------------------------------------------
# (2b) spawn_shapeT: shape of spawnT.
echo "building SpawnShapeZ.lean ..."
if ! b2_spawnshapez_out=$(leanb SpawnShapeZ 2>&1); then
  echo "$b2_spawnshapez_out"
  echo 'FAIL: SpawnShapeZ.lean does not compile.'
  fail=1
fi
case "$b2_spawnshapez_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a SpawnShapeZ.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) SpawnShapeZ: every #print axioms theorem, std axioms only.
for thm in \
    "spawn_shapeT"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_spawnshapez_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: SpawnShapeZ.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermClose.lean ----------------------------------------------------------
# T3c-1: closing a static type (option B).  `cl ρ W c d t`
# replaces free index variables by literals and free type variables by closed
# witnesses; shift, instantiation, `TyEqS` and simultaneous type substitution
# are absorbed into the valuation or the witness map.
echo "building TermClose.lean ..."
if ! tcl_out=$(leanb TermClose 2>&1); then
  echo "$tcl_out"
  echo 'FAIL: TermClose.lean does not compile: a closure lemma no longer goes through.'
  fail=1
fi
case "$tcl_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermClose.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in cl_shiftI cl_shiftT cl_instT cl_tyEq cl_shifted cl_substTs; do
  if ! echo "$tcl_out" | grep -q "'TermClose.$thm' depends on axioms"; then
    echo "FAIL: TermClose.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermTv.lean -------------------------------------------------------------
# T3c-4, option (2): a checker regularity lemma, with no checker change.  Every
# type a typed context records keeps its type variables below `ke.length`
# (`TvOK`), and every operation rule (`OpT_TvOK`), every structural rule, and
# every declaration's body context (`declCx_TvOK`) preserves or establishes it.
echo "building TermTv.lean ..."
if ! ttv_out=$(leanb TermTv 2>&1); then
  echo "$ttv_out"
  echo 'FAIL: TermTv.lean does not compile: a context-regularity lemma no longer goes through.'
  fail=1
fi
case "$ttv_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermTv.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in tb_of_wf guardT_of_tb lt_of_guardT tb_substT tb_substTs instantiate_tb OpT_TvOK declCx_TvOK peek_opaqueOK bind_opaqueOK mg_of_wf mg_unfold1 instantiate_mg peek_mg; do
  if ! echo "$ttv_out" | grep -q "'TermTv.$thm' depends on axioms"; then
    echo "FAIL: TermTv.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# ==== (A1 checker) A1 scope rule ProgScopeOKW + A1 checkW invariant + KidOK argOK/wrapOK + spawn R0 argOK + InitOK stoW ====
# --- TermWrapDefs.lean ----------------------------------------------------------
# (A1 checker) A1 type tests and checkW, moved verbatim from TermScopeW.
echo "building TermWrapDefs.lean ..."
if ! gd9_termwrapdefs_out=$(leanb TermWrapDefs 2>&1); then
  echo "$gd9_termwrapdefs_out"
  echo 'FAIL: TermWrapDefs.lean does not compile.'
  fail=1
fi
case "$gd9_termwrapdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermWrapDefs.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermCkDefs.lean ------------------------------------------------------------
# (A1 checker) wrapTop, VarsW, the witness clause WitA (CkW vocabulary).
echo "building TermCkDefs.lean ..."
if ! gd9_termckdefs_out=$(leanb TermCkDefs 2>&1); then
  echo "$gd9_termckdefs_out"
  echo 'FAIL: TermCkDefs.lean does not compile.'
  fail=1
fi
case "$gd9_termckdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCkDefs.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermCk0.lean ---------------------------------------------------------------
# (A1 checker) TermA4 base lemmas.
echo "building TermCk0.lean ..."
if ! gd9_termck0_out=$(leanb TermCk0 2>&1); then
  echo "$gd9_termck0_out"
  echo 'FAIL: TermCk0.lean does not compile.'
  fail=1
fi
case "$gd9_termck0_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCk0.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermCkS.lean ---------------------------------------------------------------
# (A1 checker) wrapTop and its substitution lemma.
echo "building TermCkS.lean ..."
if ! gd9_termcks_out=$(leanb TermCkS 2>&1); then
  echo "$gd9_termcks_out"
  echo 'FAIL: TermCkS.lean does not compile.'
  fail=1
fi
case "$gd9_termcks_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCkS.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermCkS2.lean --------------------------------------------------------------
# (A1 checker) CkW p w cx e: the frame context is the checker context.
echo "building TermCkS2.lean ..."
if ! gd9_termcks2_out=$(leanb TermCkS2 2>&1); then
  echo "$gd9_termcks2_out"
  echo 'FAIL: TermCkS2.lean does not compile.'
  fail=1
fi
case "$gd9_termcks2_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCkS2.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermCkX.lean ---------------------------------------------------------------
# (A1 checker) parity/ifeq/cas/casp: the checker rule versus Typed.
echo "building TermCkX.lean ..."
if ! gd9_termckx_out=$(leanb TermCkX 2>&1); then
  echo "$gd9_termckx_out"
  echo 'FAIL: TermCkX.lean does not compile.'
  fail=1
fi
case "$gd9_termckx_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCkX.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermCkC.lean ---------------------------------------------------------------
# (A1 checker) split/unpack/region/openPub/case/ifnull child contexts.
echo "building TermCkC.lean ..."
if ! gd9_termckc_out=$(leanb TermCkC 2>&1); then
  echo "$gd9_termckc_out"
  echo 'FAIL: TermCkC.lean does not compile.'
  fail=1
fi
case "$gd9_termckc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCkC.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermCkW.lean ---------------------------------------------------------------
# (A1 checker) checkW_sound: checkW accepts => Typed (copy of check_sound).
echo "building TermCkW.lean ..."
if ! gd9_termckw_out=$(leanb TermCkW 2>&1); then
  echo "$gd9_termckw_out"
  echo 'FAIL: TermCkW.lean does not compile.'
  fail=1
fi
case "$gd9_termckw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCkW.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermCkL.lean ---------------------------------------------------------------
# (A1 checker) every OpT rule binds only x (let continuation contexts).
echo "building TermCkL.lean ..."
if ! gd9_termckl_out=$(leanb TermCkL 2>&1); then
  echo "$gd9_termckl_out"
  echo 'FAIL: TermCkL.lean does not compile.'
  fail=1
fi
case "$gd9_termckl_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCkL.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermCkB.lean ---------------------------------------------------------------
# (A1 checker) TypedR_CkW; CkW along steps (CkW.tk) and at declaration entry (CkW_decl).
echo "building TermCkB.lean ..."
if ! gd9_termckb_out=$(leanb TermCkB 2>&1); then
  echo "$gd9_termckb_out"
  echo 'FAIL: TermCkB.lean does not compile.'
  fail=1
fi
case "$gd9_termckb_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCkB.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermA4.CkW.tk TermA4.CkW_decl; do
  if ! echo "$gd9_termckb_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermCkB.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSound.lean ----------------------------------------------------------
# T3a/T3b-1: one frame against TermRun's `tstep`: P1 and P4 for pure lets
# (arithmetic, pairs, integer packs), `ifeq`, `parity`, `unpack`; P1 for
# `split`; the SubS lemma and the layout-width lemma.  T3b-2c: `inl`, `inr`,
# `case` at non-boxed sums (boxed sums wait for T3c).  T3b-2d: frames — `call`,
# `tail`, `ret` against a stack invariant (the return continuation in `FInv`).
# Each thread-level theorem's axiom report must be present and free of sorryAx.
echo "building TermSound.lean ..."
if ! tsnd_out=$(leanb TermSound 2>&1); then
  echo "$tsnd_out"
  echo 'FAIL: TermSound.lean does not compile: a T3 proof no longer goes through.'
  fail=1
fi
case "$tsnd_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSound.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in VR_ren0 Valid_lnorm get_back decodeArm_back encodeArm_back PayOK_back ptr_of_armK Valid_ptrspine rawWords_popt armK_popt null_arm ofArm_back isBoxed_false Valid_of_VR wc_isBoxed Valid_boxed lnorm_sig case_arm_nb VR_ren vsh_zero VR_seen VR_store accs_of_rawWords isBoxed_lnorm wc_boxed tier_lsum armsWc_lnorm VR_boxL VR_boxR Lay_box sumSpine_er sumSpine_int sumSpine_sig sumSpine_of_sumHead sumSpine_of_isBoxed VR_boxE0 headArms_shp VR_boxE bh_shp IniR_ren tstep_pure tstep_ifeq tstep_parity tstep_split tstep_unpack tstep_unpackT unpackT_step pure_pres pure_progress pushT_FInv KindsOK_call wordFree_close VR_unfold WitAF_subE unguarded_of_guardT sig_pack VR_shiftT tstep_ifnull VR_up VR_sub accs_width shp_wc VR_agree accs_shiftI shp_shiftI skel_substTs wc_iex info_sub shp_sub tstep_inl tstep_inr tstep_case Valid_sub Valid_skel decodeArm_mono roundtrip asArm_valid tstep_call tstep_tail tstep_ret VR_call skel_call substS_comp tstep_fnptr tstep_callc Coh_subE VR_close VR_code Coh_consC VR_substTs VR_relsG cl_subE VR_mono sig_close_cl sig_WitL VR_ext VR_coh FInv_ext Coh_withSto WitL_call pushT_FInv accs_close coupledOK_cl0 admitsIn_share WitSh_call accs_cl_close accs_WitL countI_cl_eq countT_cl_eq accs_shiftT rawWords_iex_inner rawWords_tex_inner accs_inner accs_spine asArm_box projM_nbB Lay_boxR VR_boxLB VR_boxRB find_self_nodup firstOK_nodup; do
  if ! echo "$tsnd_out" | grep -q "'TermSound.$thm' depends on axioms"; then
    echo "FAIL: TermSound.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- P1 (plain) additions: TermTv / TermSound ----------------------------------
for thm in noIallV_shiftI noIallV_shiftT; do
  if ! echo "$ttv_out" | grep -qE "'TermTv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermTv.lean's '#print axioms $thm' is missing."; fail=1
  fi
done
for thm in RInv RInv_unsee RInv_push0 RInv_CE VR_VRR RInv_of RetOKR_RetOK FInvR_FInv ResumeR_Resume ThInvRE.thInvE; do
  if ! echo "$tsnd_out" | grep -qE "'TermSound.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermSound.lean's '#print axioms $thm' is missing."; fail=1
  fi
done

# --- TermTear.lean -----------------------------------------------------------
# T3c-5c: the tear lemma.  A non-atomic load of a shared cell reads each access
# unit from a possibly different store; for a `coupledOK` type, splicing two
# values at a unit boundary gives a value (`VR_tear`, `VR_tearIn`), and `Valid`
# tears for any type (`Valid_tear`).
echo "building TermTear.lean ..."
if ! ttear_out=$(leanb TermTear 2>&1); then
  echo "$ttear_out"
  echo 'FAIL: TermTear.lean does not compile: the tear lemma no longer goes through.'
  fail=1
fi
case "$ttear_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermTear.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in VR_tear Valid_tear VR_tearIn assemble; do
  if ! echo "$ttear_out" | grep -q "'TermTear.$thm' depends on axioms"; then
    echo "FAIL: TermTear.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- KindSound.lean ----------------------------------------------------------
# T3b-2e: row 18's kind lemmas.  A generic body checked once, each type
# parameter answering from its kind, covers every admitted instance: generic
# sharedOK / coupledOK / noOwn / Zeroable imply the instance's, generic
# not-sensitive / not-affine imply the instance's.  For the checker's `substTs`
# and `admitsIn`, and CoreLang §8's sampled `coversInstances` as a theorem.
echo "building KindSound.lean ..."
if ! ksnd_out=$(leanb KindSound 2>&1); then
  echo "$ksnd_out"
  echo 'FAIL: KindSound.lean does not compile: a row-18 kind lemma no longer goes through.'
  fail=1
fi
case "$ksnd_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a KindSound.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in row18_kinds admitsIn_ok coversInstances_true wordFree_covers zero_close; do
  if ! echo "$ksnd_out" | grep -q "'KindSound.$thm' depends on axioms"; then
    echo "FAIL: KindSound.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermMem.lean ------------------------------------------------------------
# T3c-3b: the memory invariant `MemOK` (every message at a Σ cell's offset is a
# unit of a value typed at the cell's static type, or an allocation
# placeholder) and `OwnOK` (each own cell of the thread is, word by word, at
# its latest message under the thread's coherence view, and those words form a
# value of the cell's type); loadUnits/storeUnits/alloc lemmas against them.
echo "building TermMem.lean ..."
if ! tmem_out=$(leanb TermMem 2>&1); then
  echo "$tmem_out"
  echo 'FAIL: TermMem.lean does not compile: a memory-invariant lemma no longer goes through.'
  fail=1
fi
case "$tmem_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermMem.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in alloc_latest stepStore_promSub storeUnits_growsF storeUnits_wrF storeUnits_latestF storeUnits_newOKF storeUnits_memOK0 alloc_ok0 ShapeC_of_wc readable_latest stepLoad_latest stepLoadPair_latest loadUnits_latest MemOK_push stepStore_cases storeUnits_memOK MemOK_pushPair MemOK_mono storeUnits_latest OwnOK_load OwnOK_store alloc_ok wc_of_accs NoProm_grows storeUnits_grows loadUnits_frame alloc_grows storeUnits_nonempty readable_of_latest noStraddle_latest loadUnits_nonempty OwnOK_load_nonempty OwnOK_plain CellOK_map; do
  if ! echo "$tmem_out" | grep -qE "'TermMem.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermMem.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermTidLbl.lean ------------------------------------------------------------
# (E2, R2z) every thread step keeps `tidLbl`.
echo "building TermTidLbl.lean ..."
if ! e2_termtidlbl_out=$(leanb TermTidLbl 2>&1); then
  echo "$e2_termtidlbl_out"
  echo 'FAIL: TermTidLbl.lean does not compile.'
  fail=1
fi
case "$e2_termtidlbl_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermTidLbl.lean theorem has a sorry"
    fail=1 ;;
esac
# (E2) TermTidLbl: every #print axioms theorem, std axioms only.
for thm in \
    "TermTidLbl.enter_tidLbl" \
    "TermTidLbl.tstep_tidLbl"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${e2_termtidlbl_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermTidLbl.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermArch.lean -----------------------------------------------------------
# Menu 2a(a), condition (a) of the ARM reference-semantics decision:
# every configuration reachable by TermRun's declarative `Step`
# under TSO is matched, up to lower views, by one reachable under ARM.
echo "building TermArch.lean ..."
if ! tarch_out=$(leanb TermArch 2>&1); then
  echo "$tarch_out"
  echo 'FAIL: TermArch.lean does not compile: the TSO-to-ARM lift no longer goes through.'
  fail=1
fi
case "$tarch_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermArch.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermArch.lean (extern steps under outstanding promises): std axioms only
for thm in TermArch.ths_some_tid TermArch.extSteps_sim TermArch.events_congr TermArch.extCfg_sim; do
  if ! echo "$tarch_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermArch.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in tso_reach_subset_arm tso_final_subset_arm; do
  if ! echo "$tarch_out" | grep -q "'TermArch.$thm' depends on axioms"; then
    echo "FAIL: TermArch.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermLiveProps.lean ------------------------------------------------------
# The facts TermLive's criterion rests on (A + B):
# thread, promise and machine steps only extend memory, so a class of mutually
# reachable configurations has one memory; a thread at a `cas` comparing
# against the latest value can append, so a class no thread step leaves spins
# only on stale values; a load that keeps its coherence view read old; under
# `robust` every state holds, so no word store types and a `cas` is
# `casShare` or `casEpoch` (no region token).
echo "building TermLiveProps.lean ..."
if ! tlp_out=$(leanb TermLiveProps 2>&1); then
  echo "$tlp_out"
  echo 'FAIL: TermLiveProps.lean does not compile: a liveness fact no longer goes through.'
  fail=1
fi
case "$tlp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermLiveProps.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in evalOp_ext tstep_ext Step_ext reach_mem_eq tstep_cas_appends stale_cas stepLoad_stale robust_holds robust_noStore robust_cas tstep_mono class_coh_eq class_load_stale; do
  if ! echo "$tlp_out" | grep -qE "'TermLiveProps.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermLiveProps.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermViewInv.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInv.lean ..."
if ! tvi0_out=$(leanb TermViewInv 2>&1); then
  echo "$tvi0_out"
  echo 'FAIL: TermViewInv.lean does not compile.'
  fail=1
fi
case "$tvi0_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInv.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ; do
  if ! echo "$tvi0_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermViewInvB.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInvB.lean ..."
if ! tvib_out=$(leanb TermViewInvB 2>&1); then
  echo "$tvib_out"
  echo 'FAIL: TermViewInvB.lean does not compile.'
  fail=1
fi
case "$tvib_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInvB.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ; do
  if ! echo "$tvib_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermViewInvC.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInvC.lean ..."
if ! tvic_out=$(leanb TermViewInvC 2>&1); then
  echo "$tvic_out"
  echo 'FAIL: TermViewInvC.lean does not compile.'
  fail=1
fi
case "$tvic_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInvC.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ; do
  if ! echo "$tvic_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermNallocF.lean (G1a) ------------------------------------------------------
# G1a: steps of non-allocating terms keep nalloc (NotAllocT, tstep_nallocEq).
echo "building TermNallocF.lean ..."
if ! tnallocf_out=$(leanb TermNallocF 2>&1); then
  echo "$tnallocf_out"
  echo 'FAIL: TermNallocF.lean does not compile.'
  fail=1
fi
case "$tnallocf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermNallocF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermNallocF.evalOp_nallocEq TermNallocF.tstep_nallocEq; do
  if ! echo "$tnallocf_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermStep.lean -----------------------------------------------------------
# T3c-4d: P1 + P4 for one thread step against memory.  `ThInvM` is the frame
# invariant `ThInvE` (TermSound) plus `MemInv` (MemOK, OwnOK, no promise at an
# own cell, untouched fresh labels).  Control and pure steps keep memory; `new`
# allocates at the thread's next fresh label; `load`/`store`/`xchg` at an own
# pointer read the latest words and write a whole value of the cell's type.
echo "building TermStep.lean ..."
if ! tstep_out=$(leanb TermStep 2>&1); then
  echo "$tstep_out"
  echo 'FAIL: TermStep.lean does not compile: a thread-step-against-memory proof no longer goes through.'
  fail=1
fi
case "$tstep_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermStep.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in NpZ_of_not NpZ_of_empty PrefixHeld_NpZ NpZ_le NpZ_eq_of_pos MemInv_plantE MemInv_same MemInv_promSt PrivCoh_of PrivCoh_postL PrivCoh_post PrivCoh_growsAt PrivCoh_storeUnits PrivCoh_allocBuf PrivCoh_env PrivU_env notPrivU_iniAt notPrivU_pfr notPrivU_own notPrivU_arr notPrivU_none NewOK_storeF tb_TvB Clo_shiftTN Clo_shiftIN cl_wcons cl_unfold1 AtOff_mu_inv Fd_AtOff Fd_accs Fd_nonmu Fd_mu_inv Fd_noarr Fd_arrFree arrFree_shiftT arrFree_shiftI arrFree_substT Fd_lay Fd_VR Fd_EnvVal TearOK_Fd TearOK_of_cpl Fd_foldS wf_mu_guard single_len tstepM_fold slot_viewN lanes_of fix_of skel_lanes fix_VR fix_Lay lane_rt tstepM_ldlw tstepM_ldl lanes_EnvVal tstepM_stlw tstepM_stl MemInv_fenceG FInv_fenceCx tstepM_fence tstepM_null tstepM_zero cell_cases tstepM_step ThInvS_ThInvM tstepS injM_nbB case_armNB case_armB tstepM_caseB tstepM_caseT Latest_growsAt BoxInv_tr BoxInv_eqs BoxInv_store BoxInv_alloc BoxInv_allocBuf tstepM_pure tstepM_ifeq tstepM_parity tstepM_split tstepM_unpack tstepM_unpackT tstepM_ifnull tstepM_inl tstepM_inr tstepM_case tstepM_ret tstepM_call tstepM_tail tstepM_fnptr tstepM_callc tstepM_new MemInv_load MemInv_store ownLoad ownStoreVal tstepM_loadOwn tstepM_storeOwn tstepM_xchgOwn fld_step tstep_fld tstepM_fld idx_step tstep_idx tstepM_idx Coh_envW VR_mu_unfold VR_cl_unfold sig_cl_unfold VR_at locLoad tstepM_loadLoc VR_put MemInv_storeAt tstepM_storeLoc tstepM_xchgLoc splice_seg own_seg CellOK_put slot_view tstepM_loadAt tstepM_xchgAt accs_AtOff Lay_repred BufOK_put MemInv_bufInit tstepM_bufInit IniAt_idxF compOff_rt tb_compTy tstepM_loadAtF tstepM_xchgAtF zrel_zero zrel_words zero_valOf allocBuf_ok allocBuf_grows tstepM_newBuf MemInv_fence MemInv_publish tstepM_publish PubInv_grow PubInv_store loadUnits_reads Reads_unit loadUnits_nonemptyL MemInv_loadF tstepM_loadPub storeUnits_roles MemInv_storeF tstepM_storePub rawWords_of_sig idxM_cl_agree tyM_cl_agree countT_cl_agree countI_cl_agree accs_cl_guard Clo_cl0 accs_cl_unfold_eq AtOff_embed SegOf_lay TwoAtT_lay AtOff_arr_here AtOff_arr_elem at_seg SegOf_unique InitR_of_IniSeg pub_wordOK nWords_take_le pubLoadAt tstepM_loadPubLoc LayT_of_CellOK OneAt_lt TwoAt_lt nWords_take_embed getElem_embed TwoAt_embed OneAt_embed NewRole_lt SegOf_unique2 PubInv_storeAt MemInv_storePubAt tstepM_storePubLoc cell_lyt peek_buf_lyt compOff_lyt unfold_lyt pub_accs MemInv_box injM_box tstepM_inlB projM_own tstepM_inrB boxed_operand tstepM_inlBB tstepM_inrBB tstepM_inlT tstepM_inrT alloc_undefT UndefNew_of_EFoot UndefNew_of_EFootM alloc_size_len tstep_cap cap_pres find?_filter_and find?_and_of find_firstOK VarsOK_firstOK BoxNewV_seeBox payV_lt pV_of_proj ThInvMFP.toF tstep_footprintP; do
  if ! echo "$tstep_out" | grep -q "'TermStep.$thm' depends on axioms"; then
    echo "FAIL: TermStep.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done
# spawn sites: the progress lemmas' scope excludes them.
for thm in TermStep.not_spawnT_of_mem; do
  if ! echo "$tstep_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# (PIN-D1b) theorems added to TermStep.lean.
for thm in \
    TermNPmixW.storeUnits_NPmixNF \
    TermStep.storeUnits_NPmixF \
    TermStep.heldMixAtLC \
    TermStep.storeUnits_packLeX \
    TermStep.storeUnits_fulInj \
    TermStep.fwr_le_shares \
    TermStep.storeUnits_fwrPay \
    TermStep.mc_liftPLX; do
  if ! echo "$tstep_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# (M0) new lemmas of TermStep.lean: std axioms only
for thm in "TermStep.step_cap" "TermStep.step_n" "TermStep.steps_cap" "TermStep.threadSteps_n" "TermStep.promise_n"; do
  if ! echo "$tstep_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# (2b) theorems added to TermStep.lean.
for thm in \
    "stepsG_bot_iff" \
    "StepsG.ofSteps" \
    "StepsG.toSteps_bot"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${tstep_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPubSto.lean ------------------------------------------------------------
# (D+) new module.
echo "building TermPubSto.lean ..."
if ! g286_termpubsto_out=$(leanb TermPubSto 2>&1); then
  echo "$g286_termpubsto_out"
  echo 'FAIL: TermPubSto.lean does not compile.'
  fail=1
fi
case "$g286_termpubsto_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPubSto.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPubSto.pubSto_of_typed; do
  if ! echo "$g286_termpubsto_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPubSto.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermZf.lean ---------------------------------------------------------------
# TermZf: inertness of the ghost field G.zf (iniop1, runAgree.iniOwn option (1))
echo "building TermZf.lean ..."
if ! tzf_out=$(leanb TermZf 2>&1); then
  echo "$tzf_out"
  echo 'FAIL: TermZf.lean does not compile.'
  fail=1
fi
case "$tzf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermZf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in gOf_zf tstep_zf evalOp_zf injM_zf projM_zf enter_zf callFrame_zf threadSteps_zf MemInv_zf boxFence_zf PAx_zf; do
  if ! echo "$tzf_out" | grep -qE "'TermZf.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermZf.$thm missing or uses non-standard axioms"
    fail=1
  fi
done
for thm in TermStep.IniFixZ_of TermStep.EFoot.iniFixZ; do
  if ! echo "$tzf_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermZf.lean's '#print axioms $thm' is missing or non-standard"
    fail=1
  fi
done

# --- TermPf.lean ---------------------------------------------------------------
# TermPf: inertness of the ghost field G.pf (EFoot tags, PfrTag option (A), user)
echo "building TermPf.lean ..."
if ! tpf_out=$(leanb TermPf 2>&1); then
  echo "$tpf_out"
  echo 'FAIL: TermPf.lean does not compile.'
  fail=1
fi
case "$tpf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in gOf_pf tstep_pf evalOp_pf injM_pf projM_pf enter_pf callFrame_pf threadSteps_pf MemInv_pf boxFence_pf PAx_pf ThInvM_pf; do
  if ! echo "$tpf_out" | grep -qE "'TermPf.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPf.$thm missing or uses non-standard axioms"
    fail=1
  fi
done
for thm in TermStep.PfrG_of TermStep.PfrG_refl TermStep.EFoot.pfrG TermStep.RiniArr_of TermStep.RiniArr_refl TermStep.EFoot.riniArr TermStep.ArrAt_of_buf; do
  if ! echo "$tpf_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPf.lean's '#print axioms $thm' is missing or non-standard"
    fail=1
  fi
done

# --- TermPaid.lean ---------------------------------------------------------------
# (H) H1b: paid blocks, designated promises.
echo "building TermPaid.lean ..."
if ! tpaid_out=$(leanb TermPaid 2>&1); then
  echo "$tpaid_out"
  echo 'FAIL: TermPaid.lean does not compile.'
  fail=1
fi
case "$tpaid_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPaid.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in paidB_plant paidB_plant_of paidB_step blkHeldAfter_of Desig_of TwWords_uniq; do
  if ! echo "$tpaid_out" | grep -qE "'TermPaid.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPaid.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermBlkZ.lean ---------------------------------------------------------------
# (H) H1b: zero-debit blocks.
echo "building TermBlkZ.lean ..."
if ! tblkz_out=$(leanb TermBlkZ 2>&1); then
  echo "$tblkz_out"
  echo 'FAIL: TermBlkZ.lean does not compile.'
  fail=1
fi
case "$tblkz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBlkZ.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in blkDb_zero blkDb_zero_of zwl_exists zwl_existsM zwl_existsG VRR_own_zero; do
  if ! echo "$tblkz_out" | grep -qE "'TermBlkZ.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermBlkZ.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermSlotS.lean ---------------------------------------------------------------
# Slot debits of planted buffers (paidB groundwork).
echo "building TermSlotS.lean ..."
if ! tslots_out=$(leanb TermSlotS 2>&1); then
  echo "$tslots_out"
  echo 'FAIL: TermSlotS.lean does not compile.'
  fail=1
fi
case "$tslots_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSlotS.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in mu_unfold_vrr atl_exists VRR_atl zwl_of_atl atl_bound atl_disj sum_regroup atl_complete offSum_single slot_split blkStart_iff slotStart_iff wordAt_iff clo_word_lit atl_props slot_debits slot_debitsV; do
  if ! echo "$tslots_out" | grep -qE "'TermSlotS.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermSlotS.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermViewInvD0.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInvD0.lean ..."
if ! tvid_out=$(leanb TermViewInvD0 2>&1); then
  echo "$tvid_out"
  echo 'FAIL: TermViewInvD0.lean does not compile.'
  fail=1
fi
case "$tvid_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInvD0.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ; do
  if ! echo "$tvid_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermViewInvE1.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInvE1.lean ..."
if ! tve1_out=$(leanb TermViewInvE1 2>&1); then
  echo "$tve1_out"
  echo 'FAIL: TermViewInvE1.lean does not compile.'
  fail=1
fi
case "$tve1_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInvE1.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in eo_atom eo_pair eo_add eo_mkWord; do
  if ! echo "$tve1_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermViewInvE2.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInvE2.lean ..."
if ! tve2_out=$(leanb TermViewInvE2 2>&1); then
  echo "$tve2_out"
  echo 'FAIL: TermViewInvE2.lean does not compile.'
  fail=1
fi
case "$tve2_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInvE2.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in eo_new eo_publish eo_store eo_newBuf eo_bufInit; do
  if ! echo "$tve2_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermViewInvE3.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInvE3.lean ..."
if ! tve3_out=$(leanb TermViewInvE3 2>&1); then
  echo "$tve3_out"
  echo 'FAIL: TermViewInvE3.lean does not compile.'
  fail=1
fi
case "$tve3_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInvE3.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in eo_xchg eo_stl eo_xchgAt; do
  if ! echo "$tve3_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermViewInvF.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInvF.lean ..."
if ! tvif_out=$(leanb TermViewInvF 2>&1); then
  echo "$tvif_out"
  echo 'FAIL: TermViewInvF.lean does not compile.'
  fail=1
fi
case "$tvif_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInvF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ; do
  if ! echo "$tvif_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermViewInvG.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInvG.lean ..."
if ! tvig_out=$(leanb TermViewInvG 2>&1); then
  echo "$tvig_out"
  echo 'FAIL: TermViewInvG.lean does not compile.'
  fail=1
fi
case "$tvig_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInvG.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in evalOp_V; do
  if ! echo "$tvig_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermViewInvH.lean ---------------------------------------------------------------
# B2 ViewInv: EnvVR as a machine run invariant.
echo "building TermViewInvH.lean ..."
if ! tvih_out=$(leanb TermViewInvH 2>&1); then
  echo "$tvih_out"
  echo 'FAIL: TermViewInvH.lean does not compile.'
  fail=1
fi
case "$tvih_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermViewInvH.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermViewInvH.lean (extern steps under outstanding promises): std axioms only
for thm in TermViewInv.viewInv_extS; do
  if ! echo "$tvih_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermViewInvH.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in viewInv_step viewInv_run envVR_of_run viewInv_init; do
  if ! echo "$tvih_out" | grep -qE "'TermViewInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermViewInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# (2b) theorems added to TermViewInvH.lean.
for thm in \
    "viewInvR_of" \
    "viewInvR_bot"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${tvih_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermViewInvH.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- SpawnVZ.lean -----------------------------------------------------
# (2b) viewInv_spawn: the view invariant across a spawn step.
echo "building SpawnVZ.lean ..."
if ! b2_spawnvz_out=$(leanb SpawnVZ 2>&1); then
  echo "$b2_spawnvz_out"
  echo 'FAIL: SpawnVZ.lean does not compile.'
  fail=1
fi
case "$b2_spawnvz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a SpawnVZ.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) SpawnVZ: every #print axioms theorem, std axioms only.
for thm in \
    "Z2SpawnV.viewInv_spawnCfg" \
    "Z2SpawnV.viewInv_runX" \
    "Z2SpawnV.envVR_of_runX" \
    "Z2SpawnV.viewInv_spawnStep" \
    "Z2SpawnV.WV_bump" \
    "Z2SpawnV.EnvV_cons"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_spawnvz_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: SpawnVZ.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermNPmixW.lean ---------------------------------------------------------
# GdLT: the mixed-store selection keeps every unselected unit's visibility
# (`storeUnits_NPmixW`, `nnv_sel`); TermPiece imports it.
echo "building TermNPmixW.lean ..."
if ! tnpmixw_out=$(leanb TermNPmixW 2>&1); then
  echo "$tnpmixw_out"
  echo 'FAIL: TermNPmixW.lean does not compile.'
  fail=1
fi
case "$tnpmixw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermNPmixW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in nnv_sel stepStore_NPsameS storeUnits_NPmixN storeUnits_NPmixS storeUnits_NPmixW storeUnits_atSame; do
  if ! echo "$tnpmixw_out" | grep -qE "'TermNPmixW.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermNPmixW.$thm missing or uses non-standard axioms"; fail=1
  fi
done
# (PIN-D1b) theorems added to TermNPmixW.lean.
for thm in \
    TermNPmixW.storeUnits_NPmixWF; do
  if ! echo "$tnpmixw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermNPmixW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPiece.lean ----------------------------------------------------------
# D0/D2: pieces of a laid-out type (disjointness, Fact C `Piece_sub`, Fact B
# `VRR_pieces`: resources split exactly over a piece set) and D2 step 2a: a
# `pub` store at another thread's cell whose target units are untorn
# (`UntornU`) replaces the target's words outright (`storeUnits_NPnew`), so the
# old words' resources fund a drop list of the pieces meeting a foreign promise
# (`gd_fund`); `tstepMCF_stepG` is the thread step at `PromCrP` with that list.
echo "building TermPiece.lean ..."
if ! tpiece_out=$(leanb TermPiece 2>&1); then
  echo "$tpiece_out"
  echo 'FAIL: TermPiece.lean does not compile: the piece facts or the drop-list step no longer go through.'
  fail=1
fi
case "$tpiece_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPiece.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in Piece_disj Piece_sub Piece_lift PSet_of VRR_pieces VRR_at_pieces Valid_at Drop_nil pcAt_of gd_fund G_nil tstepMR_storePubG tstepMR_storePubLocG mc_ofPLG tstepMCF_stepG TgtFoot_of_units; do
  if ! echo "$tpiece_out" | grep -q "'TermPiece.$thm' depends on axioms"; then
    echo "FAIL: TermPiece.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done
for thm in UntornU_mono stepStore_NPnewF stepStore_NPnew0 stepStore_untorn storeUnits_NPnew; do
  if ! echo "$tpiece_out" | grep -q "'TermStep.$thm' depends on axioms"; then
    echo "FAIL: TermPiece.lean's '#print axioms TermStep.$thm' is missing."
    fail=1
  fi
done
#: KeepQRS / per-unit re-pin cover (RepinCovU) / StepTgt export
for thm in winGU_of_I mem_rpC mem_rpH sum_rpC_rpH repin_splitU RepinCovS_of_U RepinCovU_nop RepinCovU_keep RepinCovU_biP RepinCovU_of RepinCovU_foreign predAt_of_winGU kPinU_iff kPinU_cov repin_itemU; do
  if ! echo "$tpiece_out" | grep -qE "'TermPiece.$thm' (depends on axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPiece.$thm missing or uses non-standard axioms"; fail=1
  fi
done
# R4 route: theorems added to TermPiece.lean.
for thm in \
    TermPiece.RepinCovSB_of_U \
    TermPiece.repinCovS_of_SB \
    TermPiece.repinCovUB_of_nbi \
    TermPiece.repinCovUB_of_ne; do
  if ! echo "$tpiece_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPiece.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# (PIN-D1b) theorems added to TermPiece.lean.
for thm in \
    TermPiece.vrr_carveX \
    TermPiece.storeLeafPay_of \
    TermPiece.gd_fundX \
    TermPiece.ThInvMPLQX.toPLX \
    TermPiece.mc_ofPLGX; do
  if ! echo "$tpiece_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPiece.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPinAtoms.lean ----------------------------------------------------------
# (PIN-D1a) new module.
echo "building TermPinAtoms.lean ..."
if ! g276_termpinatoms_out=$(leanb TermPinAtoms 2>&1); then
  echo "$g276_termpinatoms_out"
  echo 'FAIL: TermPinAtoms.lean does not compile.'
  fail=1
fi
case "$g276_termpinatoms_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPinAtoms.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPinAtoms.AtomL_bound \
    TermPinAtoms.VRR_atoms \
    TermPinAtoms.VRR_of_atoms \
    TermPinAtoms.Valid_atoms \
    TermPinAtoms.Valid_of_atoms \
    TermPinAtoms.ValOfR_atoms \
    TermPinAtoms.AtomL_atOff \
    TermPinAtoms.atomL_existsG; do
  if ! echo "$g276_termpinatoms_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPinAtoms.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- claim export ----------------------------------------
for thm in MintStepN.toM ownW_cases ClaimAt_zero MintStepN.claimAt mc_keepM cN cNX PubCons_of_not ClaimAtP.of_not OwnOpT_npub claimP_map6 claimP_mapQ7 tstepMC_publishP tstepMCF_stepL alloc_words allocBuf_words; do
  if ! echo "$tstep_out" | grep -qE "'TermStep.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermStep.lean's '#print axioms $thm' is missing."; fail=1
  fi
done

# --- TermCert.lean -----------------------------------------------------------
# T3c-7 L1 and fact (f): a promise whose thread's coherence view at its address
# has reached it is dead (no fulfil's guard admits it), stays dead along any
# solo run, so a certified thread has none: every outstanding promise is above
# the thread's `coh` there (`certified_promAbove`), and a promise made before an
# allocation, at the allocated label, makes the thread uncertifiable
# (`alloc_dead`, `certified_alloc_noProm`).
echo "building TermCert.lean ..."
if ! tcert_out=$(leanb TermCert 2>&1); then
  echo "$tcert_out"
  echo 'FAIL: TermCert.lean does not compile: the dead-promise facts no longer go through.'
  fail=1
fi
case "$tcert_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCert.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermCert.lean (extern steps under outstanding promises): std axioms only
for thm in TermFul.promsOf_ext TermCert.winInv_ext; do
  if ! echo "$tcert_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermCert.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in stepStore_dead stepRmw_dead stepRmwPair_dead alloc_dead allocBuf_dead evalOp_dead tstep_dead solo_dead certified_noDead certified_promAbove certified_alloc_noProm tstep_deadO solo_deadO certified_obAbove certified_promAboveAll certified_promAboveTso loadUnits_read certified_notRead certified_loadStep; do
  if ! echo "$tcert_out" | grep -q "'TermCert.$thm' depends on axioms"; then
    echo "FAIL: TermCert.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermOldLe.lean -------------------------------------------------------------
# R4 route: new module.
echo "building TermOldLe.lean ..."
if ! r4_termoldle_out=$(leanb TermOldLe 2>&1); then
  echo "$r4_termoldle_out"
  echo 'FAIL: TermOldLe.lean does not compile.'
  fail=1
fi
case "$r4_termoldle_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOldLe.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermGlob.lean -----------------------------------------------------------
# Typed consequences of TermCert's fulfil characterisation (stage B, S3): in a
# certified configuration no outstanding promise lies in a `word2` unit of its
# cell's type, and a promise at a `.word n P` position carries a good value.
echo "building TermGlob.lean ..."
if ! tglob_out=$(leanb TermGlob 2>&1); then
  echo "$tglob_out"
  echo 'FAIL: TermGlob.lean does not compile: the typed fulfil facts no longer go through.'
  fail=1
fi
case "$tglob_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermGlob.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in oneAt_word2 certified_noPairProm certified_promWord certified_promQC certified_noPairPromC certified_promWordC; do
  if ! echo "$tglob_out" | grep -q "'TermGlob.$thm' depends on axioms"; then
    echo "FAIL: TermGlob.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermPlant.lean ----------------------------------------------------------
# D2 step 3: the plant transfer and the system's credit invariant.  `plantD1`
# pays each foreign promise from at most one dropped reading (`plantD1_sum_le`,
# `plantD1_tgIn`); `Over_mono_cut`/`gdCov_plant` relate a planted piece to the
# drop list; `PromCrK` (own `PromCr` credit, or a plant credit without own keys,
# `CrKeys`) is `SysInv`'s credit field, with `PromCrK_prom` across the thread's
# own unplanted promise.  Insert BEFORE the TermTyped block (TermTyped and
# TermSys import TermPlant).
echo "building TermPlant.lean ..."
if ! tplant_out=$(leanb TermPlant 2>&1); then
  echo "$tplant_out"
  echo 'FAIL: TermPlant.lean does not compile: the plant transfer or PromCrK no longer go through.'
  fail=1
fi
case "$tplant_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlant.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in rsum_key nsum_ite_le plantD_cons plantD_sum_le plantD_supp tgIn_spec plantD_crShift plantD1_le plantD1_sum_le plantD1_cases plantD1_tgIn ReadTs_exists_ge OverU_mono_gen Over_mono_gen Over_mono_cut plant_piece gdCov_plant CrKeys_zero PromCrK_of PromCrK.toP PromCrK_cr PromCrK_db mem_nodupL nodupL_nodup pSum_congr dropP_of_old PromCrK_prom predEntryL tstepMCF_bufInitPL heldPieceF0L heldPieceFL mc_ofFulES mc_ofFulS SKeepT_setLab SKeepT_setSlot stepOut_ofFS stepOut_ofNS tstepMCF_bufInitFL tstepMCF_stepTS tstepMCF_stlFL tstepMCF_stlwFL tstepMCF_storeLocFL tstepMCF_storeOwnFL tstepMCF_xchgAtFFL tstepMCF_xchgAtFrL tstepMCF_xchgLocFL tstepMCF_xchgOwnFL efootDrop mintStepDrop tstepMCF_stepTKA_zf PlantCr_frameK PlantCr_step keepQX_of_keepPl keepQX_of_keepQ; do
  if ! echo "$tplant_out" | grep -qE "'TermPlant.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlant.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done
# R4 route: theorems added to TermPlant.lean.
for thm in \
    TermPlant.ThInvMCFSQ.congrCr \
    TermPlant.ThInvMCFSQ.toKARSB \
    TermPlant.VR_ones_nundef \
    TermPlant.biRcOut_of_nb \
    TermPlant.heldPieceF0LDC \
    TermPlant.heldPieceFLDC \
    TermPlant.keepQRSB_of_ex \
    TermPlant.keepQRSB_of_nb \
    TermPlant.keepQRS_of_B \
    TermPlant.mapQ8_mono \
    TermPlant.notBiRc_of_ne \
    TermPlant.pieceAcctF0DC \
    TermPlant.slotPayS_mono \
    TermPlant.stepOut_ofFSARSB \
    TermPlant.tstepMCF_bufInitFLDC \
    TermPlant.tstepMCF_bufInitPLC \
    TermPlant.tstepMCF_stepTAC \
    TermPlant.tstepMCF_stepTKAC \
    TermPlant.tstepMCF_stepTKA_zfC \
    TermPlant.tstepMCF_stepTSAC \
    TermPlant.tstepMCF_stlFLDC \
    TermPlant.tstepMCF_stlwFLDC \
    TermPlant.tstepMCF_storeLocFLDC \
    TermPlant.tstepMCF_storeOwnFLDC \
    TermPlant.tstepMCF_xchgAtFFLDC \
    TermPlant.tstepMCF_xchgAtFrLDC \
    TermPlant.tstepMCF_xchgLocFLDC \
    TermPlant.tstepMCF_xchgOwnFLDC; do
  if ! echo "$tplant_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlant.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# (PIN-D1b) theorems added to TermPlant.lean.
for thm in \
    TermPlant.mc_ofPLGQX; do
  if ! echo "$tplant_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlant.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done


# --- TermPiece/TermPlant (check-7 §11 redesign) --------------------
for thm in TermTear.mix2_wrap TermTear.mixR2_gen TermTear.VRR_mix2 TermTear.nWords_take_succ_cons TermTear.mixU_getElem TermPiece.GdCovU.toCov TermPiece.GdCovU_own; do
  if ! echo "$tpiece_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPiece.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done
for thm in TermPlant.PinW_mix TermPlant.mem_winL TermPlant.LowestIn_winL_mono TermPlant.PinW_winL_mono TermPlant.PlantCr_add TermPlant.PredAt_mono TermPlant.LowestIn_back TermPlant.PlantCr_mono TermPlant.H2AtW TermPlant.ForAbove TermPlant.H2AtW_of_ForAbove TermPlant.PlantCr_forAbove TermPlant.Over_mono_cutW TermPlant.PlantCrC TermPlant.PlantCrC.toCr TermPlant.IniWr_cell TermPlant.IniW_cell TermPlant.predEntry TermPlant.PromCr_congrI TermPlant.mc_ofFulE TermPlant.sum_pieces_le TermPlant.wordsAcct TermPlant.dbF_le TermPlant.bufCell TermPlant.tstepMCF_bufInitP TermPlant.iallOK_ofNIP TermPlant.noIallV_shiftTP TermPlant.noIallV_shiftIP TermPlant.noIallV_substTP TermPlant.noIallV_of_substTP TermPlant.noIallV_unfoldP TermPlant.noIallV_foldP TermPlant.noIallV_AtOffP TermPlant.noIallV_FdP TermPlant.noIallV_of_niDeep TermPlant.niCl TermPlant.niDeep_bufOf TermPlant.niDeep_compTy TermPlant.some_det TermPlant.stepOut_ofF TermPlant.stepOut_ofN TermPlant.tstepMCF_stepT TermPiece.sum_map_split TermPlant.pSum_dropA_swap TermPlant.PromCrK_dropA TermPlant.KeepPl_dropA TermPlant.ThInvMCFSQK.toFQK TermPlant.ThInvMCFSQK.mono TermPlant.ThInvMCFSQK.ofS TermPlant.ThInvMCFSQ.toKA TermPlant.stepOut_ofFSA TermPlant.stepOut_ofNSA TermPlant.tstepMCF_stepGLA TermPlant.gdCovU_plant TermPlant.tstepMCF_stepTSA TermPlant.tstepMCF_stepTA TermPlant.tstepMCF_stepTKA; do
  if ! echo "$tplant_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlant.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

for thm in lt_size_of_some piece_match LowOwn_uniq; do
  if ! echo "$tplant_out" | grep -qE "'TermPiece.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlant.lean's '#print axioms $thm' (moved to TermPiece) is missing."; fail=1
  fi
done
# --- OvW3 R1/R2 re-pin --------------------------------------------
for thm in CrItem_mono GdLT_of LayT_of_CellR R_nil RepinCov_biP RepinCov_foreign RepinCov_keep RepinCov_nop RepinCov_of RepinQ_mono ThInvMPLQ.toPL bump_sel carveVRR crKeys_rpSum exists_minN firstW_ext heldMixAtLD inAcc_embR inAcc_oneR inAcc_uniqR kPin_cov kPin_iff latestNP_keepO lowest_inR mix_flip nWords_take_monoR nword_piece opTgtP_of opTgtP_store pcR_valOf pick_list predAt_of_winGI promAt_ext repin_item repin_mixU repin_of_items res_mem_le_sumR rpSum_cons rpSum_ge rpSum_nil rpSum_none seg_of_atOffS storeUnits_fulU storeUnits_newCoh sum_ite_le sum_ite_out sum_map_split sum_rpSum_le tstepMR_storePubGQ tstepMR_storePubLocGQ wle_getR wle_ofR; do
  if ! echo "$tpiece_out" | grep -qE "'TermPiece.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPiece.$thm missing or uses non-standard axioms"; fail=1
  fi
done
for thm in PromCrK_repin ThInvMCFSQ.toKAR ThInvMCFSQK.toR cellAcctD crKeys_iffP crPatchAt_zero heldPieceF0LD heldPieceFLD inAcc_ones_eq keepQR_le keepQR_of_keepQ keepQX_mono keepQX_of_keepQR map_crPatchAt_zero mc_ofFulSQR mc_ofFulSQX mc_ofPLGQ oldCr_nwordZ opTgt_iffP ownLoc_shape ownPtr_shape patchAllD patchOD peek_locZ pieceAcctF0D repinCov_stepK RepinCov_ofX RepinCovXU_of tstepMCF_bufInitFLD repinCovX_tgt bufInit_locZ repinCovX_bufInitN bufInit_idx_le bufInit_idx_ev repinCov_tgt repinCov_wordStore repin_fromDs slot_locZ stepOutR_of stepOutR_of0 stepOut_ofFSAR tstepMCF_stepGLAR tstepMCF_stlFLD tstepMCF_stlwFLD tstepMCF_storeLocFLD tstepMCF_storeOwnFLD tstepMCF_xchgAtFFLD tstepMCF_xchgAtFrLD tstepMCF_xchgLocFLD tstepMCF_xchgOwnFLD tstep_store_foot wordStore_unit; do
  if ! echo "$tplant_out" | grep -qE "'TermPlant.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlant.$thm missing or uses non-standard axioms"; fail=1
  fi
done
#: KeepQRS / per-unit re-pin cover (RepinCovU) / StepTgt export
for thm in keepQRS_le keepQRS_plhMem keepQRS_plhKeys keepQRS_of_keepQ RepinQU_mono PromCrK_repinU ThInvMCFSQ.toKARS le_plh0 covS_nil ThInvMCFSQK.toRS stepOut_ofFSARS repinCovU_tgt stepOutRS_of claimP_mapQ8 repinCovU_wordStore repinCovU_stepK keepQX_of_keepQRS; do
  if ! echo "$tplant_out" | grep -qE "'TermPlant.$thm' (depends on axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlant.$thm missing or uses non-standard axioms"; fail=1
  fi
done
#: PubKeep
for thm in pubKeep_np tstepMR_publishE tstepMC_publishPE OldCr_pub OldCr_uniq pubFix tstepMCF_pubK; do
  if ! echo "$tplant_out" | grep -qE "'TermPlant.$thm' (depends on axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlant.$thm missing or uses non-standard axioms"; fail=1
  fi
done

# --- TermTyped.lean ----------------------------------------------------------
# The typed run along certifying runs and the S3 fix (stage B, S4g): from
# `ProgT` and the run-level scope, thread `i`'s invariant holds at every
# certified configuration reached (`solo_typedP`); every single-word write lands
# on a `.one` unit (`SWOne_holds`); a `WordOK` word at a non-ghost `.word n P`
# position is a state of `P` (`wordOK_good`); hence no outstanding promise of a
# certified thread lies in a `word2` unit (`certified_noPairPromP`), and one at a
# `.word n P` position is `undef` or good (`certified_promWordP`).
echo "building TermTyped.lean ..."
if ! ttyped_out=$(leanb TermTyped 2>&1); then
  echo "$ttyped_out"
  echo 'FAIL: TermTyped.lean does not compile: the typed run / S3 fix no longer goes through.'
  fail=1
fi
case "$ttyped_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermTyped.lean theorem has a sorry"
    fail=1 ;;
esac
# (C) InvAt_ext, solo_typedL/W/P, certified_promTyped/promWordOK/noPairPromT/S/P/promWordT/S/P, solo_ownZero and
# publish_noOwnUse take `NoBoxedCur`/`CurFree` (hnb): restricted to certificate runs with no boxed current(), the
# pre-C coverage; the finals use the anchored X-chain (solo_typedX/certified_promTypedX/flipOK_cert, `TidAt`, no hnb).
# new theorems of TermTyped.lean (extern steps under outstanding promises): std axioms only
for thm in TermTyped.ThInvE_emit TermTyped.ThInvRE_emit TermTyped.ThInvM_emit TermTyped.InvAt_ext TermTyped.InvAtXR_ext; do
  if ! echo "$ttyped_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermTyped.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in certified_hinhW1 wordOK_locPub locPub_VR plant_typeFacts plant_hpl plant_hplCl certified_promAboveSt taken_promAbove PAx_of_step certified_next ThInvM_promise_tr solo_typedL solo_typedW solo_typedP certified_promTyped certified_promWordOK certified_noPairPromT certified_promWordT SWOne_holds wordOK_good pwf_of_inv certified_noPairPromS certified_promWordS certified_noPairPromP certified_promWordP scopeD_SW IniLoc_foot IniHeld_foot witP_run; do
  if ! echo "$ttyped_out" | grep -qE "'TermTyped.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermTyped.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# ScopeAt's spawn-site carve-out.
for thm in TermTyped.not_spawnT_of_steps; do
  if ! echo "$ttyped_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermTyped.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermDPlus.lean -------------------------------------------------------------
# (D+) new module.
echo "building TermDPlus.lean ..."
if ! g286_termdplus_out=$(leanb TermDPlus 2>&1); then
  echo "$g286_termdplus_out"
  echo 'FAIL: TermDPlus.lean does not compile.'
  fail=1
fi
case "$g286_termdplus_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermDPlus.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermDPlus.pubWin_ab \
    TermDPlus.noHold_seen \
    TermDPlus.noHoldPubA_of_N; do
  if ! echo "$g286_termdplus_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermDPlus.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermCut.lean ------------------------------------------------------------
# Stage B, S7: the global environment and per-thread cuts under A-strict.
# Shared-label transfer (`VR_transferS`, `CellOKR_transferS`: store inclusion only
# at cells with a frontier, for `noOR` types; `noOR_of` from `noOwnIn` + `rgnFree`),
# the cuts (`InclS_cut`: every cut contains every other cut's shared part; `Cut_le`),
# and a thread step on E_g read from S6's `EFoot` (`EFoot_post`, `GFoot.le`):
# the stepping thread's witness is exactly its new cut (`Cut_self`), other cuts only
# grow, by exactly the newly published cell (`Cut_other`).
echo "building TermCut.lean ..."
if ! tcut_out=$(leanb TermCut 2>&1); then
  echo "$tcut_out"
  echo 'FAIL: TermCut.lean does not compile: the global environment / cuts no longer go through.'
  fail=1
fi
case "$tcut_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCut.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in VR_transferS VRR_transferS noOR_of InclS.trans WordOK_transferS CellOKR_transferS EnvVal_transferS cutSto_some cutSto_priv InclS_cut Cut_le WordOK_cut CellOKR_cut InclS_cert_cut EFoot_post GFoot.le cutSto_congr Cut_self Cut_other GFoot.sto_old MemHeldS_of_G MemHeldG_of_S HeldEntry_cut; do
  if ! echo "$tcut_out" | grep -qE "'TermCut.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermCut.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermPredHold.lean ---------------------------------------------------------------
# PredHolder: PredHoldG SysInvN clause, holder_min (F1).
echo "building TermPredHold.lean ..."
if ! tph_out=$(leanb TermPredHold 2>&1); then
  echo "$tph_out"
  echo 'FAIL: TermPredHold.lean does not compile.'
  fail=1
fi
case "$tph_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPredHold.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in holder_min predU_cut_seen predHold_none firstW_ex predU_own predU_of; do
  if ! echo "$tph_out" | grep -qE "'TermPredHold.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPredHold.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermZwIni.lean ---------------------------------------------------------------
# Zero-width ini: zwIni SysInvN clause (BH1 removal).
echo "building TermZwIni.lean ..."
if ! tzwi_out=$(leanb TermZwIni 2>&1); then
  echo "$tzwi_out"
  echo 'FAIL: TermZwIni.lean does not compile.'
  fail=1
fi
case "$tzwi_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermZwIni.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in hnew_of_efoot Np_zw NpZ_zw zwIni_none zwIniE_cut zwIni_post; do
  if ! echo "$tzwi_out" | grep -qE "'TermZwIni.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermZwIni.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnKey.lean ---------------------------------------------------------------
# Typed own handles name own cells (B2, ownKeyOwn groundwork).
echo "building TermOwnKey.lean ..."
if ! townkey_out=$(leanb TermOwnKey 2>&1); then
  echo "$townkey_out"
  echo 'FAIL: TermOwnKey.lean does not compile.'
  fail=1
fi
case "$townkey_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnKey.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in VRR_ownL OwnRR_of_cohR MemHeld_ownL MemHeldOn_ownL OwnL_cut; do
  if ! echo "$townkey_out" | grep -qE "'TermOwnKey.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnKey.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermSmoke.lean ----------------------------------------------------------
# T2 smoke test: every library program (mutex, seqlock, Michael-Scott queue,
# claim queue, and the polymorphic variants) set up, then run by two threads
# under the explorer.  The guards: the search finishes, no load returns
# `undef`, the outcomes are the linearisable ones; and a boxed sum stored
# plainly never reads `undef` unless its injection fence is switched off.
echo "building TermSmoke.lean ..."
if ! tsm_out=$(leanb TermSmoke 2>&1); then
  echo "$tsm_out"
  echo 'FAIL: TermSmoke.lean: a library program misbehaves under the semantics.'
  fail=1
fi

# --- TermLive.lean -----------------------------------------------------------
# Liveness under fairness: the explorer's configuration graph kept, its
# strongly connected classes, and the fair-livelock criterion (a class closed
# under thread steps that is not a final configuration).  The guards: the
# mutex's two increments have no fair livelock; with thread 0 allowed to stop,
# the only livelocks are thread 1's spin after thread 0 stopped holding the
# lock; the graph's finals agree with `exploreM`'s.
echo "building TermLive.lean ..."
if ! tlv_out=$(leanb TermLive 2>&1); then
  echo "$tlv_out"
  echo 'FAIL: TermLive.lean: the liveness analysis or its pinned verdicts changed.'
  fail=1
fi

# --- TermOnce.lean -----------------------------------------------------------
# Stage B S9: once-only facts. Region ids are ghost per-thread counters
# (ridPair): freshness given counters rc (fresh_unused, repick_fresh); mint
# shapes (MintStep_wd/rg/sh); Init/MintOK for SysInv's balance; fresh-mint key
# lemma (keySum_fresh, fresh_key_le_one); global epoch monotonicity
# (EpochLocal, epoch_mint_once); share-bound arithmetic.
echo "building TermOnce.lean ..."
if ! tonce_out=$(leanb TermOnce 2>&1); then
  echo "$tonce_out"
  echo 'FAIL: TermOnce.lean does not compile: the once-only facts no longer go through.'
  fail=1
fi
case "$tonce_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOnce.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ridPair_pos ridPair_lt ridPair_unused RidUsed_mono RidUsed_ridSet fresh_unused fresh_bump ridNext_ne_other raiseRid_inv repick_fresh MintStep_wd MintStep_rg MintStep_sh MintOKL_wd_le MintOK_wd_le MintOKL_init MintOKL_step keySum_fresh fresh_key_le_one pSum_PromCr_wd pSum_PromCr_rg EpochLocal.mono EpochMono_of_local EpochLocal_ext EpochLocal_step EpochLocal_steps epoch_mint_once PredAt_ext shareBound_step DbRes_wd_noWord; do
  if ! echo "$tonce_out" | grep -qF "'TermOnce.$thm' "; then
    echo "FAIL: TermOnce.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermLiveHeld.lean -------------------------------------------------------
# Liveness L2 (C1): a step that leaves (or enters, except casTake) a held state
# of a protocol word needs the region token rg n in its frame; with token
# uniqueness, only the holder changes a held word. Whole-cell overwrites of an
# initialised non-epoch word are excluded by the one-carrier-per-region ghost
# key wd n (machine_words after S10 discharges hwd).
echo "building TermLiveHeld.lean ..."
if ! tlh_out=$(leanb TermLiveHeld 2>&1); then
  echo "$tlh_out"
  echo 'FAIL: TermLiveHeld.lean does not compile: the held-word lemmas no longer go through.'
  fail=1
fi
case "$tlh_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermLiveHeld.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in wd_held wholecell_two_carriers wholecell_excluded held_write_dichotomy held_write_needs_token held_enter_needs_token held_word_changes_only_by_holder held_word_changes_only_by_holder_sum pair_write_dichotomy pair_write_needs_token tokUniq_of_sum storeOwn_word_cex storeOwn_wd_frame stp_no_wordAt casp_no_wordAt nonWordFootT_of held_write_dichotomy_noFoot held_write_needs_token_noFoot held_enter_needs_token_noFoot held_word_changes_only_by_holder_noFoot held_word_changes_only_by_holder_sum_noFoot; do
  if ! echo "$tlh_out" | grep -qE "'TermLiveHeld.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermLiveHeld.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermSys.lean ------------------------------------------------------------
# Stage B S7h: the system invariant skeleton SysInv (per-thread ThSys at Cut i:
# ThInvRE + plain ThInvE, MemInv, private/shared held, credits; global MemHeldG,
# GStoClo, SharedTyOK, balance with abstract Init/MintOK, rg and wd key sums)
# and its consequences: tstepMC_step hypotheses at each cut, shared-holding
# agreement, tokUniq_of_SysInv, machine_words_of_SysInv.
echo "building TermSys.lean ..."
if ! tsys_out=$(leanb TermSys 2>&1); then
  echo "$tsys_out"
  echo 'FAIL: TermSys.lean does not compile: the system invariant skeleton no longer goes through.'
  fail=1
fi
case "$tsys_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSys.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in SysInv.intro SysInvW.thread SysInvW.thread_lt ThSys.memHeld ThSys.thInvMC ThSys.thInvM ThSys.thInvR ThSys.env SysInvW.thInvMC SysInvW.thInvM SysInvW.env SysInvW.memHeldS_of_held SysInvW.memHeldG_of_S sum_add_key SysInvW.tokSum SysInvW.tokSum_thread SysInvW.tokUniq SysInvW.wd_thread SysInvW.hwd SysInvW.wdUniq machine_words_of_SysInv tokUniq_of_SysInv; do
  if ! echo "$tsys_out" | grep -qF "'TermSys.$thm' "; then
    echo "FAIL: TermSys.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermStepper.lean --------------------------------------------------------
# Stage B S8b part 1: PromsOK bookkeeping under promise and thread steps
# (fpProm/fpSync), global FpOK/freshness support, the stepper's write footprint
# (tstep_new, termTgt_sto, stepper_writeAt), ini stability (gfoot_ini_*),
# no single-word writes in word2 units (sw_noWord2E), WordOK of new messages at
# shared cells (newMsg_wordOK_*), bundled as stepper_facts.
echo "building TermStepper.lean ..."
if ! tstp_out=$(leanb TermStepper 2>&1); then
  echo "$tstp_out"
  echo 'FAIL: TermStepper.lean does not compile: the stepper facts no longer go through.'
  fail=1
fi
case "$tstp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermStepper.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in PromsOK_promise PromsOK_thread PromsDisj_thread AllPromLt_thread FpOwnFree_thread fpSync_self fpok_of fpok_nil fresh_blankG SysInvW.gfresh evalOp_new tstep_new termTgt_sto tstep_writeAt stepper_writeAt gfoot_ini_other sw_noWord2E newMsg_wordOK_other newMsg_wordOK_own stepper_facts; do
  if ! echo "$tstp_out" | grep -qF "'TermStepper.$thm' "; then
    echo "FAIL: TermStepper.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermIniStep.lean ---------------------------------------------------------------
# D1′: fulfil facts of tstep (vful/fulW).
echo "building TermIniStep.lean ..."
if ! tinis_out=$(leanb TermIniStep 2>&1); then
  echo "$tinis_out"
  echo 'FAIL: TermIniStep.lean does not compile.'
  fail=1
fi
case "$tinis_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermIniStep.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in stepRmw_fulW stepRmwPair_fulW tstep_vful tstep_fulW; do
  if ! echo "$tinis_out" | grep -qE "'TermIniStep.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermIniStep.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermUndefZ.lean ---------------------------------------------------------------
# undefAt vocabulary (B2, U243).
echo "building TermUndefZ.lean ..."
if ! tundz_out=$(leanb TermUndefZ 2>&1); then
  echo "$tundz_out"
  echo 'FAIL: TermUndefZ.lean does not compile.'
  fail=1
fi
case "$tundz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermUndefZ.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermOwnCohZ.lean ---------------------------------------------------------------
# OwnCohZ vocabulary.
echo "building TermOwnCohZ.lean ..."
if ! towcz_out=$(leanb TermOwnCohZ 2>&1); then
  echo "$towcz_out"
  echo 'FAIL: TermOwnCohZ.lean does not compile.'
  fail=1
fi
case "$towcz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCohZ.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermBoxZ.lean ---------------------------------------------------------------
# Box clauses vocabulary: BoxPV/BoxFrOwn/BoxFrLe/PayOwn/BoxSto.
echo "building TermBoxZ.lean ..."
if ! tboxz_out=$(leanb TermBoxZ 2>&1); then
  echo "$tboxz_out"
  echo 'FAIL: TermBoxZ.lean does not compile.'
  fail=1
fi
case "$tboxz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBoxZ.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in payOwn_none; do
  if ! echo "$tboxz_out" | grep -qE "'TermBoxZ.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermBoxZ.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPtrRtsDefs.lean --------------------------------------------------------
# p265b (promInCut_bII): rts vocabulary, imported by TermMainDefs.
echo "building TermPtrRtsDefs.lean ..."
if ! g265_ptrrtsdefs_out=$(leanb TermPtrRtsDefs 2>&1); then
  echo "$g265_ptrrtsdefs_out"
  echo 'FAIL: TermPtrRtsDefs.lean does not compile.'
  fail=1
fi
case "$g265_ptrrtsdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPtrRtsDefs.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermUndefLowDefs.lean ------------------------------------------------------
# Pool cover (undefLow): vocabulary, imported by TermMainDefs.
echo "building TermUndefLowDefs.lean ..."
if ! g265_undeflowdefs_out=$(leanb TermUndefLowDefs 2>&1); then
  echo "$g265_undeflowdefs_out"
  echo 'FAIL: TermUndefLowDefs.lean does not compile.'
  fail=1
fi
case "$g265_undeflowdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermUndefLowDefs.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermOverCrDefs.lean --------------------------------------------------------
# Pool cover (opgQ sidecar): vocabulary, imported by TermMainDefs.
echo "building TermOverCrDefs.lean ..."
if ! g265_overcrdefs_out=$(leanb TermOverCrDefs 2>&1); then
  echo "$g265_overcrdefs_out"
  echo 'FAIL: TermOverCrDefs.lean does not compile.'
  fail=1
fi
case "$g265_overcrdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrDefs.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermPlantIdxDefs.lean -----------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPlantIdxDefs.lean ..."
if ! k1a_termplantidxdefs_out=$(leanb TermPlantIdxDefs 2>&1); then
  echo "$k1a_termplantidxdefs_out"
  echo 'FAIL: TermPlantIdxDefs.lean does not compile.'
  fail=1
fi
case "$k1a_termplantidxdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantIdxDefs.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPlantAtT.plantIdx_none; do
  if ! echo "$k1a_termplantidxdefs_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantIdxDefs.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolDefs.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermPoolDefs.lean ..."
if ! r4_termpooldefs_out=$(leanb TermPoolDefs 2>&1); then
  echo "$r4_termpooldefs_out"
  echo 'FAIL: TermPoolDefs.lean does not compile.'
  fail=1
fi
case "$r4_termpooldefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolDefs.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermMainDefs.lean -------------------------------------------------------
# The vocabulary of the headline-1 skeleton (SysInvN, step contexts) shared by
# TermInterf (S8c) and TermMain.
echo "building TermMainDefs.lean ..."
if ! tmdefs_out=$(leanb TermMainDefs 2>&1); then
  echo "$tmdefs_out"
  echo 'FAIL: TermMainDefs.lean does not compile: the headline-1 vocabulary no longer goes through.'
  fail=1
fi
case "$tmdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermMainDefs.lean theorem has a sorry"
    fail=1 ;;
esac

# (2b) theorems added to TermMainDefs.lean.
for thm in \
    "TCtx.toX" \
    "TCtxX.toBot" \
    "PCtx.toX" \
    "PCtxX.toBot"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${tmdefs_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMainDefs.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermRiniCoh.lean -----------------------------------------------------------
# ((i') riniCoh+frlt) new module.
echo "building TermRiniCoh.lean ..."
if ! g285_termrinicoh_out=$(leanb TermRiniCoh 2>&1); then
  echo "$g285_termrinicoh_out"
  echo 'FAIL: TermRiniCoh.lean does not compile.'
  fail=1
fi
case "$g285_termrinicoh_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermRiniCoh.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermRiniCoh.riniCoh_seen \
    TermRiniCoh.riniCoh_init \
    TermRiniCoh.riniCoh_gfoot \
    TermRiniCoh.riniCoh_prom \
    TermRiniCoh.riniCoh_step \
    TermRiniCoh.hltOwn_of_frlt \
    TermRiniCoh.hltOwn_cut \
    TermRiniCoh.privCoh_seen \
    TermRiniCoh.hltOwn_of_cut \
    TermRiniCoh.hltOwn_sys \
    TermRiniCoh.privCoh_sys; do
  if ! echo "$g285_termrinicoh_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermRiniCoh.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnG0Defs.lean ---------------------------------------------------------------
# G-b.
echo "building TermOwnG0Defs.lean ..."
if ! towng0defs_out=$(leanb TermOwnG0Defs 2>&1); then
  echo "$towng0defs_out"
  echo 'FAIL: TermOwnG0Defs.lean does not compile.'
  fail=1
fi
case "$towng0defs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnG0Defs.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in SoloNP.toSolo; do
  if ! echo "$towng0defs_out" | grep -qE "'TermOwnG0Defs.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnG0Defs.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermK5Defs.lean ---------------------------------------------------------------
# S1b: PfrProvE definition.
echo "building TermK5Defs.lean ..."
if ! tk5defs_out=$(leanb TermK5Defs 2>&1); then
  echo "$tk5defs_out"
  echo 'FAIL: TermK5Defs.lean does not compile.'
  fail=1
fi
case "$tk5defs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK5Defs.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermK5V.lean ---------------------------------------------------------------
# S1b: pub_vWr.
echo "building TermK5V.lean ..."
if ! tk5v_out=$(leanb TermK5V 2>&1); then
  echo "$tk5v_out"
  echo 'FAIL: TermK5V.lean does not compile.'
  fail=1
fi
case "$tk5v_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK5V.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in fenceS_vWr pub_vWr; do
  if ! echo "$tk5v_out" | grep -qE "'TermK5V.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermK5V.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermK5P.lean ---------------------------------------------------------------
# S1b stage (iii): step lemmas for the PfrProvE-carrying producers.
echo "building TermK5P.lean ..."
if ! tk5p_out=$(leanb TermK5P 2>&1); then
  echo "$tk5p_out"
  echo 'FAIL: TermK5P.lean does not compile.'
  fail=1
fi
case "$tk5p_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK5P.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermK5P.lean (extern steps under outstanding promises): std axioms only
for thm in TermK5P.soloNP_snocE TermK5P.pfrProv_ext; do
  if ! echo "$tk5p_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK5P.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in soloNP_snocT soloNP_snocP pfrProvE_start tstep_footprintK tstep_footprintKQ pubZ_noBufInit pfrProv_thread pfrProv_prom; do
  if ! echo "$tk5p_out" | grep -qE "'TermK5P.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermK5P.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# (moved after TermMainDefs; TermIni now imports TermK5P -> TermK5Defs/TermK5V -> TermOwnG0Defs -> TermMainDefs.)
# --- TermK5O.lean ---------------------------------------------------------------
# New module.
echo "building TermK5O.lean ..."
if ! g277_termk5o_out=$(leanb TermK5O 2>&1); then
  echo "$g277_termk5o_out"
  echo 'FAIL: TermK5O.lean does not compile.'
  fail=1
fi
case "$g277_termk5o_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK5O.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermK5O.lean (extern steps under outstanding promises): std axioms only
for thm in TermK5O.pfrProvO_ext; do
  if ! echo "$g277_termk5o_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK5O.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    TermK5O.pfrProvO_start \
    TermK5O.pubZO_noBufInit \
    TermK5O.pubZO_snoc \
    TermK5O.pfrProvO_thread \
    TermK5O.pfrProvO_prom; do
  if ! echo "$g277_termk5o_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK5O.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermIni.lean ---------------------------------------------------------------
# D1′ + holder bound: HoldB, XH typed run, RunAgreeW, planted-label pfr.
echo "building TermIni.lean ..."
if ! tini_out=$(leanb TermIni 2>&1); then
  echo "$tini_out"
  echo 'FAIL: TermIni.lean does not compile.'
  fail=1
fi
case "$tini_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermIni.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in plantT_le plantF_mono holder_iniW HoldB_start HoldB_foot HoldB_prom HoldB_promSt InvAtXH_promOf solo_typedXH certified_promTypedXH certified_promNotUndefXH certified_holderWordH certified_hinhW1H RunAgree_ofW runAgree_pfrL InvAtXHP.toH InvAtXHP_promOf solo_typedXHP certified_promTypedXHP certified_promNotUndefXHP certified_holderWordHP certified_hinhW1HP; do
  if ! echo "$tini_out" | grep -qE "'TermIni.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermIni.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermIniPay.lean ---------------------------------------------------------------
# RunAgreeW.pay from box clauses L1-L3.
echo "building TermIniPay.lean ..."
if ! tinip_out=$(leanb TermIniPay 2>&1); then
  echo "$tinip_out"
  echo 'FAIL: TermIniPay.lean does not compile.'
  fail=1
fi
case "$tinip_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermIniPay.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in runAgree_payW; do
  if ! echo "$tinip_out" | grep -qE "'TermIni.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermIni.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermInterf.lean ---------------------------------------------------------
# S8c interference: an idle thread's invariants across another
# thread's step and a promise step, per field and per MemInv clause.
echo "building TermInterf.lean ..."
if ! tinterf_out=$(leanb TermInterf 2>&1); then
  echo "$tinterf_out"
  echo 'FAIL: TermInterf.lean does not compile: the S8c interference lemmas no longer go through.'
  fail=1
fi
case "$tinterf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermInterf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in cl4_privCoh pcl4_privCoh ThInvRE_incl ThInvE_incl interfFrameT_holds interfFrameP_holds interfHPT_holds \
    fpokVisT_holds freshT_holds interfCrT_holds boxtopT_holds fpokVisP_holds boxtopP_holds \
    freshP_holds interfHPP_holds interfCrP_holds interfMemT_of_clauses cl3_promLt cl4_freshLP \
    cl5_seenLE cl8_ownPubV cl10_boxInv cl11_promOK cl1_memOKP cl6_ownHidP interfMemP_of_clauses \
    pcl3_promLt pcl4_freshLP pcl5_seenLE pcl8_ownPubV pcl10_boxInv pcl11_promOK pcl6_ownHidP \
    pcl1_memOKP cl9_of_parts cl9a_seenOwn cl9b_inh cl9c_pubCpl cl9e_pubLive cl7_pubDefP pcl7_pubDefP \
    pcl9_of_parts pcl9a_seenOwn pcl9b_inh pcl9c_pubCpl pcl9e_pubLive pcl2_ownOKPF pcl9d_pubPair \
    cl9d_pubPair tstep_pairsUp cl2_ownOKPF riniFoot_holds pubFrontier_holds pairStepper_holds interfCrT_mover interfCrPK_holds interfCrTK_holds promSelfK_holds interfCrT_cond interfDb_mover; do
  if ! echo "$tinterf_out" | grep -qF "'TermInterf.$thm' "; then
    echo "FAIL: TermInterf.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermPlantFrz.lean ---------------------------------------------------------------
# PlantFrozen planted half.
echo "building TermPlantFrz.lean ..."
if ! tpfrz_out=$(leanb TermPlantFrz 2>&1); then
  echo "$tpfrz_out"
  echo 'FAIL: TermPlantFrz.lean does not compile.'
  fail=1
fi
case "$tpfrz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantFrz.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in plantFrozen_planted plantFrozenF_of plantFrozenPub_of_iniFix plantFrozenPub_holds; do
  if ! echo "$tpfrz_out" | grep -qE "'TermPlantFrz.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantFrz.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermBal.lean ------------------------------------------------------------
# accounting: net key bounds (K-net) and the balance across thread and
# promise steps, as per-key algebra over the threads (no telescoping needed).
echo "building TermBal.lean ..."
if ! tbal_out=$(leanb TermBal 2>&1); then
  echo "$tbal_out"
  echo 'FAIL: TermBal.lean does not compile: the accounting lemmas no longer go through.'
  fail=1
fi
case "$tbal_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBal.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in promNodupR_of knetP_proof balP_proof knetT_proof balT_proof mintRoomT_of_zero mintRoomT_of_parts mintClosedT_true ridFresh_of knetT_rid claimRoom_D5 claimRoom_noTicket knetT_coreD knetT_D balT_D ridT_N ridP_N claimRoom_at; do
  if ! echo "$tbal_out" | grep -qF "'TermBal.$thm' "; then
    echo "FAIL: TermBal.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermScope.lean ----------------------------------------------------------
# S10 T1/O0: the syntactic scope check ProgScopeOK (region-free interim, no ∀ in
# annotations, D5 no ticket lock), the run invariant RunScope (pinned through Lay), scope_of.
echo "building TermScope.lean ..."
if ! tscope_out=$(leanb TermScope 2>&1); then
  echo "$tscope_out"
  echo 'FAIL: TermScope.lean does not compile: the S10 scope discharge no longer goes through.'
  fail=1
fi
case "$tscope_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermScope.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in drf_of_Lay evalOp_drf tstep_drf run_drf scope_term progT_of_check scope_of noTicket_of residualNoTicket_of; do
  if ! echo "$tscope_out" | grep -qF "'TermScope.$thm' "; then
    echo "FAIL: TermScope.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# ==== (A1 checker) A1 scope rule ProgScopeOKW + A1 checkW invariant + KidOK argOK/wrapOK + spawn R0 argOK + InitOK stoW ====
# (M0) new lemmas of TermScope.lean: std axioms only
for thm in "TermScope.ThScope_withS"; do
  if ! echo "$tscope_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermScope.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# (2b) theorems added to TermScope.lean.
for thm in \
    "runDRF_step" \
    "runDRFR_of" \
    "runDRFR_bot"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${tscope_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermScope.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermScopeW.lean ------------------------------------------------------------
# Scope rule A1: ProgScopeOKW / checkW (ObligationsF.progScope := ProgScopeOKW).
echo "building TermScopeW.lean ..."
if ! gd9_termscopew_out=$(leanb TermScopeW 2>&1); then
  echo "$gd9_termscopew_out"
  echo 'FAIL: TermScopeW.lean does not compile.'
  fail=1
fi
case "$gd9_termscopew_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermScopeW.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermScopeWCk.lean ----------------------------------------------------------
# (A1 checker) ProgScopeOKW gives ProgCkW (the D9 invariant at every declaration).
echo "building TermScopeWCk.lean ..."
if ! gd9_termscopewck_out=$(leanb TermScopeWCk 2>&1); then
  echo "$gd9_termscopewck_out"
  echo 'FAIL: TermScopeWCk.lean does not compile.'
  fail=1
fi
case "$gd9_termscopewck_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermScopeWCk.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermA4.progCkW_of_wrap TermA4.progCkW_of_scopeW; do
  if ! echo "$gd9_termscopewck_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermScopeWCk.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermInit.lean -----------------------------------------------------------
# S11: SysInvW at the empty-memory spawn configuration, the rid clause,
# RunScope initially, EntryOK from the checker.
echo "building TermInit.lean ..."
if ! tinit_out=$(leanb TermInit 2>&1); then
  echo "$tinit_out"
  echo 'FAIL: TermInit.lean does not compile: the S11 initial configuration no longer goes through.'
  fail=1
fi
case "$tinit_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermInit.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in sysInvW_init ridOK_init runDRF_init runDRF_spawn entryOK_of vs0_spawn spawn0_vs0; do
  if ! echo "$tinit_out" | grep -qF "'TermInit.$thm' "; then
    echo "FAIL: TermInit.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermSpawnScope.lean ----------------------------------------------
# (2b) runScope_spawnStep.
echo "building TermSpawnScope.lean ..."
if ! b2_termspawnscope_out=$(leanb TermSpawnScope 2>&1); then
  echo "$b2_termspawnscope_out"
  echo 'FAIL: TermSpawnScope.lean does not compile.'
  fail=1
fi
case "$b2_termspawnscope_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnScope.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnScope: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnScope.thScope_spawnPar" \
    "TermSpawnScope.thScope_spawnKid" \
    "TermSpawnScope.runScope_spawnStep" \
    "TermSpawnScope.runScopeR_spawn" \
    "TermSpawnScope.run_scopeX"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnscope_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnScope.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermDwf.lean ------------------------------------------------------------
# T3 (route c′): StoreCrZ at every reachable step, non-epoch half by the wd key
# (KeyNet), epoch half from PromPred, predicted slots excluded by NoPredEpoch.
echo "building TermDwf.lean ..."
if ! tdwf_out=$(leanb TermDwf 2>&1); then
  echo "$tdwf_out"
  echo 'FAIL: TermDwf.lean does not compile: the StoreCrZ discharge no longer goes through.'
  fail=1
fi
case "$tdwf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermDwf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in storePub_wd_at storePubLoc_wd_at sum_range_le sum_range_skip sum_range_split storeCrZ_of dwf_of; do
  if ! echo "$tdwf_out" | grep -qF "'TermDwf.$thm' "; then
    echo "FAIL: TermDwf.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done
# (PIN-D1b) theorems added to TermDwf.lean.
for thm in \
    TermDwf.storeCrZ0_of \
    TermDwf.dwf0_of; do
  if ! echo "$tdwf_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermDwf.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermIall.lean -----------------------------------------------------------
# T2 (option ii): StoreIall at every reachable step, by pinning the stored cell's
# type to the runtime type (ProgIall in ProgScopeOK) and WitAF's ∀-free witnesses.
echo "building TermIall.lean ..."
if ! tiall_out=$(leanb TermIall 2>&1); then
  echo "$tiall_out"
  echo 'FAIL: TermIall.lean does not compile: the StoreIall discharge no longer goes through.'
  fail=1
fi
case "$tiall_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermIall.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in noIallV_AtOff noIallV_Fd storeIall_term iall_of; do
  if ! echo "$tiall_out" | grep -qF "'TermIall.$thm' "; then
    echo "FAIL: TermIall.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermNoHold.lean ---------------------------------------------------------
# certificate facts (certified_promLoc, PromLocF discharge, epoch PromPred).
echo "building TermNoHold.lean ..."
if ! tnohold_out=$(leanb TermNoHold 2>&1); then
  echo "$tnohold_out"
  echo 'FAIL: TermNoHold.lean does not compile: the certificate facts no longer go through.'
  fail=1
fi
case "$tnohold_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermNoHold.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in solo_typedXF certified_promLoc promLocP promLocT promLocF_of certified_promPredE promPredT InvAtXFP.toF InvAtXFP_of solo_typedXFP; do
  if ! echo "$tnohold_out" | grep -qE "'TermNoHold.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermNoHold.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermBiiS.lean --------------------------------------------------------------
# (BII v3) new module.
echo "building TermBiiS.lean ..."
if ! g278_termbiis_out=$(leanb TermBiiS 2>&1); then
  echo "$g278_termbiis_out"
  echo 'FAIL: TermBiiS.lean does not compile.'
  fail=1
fi
case "$g278_termbiis_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBiiS.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermBiiS.tstep_footprintB \
    TermBiiS.xfz_threadB; do
  if ! echo "$g278_termbiis_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBiiS.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermXFO.lean ---------------------------------------------------------------
# New module.
echo "building TermXFO.lean ..."
if ! g277_termxfo_out=$(leanb TermXFO 2>&1); then
  echo "$g277_termxfo_out"
  echo 'FAIL: TermXFO.lean does not compile.'
  fail=1
fi
case "$g277_termxfo_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermXFO.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermXFO.InvAtXFO.toF \
    TermXFO.InvAtXFO.toZ \
    TermXFO.InvAtXFO_of \
    TermXFO.solo_typedXFO \
    TermXFO.certified_promNotUndefXO; do
  if ! echo "$g277_termxfo_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermXFO.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantF.lean ---------------------------------------------------------
# plant choice and certificate-backed plant/promise fields.
echo "building TermPlantF.lean ..."
if ! tplantf_out=$(leanb TermPlantF 2>&1); then
  echo "$tplantf_out"
  echo 'FAIL: TermPlantF.lean does not compile: the plant/promise fields no longer go through.'
  fail=1
fi
case "$tplantf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in inclS_bare plantInhZ noBoxProm_of oneAt_twoAtT promNoTwoP_of plantSpec_of plantCpl_of promTyAPostP_of promIniPostP_of promTyAPost_of promIniPost_of promViewLt_run plantInh_of SWIni promNewIni_of promNewWord_of promNewOK_of plantPromOK_of pubPromOK_of promIniGen promWordGen inclS_plantE inclS_post; do
  if ! echo "$tplantf_out" | grep -qE "'TermPlantF.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantF.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# (2b) theorems added to TermPlantF.lean.
for thm in \
    "TermPlantF.promViewLtR_of"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${tplantf_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantF.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPredHoldP.lean ---------------------------------------------------------------
# PredHoldG preservation at thread/promise steps.
echo "building TermPredHoldP.lean ..."
if ! tphp_out=$(leanb TermPredHoldP 2>&1); then
  echo "$tphp_out"
  echo 'FAIL: TermPredHoldP.lean does not compile.'
  fail=1
fi
case "$tphp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPredHoldP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in predHold_prom plantHeld_of predHold_promX predHold_thread hIL_of_efoot; do
  if ! echo "$tphp_out" | grep -qE "'TermPredHoldP.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPredHoldP.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantHidOf.lean ---------------------------------------------------------------
# plantHid discharged (B2).
echo "building TermPlantHidOf.lean ..."
if ! tphof_out=$(leanb TermPlantHidOf 2>&1); then
  echo "$tphof_out"
  echo 'FAIL: TermPlantHidOf.lean does not compile.'
  fail=1
fi
case "$tphof_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantHidOf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in plantHid_of; do
  if ! echo "$tphof_out" | grep -qE "'TermPlantHidOf.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantHidOf.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantR.lean --------------------------------------------------------
# raise/plant one label in a thread (MemHeld/PromCr/ThInvMC across a plant).
echo "building TermPlantR.lean ..."
if ! tplantr_out=$(leanb TermPlantR 2>&1); then
  echo "$tplantr_out"
  echo 'FAIL: TermPlantR.lean does not compile.'
  fail=1
fi
case "$tplantr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantR.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in MemHeld_raise MemHeld_raiseS PromCr_raise acct_raise tele_chain ThInvMC_raise MemHeld_flipLH MemHeld_plantN unit_tele hnew_word hacc_word MemHeld_plantW ThInvMC_plantW WordOK_wordbuf latest_prom hval_of ThInvMC_plantWH ThInvMC_plantWF plantF_congrE; do
  if ! echo "$tplantr_out" | grep -qE "'TermPlantR.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantR.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantFul.lean ---------------------------------------------------------------
# plantFulfil from PlantAtT + OwnKeyT; W1 taken-r (c).
echo "building TermPlantFul.lean ..."
if ! tpfu_out=$(leanb TermPlantFul 2>&1); then
  echo "$tpfu_out"
  echo 'FAIL: TermPlantFul.lean does not compile.'
  fail=1
fi
case "$tpfu_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantFul.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in plantFulfil_of ownKeyT_of plantPendT_of plantOp_W1T; do
  if ! echo "$tpfu_out" | grep -qE "'TermPlantFul.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantFul.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantOpG.lean ---------------------------------------------------------------
# plantOp: W1-W3 from PlantAtT; only cover part plantOpG remains.
echo "building TermPlantOpG.lean ..."
if ! tpog_out=$(leanb TermPlantOpG 2>&1); then
  echo "$tpog_out"
  echo 'FAIL: TermPlantOpG.lean does not compile.'
  fail=1
fi
case "$tpog_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantOpG.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in plantOp_of; do
  if ! echo "$tpog_out" | grep -qE "'TermPlantOpG.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantOpG.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOverCr.lean ------------------------------------------------------------
# Pool cover (opgQ sidecar, TermPromAboveG closure).
echo "building TermOverCr.lean ..."
if ! g265_overcr_out=$(leanb TermOverCr 2>&1); then
  echo "$g265_overcr_out"
  echo 'FAIL: TermOverCr.lean does not compile.'
  fail=1
fi
case "$g265_overcr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCr.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermOverCr.crItem_of_Q TermOverCr.coverAt_of_overCr TermOverCr.plantOpG_of TermOverCr.overCr_noProm TermOverCr.overCrG_noProm TermOverCr.crItem_frame TermOverCr.overCr_frame TermOverCr.item_of_plantCr TermOverCr.item_of_plantCr_ex; do
  if ! echo "$g265_overcr_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOverCr4.lean -----------------------------------------------------------
# Pool cover (opgQ sidecar).
echo "building TermOverCr4.lean ..."
if ! g265_overcr4_out=$(leanb TermOverCr4 2>&1); then
  echo "$g265_overcr4_out"
  echo 'FAIL: TermOverCr4.lean does not compile.'
  fail=1
fi
case "$g265_overcr4_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCr4.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermOverCr4.predAt_of_latestNP TermOverCr4.latestNP_of_predAt TermOverCr4.crItem_of_latest TermOverCr4.below_unskipped TermOverCr4.overCr_extend TermOverCr4.lowOwn_ne TermOverCr4.holder_ne TermOverCr4.promAt_sh_iff TermOverCr4.oldCr_nword_zero TermOverCr4.plantCr_of_nz TermOverCr4.f2bS_self TermOverCr4.promAt_sub TermOverCr4.gd_item TermOverCr4.gd_itemQ TermOverCr4.piece_newOver; do
  if ! echo "$g265_overcr4_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantW.lean --------------------------------------------------------
# one label plant in the global environment (ThSysAt_plant1).
echo "building TermPlantW.lean ..."
if ! tplantw_out=$(leanb TermPlantW 2>&1); then
  echo "$tplantw_out"
  echo 'FAIL: TermPlantW.lean does not compile.'
  fail=1
fi
case "$tplantw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in CE_withSto_Cut HoldW_prom PrefixHeld_prom hhold_prom acct_trans PromCrK_lift ThSysAt_plant1; do
  if ! echo "$tplantw_out" | grep -qE "'TermPlantW.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantW.$thm missing or uses non-standard axioms"
    fail=1
  fi
done
# R4 route: theorems added to TermPlantW.lean.
for thm in \
    TermPlantW.KeepNW_of_sto \
    TermPlantW.KeepNW_refl \
    TermPlantW.KeepNW_trans \
    TermPlantW.PromCrK_liftG \
    TermPlantW.PromCrK_liftK \
    TermPlantW.PromCrK_liftQK \
    TermPlantW.ThSysAt_plant1K \
    TermPlantW.exK_sto; do
  if ! echo "$tplantw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantL.lean --------------------------------------------------------
# plant iteration (ThSysAt_plantL, plantL_eq_plantG).
echo "building TermPlantL.lean ..."
if ! tplantl_out=$(leanb TermPlantL 2>&1); then
  echo "$tplantl_out"
  echo 'FAIL: TermPlantL.lean does not compile.'
  fail=1
fi
case "$tplantl_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantL.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ThSysAt_plant1B ThSysAt_plantL plantL_eq_plantG FlipOK_agree FpOK_agree HoldW_agree ThSysAt_flip1 ThSysAt_flip1B; do
  if ! echo "$tplantl_out" | grep -qE "'TermPlantL.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantL.$thm missing or uses non-standard axioms"
    fail=1
  fi
done
# R4 route: theorems added to TermPlantL.lean.
for thm in \
    TermPlantL.ThSysAt_flip1BK \
    TermPlantL.ThSysAt_flip1K \
    TermPlantL.ThSysAt_plant1BK \
    TermPlantL.ThSysAt_plantLK; do
  if ! echo "$tplantl_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantL.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantE.lean --------------------------------------------------------
# event layer, ThSys_plantW and selfPlant_of.
echo "building TermPlantE.lean ..."
if ! tplante_out=$(leanb TermPlantE 2>&1); then
  echo "$tplante_out"
  echo 'FAIL: TermPlantE.lean does not compile.'
  fail=1
fi
case "$tplante_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantE.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in promSelfK_any ThSysAt_prom iniCap_of_heldP promTyL plantStep ThSys_plantW selfPlant_of flipOK_post flipStep; do
  if ! echo "$tplante_out" | grep -qE "'TermPlantE.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantE.$thm missing or uses non-standard axioms"
    fail=1
  fi
done
# R4 route: theorems added to TermPlantE.lean.
for thm in \
    TermPlantE.ThSysAt_promK \
    TermPlantE.flipStepK \
    TermPlantE.plantStepK; do
  if ! echo "$tplante_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantE.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPredOne.lean ---------------------------------------------------------------
# W=2 .one lemma for plants (used by TermPlantR1).
echo "building TermPredOne.lean ..."
if ! tpone_out=$(leanb TermPredOne 2>&1); then
  echo "$tpone_out"
  echo 'FAIL: TermPredOne.lean does not compile.'
  fail=1
fi
case "$tpone_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPredOne.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in allOne_of_held plantNew_allOne; do
  if ! echo "$tpone_out" | grep -qE "'TermPredOne.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPredOne.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantS.lean --------------------------------------------------------
# simultaneous plant of copyable unit buffers (design B).
echo "building TermPlantS.lean ..."
if ! tplants_out=$(leanb TermPlantS 2>&1); then
  echo "$tplants_out"
  echo 'FAIL: TermPlantS.lean does not compile.'
  fail=1
fi
case "$tplants_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantS.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in WordOK_unit ValOfR_copy slotR_of_wordOK HeldEntry_raiseU MemHeld_raiseQ PromCr_raiseQ MemHeld_flipQ PromCrK_liftQ firstW_of_R1w plantS_plantL_eq unitFacts nWords_ones nWords_take_ones slot_eq WordOK_slot HeldEntry_raiseUR; do
  if ! echo "$tplants_out" | grep -qE "'TermPlantS.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantS.$thm missing or uses non-standard axioms"
    fail=1
  fi
done
# Shared slot theorem in TermPlantS.lean.
for thm in \
    TermPlantS.slotFacts; do
  if ! echo "$tplants_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantS.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantP.lean --------------------------------------------------------
# privSlot from PrivCoh; .two units are never planted.
echo "building TermPlantP.lean ..."
if ! tplantp_out=$(leanb TermPlantP 2>&1); then
  echo "$tplantp_out"
  echo 'FAIL: TermPlantP.lean does not compile.'
  fail=1
fi
case "$tplantp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in privR1w privSlot_of slot_oneAt plantN_two; do
  if ! echo "$tplantp_out" | grep -qE "'TermPlantP.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantP.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantR1.lean ---------------------------------------------------------------
# selfPlant R1: SelfPlantRestN vacuous via stoNI.
echo "building TermPlantR1.lean ..."
if ! tpr1_out=$(leanb TermPlantR1 2>&1); then
  echo "$tpr1_out"
  echo 'FAIL: TermPlantR1.lean does not compile.'
  fail=1
fi
case "$tpr1_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantR1.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in pw_two chain_tele slot_debitsW slot_debitsWV PrivSlotA.toF privSlot_any exists_greatest HeldEntry_raiseW AtB_iff sum_filter_succN sum_filter_succM unit_tele FRes_wv FRes_eq_wv WRes_wv wvE_undef newDb_res newCr_res noOwnR_zero blkDb_nstart unit_pay sum_map_eq_zero sum_map_add sum_ind sum_part sum_new wvE_nword slot_pay slotR_tear nodup_map_some sum_range_mul sum_units nWl_eq RdW_uniq RdW_ex filter_sub sum_congrB slot_in slot_divmod rdW_list_eq raise_pay ThSysAt_plantQ wvE_noAt wdE_noAt newDb_zero newCr_zero wordAt_of_unit r1Facts qSplit qFacts ThSys_plantR selfPlant_ofR Np_nonarr plantNew_shape SelfPlantRestN.toR selfPlant_ofN selfPlantRestN_of; do
  if ! echo "$tpr1_out" | grep -qE "'TermPlantR1.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantR1.$thm missing or uses non-standard axioms"
    fail=1
  fi
done
# TermPlantS.{ThSysAt_plantS,ThSys_plantS,selfPlant_of} live in TermPlantR1 (namespace TermPlantS).
for thm in ThSysAt_plantS ThSys_plantS selfPlant_of; do
  if ! echo "$tpr1_out" | grep -qE "'TermPlantS.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantS.$thm missing or uses non-standard axioms"
    fail=1
  fi
done
# R4 route: theorems added to TermPlantR1.lean.
for thm in \
    TermPlantR1.ThSysAt_plantQK \
    TermPlantR1.ThSys_plantRK; do
  if ! echo "$tpr1_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantR1.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermStoreNI.lean --------------------------------------------------------
# storeNI from the post-step certificate + named fact SeenHid (Obligations.seenHid).
echo "building TermStoreNI.lean ..."
if ! tsni_out=$(leanb TermStoreNI 2>&1); then
  echo "$tsni_out"
  echo 'FAIL: TermStoreNI.lean does not compile.'
  fail=1
fi
case "$tsni_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermStoreNI.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in Bnd_le_storeOb stepStore_info storeUnits_frame storeUnits_bound latest_below initAt_hid storeNI_bound storeNI_of storeNI_field; do
  if ! echo "$tsni_out" | grep -qE "'TermStoreNI.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermStoreNI.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermWdCover.lean --------------------------------------------------------
# memory-side wd accounting: dwf_ofM replaces the (false) wdCover field; named facts holderUniq, storeHolderFree.
echo "building TermWdCover.lean ..."
if ! twdc_out=$(leanb TermWdCover 2>&1); then
  echo "$twdc_out"
  echo 'FAIL: TermWdCover.lean does not compile.'
  fail=1
fi
case "$twdc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermWdCover.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in leaf_word one_at db_wd_pos db_wd_le1 VRR_count_head VRR_count cell_count held_count cutSto_vis; do
  if ! echo "$twdc_out" | grep -qE "'TermWdCover.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermWdCover.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPromNU.lean --------------------------------------------------------
# SysInvN clause promNU (outstanding promises are non-undef).
echo "building TermPromNU.lean ..."
if ! tpnu_out=$(leanb TermPromNU 2>&1); then
  echo "$tpnu_out"
  echo 'FAIL: TermPromNU.lean does not compile.'
  fail=1
fi
case "$tpnu_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPromNU.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in promNU_thread promNU_prom; do
  if ! echo "$tpnu_out" | grep -qE "'TermPromNU.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPromNU.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermSeenHid.lean --------------------------------------------------------
# seenHid proved from EnvVR + FrontW (field seenFacts).
echo "building TermSeenHid.lean ..."
if ! tseen_out=$(leanb TermSeenHid 2>&1); then
  echo "$tseen_out"
  echo 'FAIL: TermSeenHid.lean does not compile.'
  fail=1
fi
case "$tseen_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSeenHid.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in undef_not_wordOK valOf_nundef own_val store_target slot_lt hid_of_hidden hid_of_latest seenHid_of; do
  if ! echo "$tseen_out" | grep -qE "'TermSeenHid.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermSeenHid.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermShty.lean --------------------------------------------------------
# S10: shared cell types noOR (field shtyT discharged).
echo "building TermShty.lean ..."
if ! tshty_out=$(leanb TermShty 2>&1); then
  echo "$tshty_out"
  echo 'FAIL: TermShty.lean does not compile.'
  fail=1
fi
case "$tshty_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermShty.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in shtyT_holds; do
  if ! echo "$tshty_out" | grep -qE "'TermShty.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermShty.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnFresh.lean --------------------------------------------------------
# SysInvN clause ownF (OwnFreshZ); field ownKeySto discharged.
echo "building TermOwnFresh.lean ..."
if ! towf_out=$(leanb TermOwnFresh 2>&1); then
  echo "$towf_out"
  echo 'FAIL: TermOwnFresh.lean does not compile.'
  fail=1
fi
case "$towf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnFresh.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in keyLoad_zero promCrK_own ownFresh_thread ownFresh_prom mintRoomF_at knetT_F ownFreshZ_zero; do
  if ! echo "$towf_out" | grep -qE "'TermOwnFresh.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnFresh.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrBII.lean ---------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrBII.lean ..."
if ! r4_termovercrbii_out=$(leanb TermOverCrBII 2>&1); then
  echo "$r4_termovercrbii_out"
  echo 'FAIL: TermOverCrBII.lean does not compile.'
  fail=1
fi
case "$r4_termovercrbii_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrBII.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermPoolStaging.lean -------------------------------------------------------
# R4 route: new module.
echo "building TermPoolStaging.lean ..."
if ! r4_termpoolstaging_out=$(leanb TermPoolStaging 2>&1); then
  echo "$r4_termpoolstaging_out"
  echo 'FAIL: TermPoolStaging.lean does not compile.'
  fail=1
fi
case "$r4_termpoolstaging_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolStaging.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolStaging.poolTag_iff \
    TermPoolStaging.cr_le_crPl \
    TermPoolStaging.PoolInv.old \
    TermPoolStaging.δc_add_δh_le \
    TermPoolStaging.crShiftP_δc \
    TermPoolStaging.δh_tag; do
  if ! echo "$r4_termpoolstaging_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolStaging.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolBal.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermPoolBal.lean ..."
if ! r4_termpoolbal_out=$(leanb TermPoolBal 2>&1); then
  echo "$r4_termpoolbal_out"
  echo 'FAIL: TermPoolBal.lean does not compile.'
  fail=1
fi
case "$r4_termpoolbal_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolBal.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolBal.keyT_pool \
    TermPoolBal.keyP_pool \
    TermPoolBal.room_pool \
    TermPoolBal.poolBalT_of \
    TermPoolBal.poolKnetT_of \
    TermPoolBal.poolRidT_of \
    TermPoolBal.poolBalP_of \
    TermPoolBal.poolKnetP_of \
    TermPoolBal.poolRidP_of; do
  if ! echo "$r4_termpoolbal_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolBal.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolSplit.lean ---------------------------------------------------------
# R4 route: new module.
echo "building TermPoolSplit.lean ..."
if ! r4_termpoolsplit_out=$(leanb TermPoolSplit 2>&1); then
  echo "$r4_termpoolsplit_out"
  echo 'FAIL: TermPoolSplit.lean does not compile.'
  fail=1
fi
case "$r4_termpoolsplit_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolSplit.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolSplit.nsum_split \
    TermPoolSplit.plStep_split; do
  if ! echo "$r4_termpoolsplit_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolSplit.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolBalP.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermPoolBalP.lean ..."
if ! r4_termpoolbalp_out=$(leanb TermPoolBalP 2>&1); then
  echo "$r4_termpoolbalp_out"
  echo 'FAIL: TermPoolBalP.lean does not compile.'
  fail=1
fi
case "$r4_termpoolbalp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolBalP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolBalP.keyT_poolP \
    TermPoolBalP.poolBalTP_of \
    TermPoolBalP.poolKnetTP_of \
    TermPoolBalP.poolRidTP_of; do
  if ! echo "$r4_termpoolbalp_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolBalP.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnNet.lean ---------------------------------------------------------------
# ownNet as a theorem (B2).
echo "building TermOwnNet.lean ..."
if ! townnet_out=$(leanb TermOwnNet 2>&1); then
  echo "$townnet_out"
  echo 'FAIL: TermOwnNet.lean does not compile.'
  fail=1
fi
case "$townnet_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnNet.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in pSumAt_own_zero ownNet_of ownNet_one; do
  if ! echo "$townnet_out" | grep -qE "'TermOwnNet.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnNet.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnPub.lean ---------------------------------------------------------------
# ownKeyOwn / ownPub SysInvN clauses: step lemmas (B2).
echo "building TermOwnPub.lean ..."
if ! townpub_out=$(leanb TermOwnPub 2>&1); then
  echo "$townpub_out"
  echo 'FAIL: TermOwnPub.lean does not compile.'
  fail=1
fi
case "$townpub_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnPub.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ownKeyOwn_thread ownPub_thread ownKeyOwn_prom ownPub_prom; do
  if ! echo "$townpub_out" | grep -qE "'TermOwnPub.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnPub.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermB5.lean --------------------------------------------------------
# B5: newPair (N14) and newForeignTyped (N13) discharged (TermB5.newPair_of, newForeignTyped_of).
echo "building TermB5.lean ..."
if ! tb5_out=$(leanb TermB5 2>&1); then
  echo "$tb5_out"
  echo 'FAIL: TermB5.lean does not compile.'
  fail=1
fi
case "$tb5_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermB5.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in tstep_newR ptr_targetI unitsOp_uaI tstep_newPosR twoAt_twoAtT initR_of_iniAt tctx_newPosR newPair_of newForeignTyped_of promNoTwoOK_init promNoTwoOK_promise promNoTwoOK_thread promNoTwoPost_of; do
  if ! echo "$tb5_out" | grep -qE "'TermB5.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermB5.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermBiiF.lean --------------------------------------------------------------
# (BII v3) new module.
echo "building TermBiiF.lean ..."
if ! g278_termbiif_out=$(leanb TermBiiF 2>&1); then
  echo "$g278_termbiif_out"
  echo 'FAIL: TermBiiF.lean does not compile.'
  fail=1
fi
case "$g278_termbiif_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBiiF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermBiiF.bufInit_uaIP \
    TermBiiF.promIniGenB \
    TermBiiF.bufInitIniF_of; do
  if ! echo "$g278_termbiif_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBiiF.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPromPred.lean --------------------------------------------------------
# promPred weakened to the epoch case (TermNoHold.PromPredE); dwf via dwf_ofE.
echo "building TermPromPred.lean ..."
if ! tpp_out=$(leanb TermPromPred 2>&1); then
  echo "$tpp_out"
  echo 'FAIL: TermPromPred.lean does not compile.'
  fail=1
fi
case "$tpp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPromPred.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in promPred_weaken; do
  if ! echo "$tpp_out" | grep -qE "'TermPromPred.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPromPred.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermCohLe.lean -----------------------------------------------------------
# cohle: ownCohLe (narrowed) from OwnCohInv (field ownCohInv), wp + certRunT from certRunC;
# T8 rmw slot form NoPlantRMWS (rmwS_of, from the residual RmwPubF; adopted after (H)).
echo "building TermCohLe.lean ..."
if ! tcohle_out=$(leanb TermCohLe 2>&1); then
  echo "$tcohle_out"
  echo 'FAIL: TermCohLe.lean does not compile.'
  fail=1
fi
case "$tcohle_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCohLe.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in tstep_appAll tstep_newLe CellOK_len cohLe_core ownCohInv_step ownCohLe_of ownCohInvT_step OwnCohInv_mono OwnCohInv_coh0 certRunT_of flipOK_congr wp_of iniWr_of_iniAt refIniWr wordRef_iniWr rmwS_core noPlantRMWS_congr rmwS_of; do
  if ! echo "$tcohle_out" | grep -qE "'TermCohLe.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermCohLe.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermCertScope.lean ---------------------------------------------------------------
# Scope half of certRunC/certRun via endCx (iv) (B5).
echo "building TermCertScope.lean ..."
if ! tcsc_out=$(leanb TermCertScope 2>&1); then
  echo "$tcsc_out"
  echo 'FAIL: TermCertScope.lean does not compile.'
  fail=1
fi
case "$tcsc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCertScope.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermCertScope.lean (extern steps under outstanding promises): std axioms only
for thm in TermCertScope.drf_ext; do
  if ! echo "$tcsc_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermCertScope.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in solo_drf scopeD_of scopeAt_of certScopeC_of certScopeP_of certRunC_of certRunP_of; do
  if ! echo "$tcsc_out" | grep -qE "'TermCertScope.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermCertScope.$thm missing or uses non-standard axioms"
    fail=1
  fi
done
# (D+) theorems added to TermCertScope.lean.
for thm in \
    TermCertScope.certWinC_of_N \
    TermCertScope.certWinP_of_N; do
  if ! echo "$tcsc_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermCertScope.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnX2.lean ---------------------------------------------------------------
echo "building TermOwnX2.lean ..."
if ! townx2_out=$(leanb TermOwnX2 2>&1); then
  echo "$townx2_out"
  echo 'FAIL: TermOwnX2.lean does not compile.'
  fail=1
fi
case "$townx2_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnX2.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermOwnX2.lean (extern steps under outstanding promises): std axioms only
for thm in TermOwnX2.ownXLe_ext; do
  if ! echo "$townx2_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnX2.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in anchR_gen anchStep_same wrHyp run_ind_win OwnXLe.mono OwnXLe.use_ne ownXLe_start ownXLe_start_pub valOfR_own_zero cellOKR_own_zero heldEntry_pfr_own_zero memHeldOn_pfr_own_zero memHeldS_own_zero memHeld_own_priv proj_own_le proj_own_le4 memHeld_priv_le cut_sto_ne stoNIE_cut stoNIE_efoot thInvRE_ext ownXLe_run exprPkg_cases ownXStepT_of_pkgs; do
  if ! echo "$townx2_out" | grep -qE "'TermOwnX2.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnX2.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermRiniCohW.lean ----------------------------------------------------------
# ((i') riniCoh+frlt) new module.
echo "building TermRiniCohW.lean ..."
if ! g285_termrinicohw_out=$(leanb TermRiniCohW 2>&1); then
  echo "$g285_termrinicohw_out"
  echo 'FAIL: TermRiniCohW.lean does not compile.'
  fail=1
fi
case "$g285_termrinicohw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermRiniCohW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermRiniCohW.riniCoh_thread; do
  if ! echo "$g285_termrinicohw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermRiniCohW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnHeldQ.lean ---------------------------------------------------------------
echo "building TermOwnHeldQ.lean ..."
if ! townheldq_out=$(leanb TermOwnHeldQ 2>&1); then
  echo "$townheldq_out"
  echo 'FAIL: TermOwnHeldQ.lean does not compile.'
  fail=1
fi
case "$townheldq_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnHeldQ.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in heldEntry_eqs memHeldOn_eqs memHeldOn_split memHeldOn_move memHeldOn_focus memHeldOn_unfocus memHeldOn_off heldEntry_tr memHeldOn_tr memHeldOn_store ownXStepPkg_of_local ownXStepL_of heldStoreAtP; do
  if ! echo "$townheldq_out" | grep -qE "'TermOwnHeldQ.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnHeldQ.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPubW.lean ---------------------------------------------------------------
echo "building TermPubW.lean ..."
if ! tpubw_out=$(leanb TermPubW 2>&1); then
  echo "$tpubw_out"
  echo 'FAIL: TermPubW.lean does not compile.'
  fail=1
fi
case "$tpubw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPubW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in MemInv_publish0 MemInv_publishW EFoot.weak EFootW.riniW EFootW_pub ThInvMF.weak ThInvMCFS.weak PubWinT3_of tstepM_publishW tstepMR_publishW tstepMC_publishW Foot.weak FootW_ext cNXW ThInvMCFSW.toF tstepMF_stepW tstep_footprintW tstepMCF_stepLW tstepMCF_stepW tstep_footprintMCW; do
  if ! echo "$tpubw_out" | grep -qE "'TermStep.$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStep.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermFreshArr.lean (G1a) -----------------------------------------------------
# G1a: the FreshArr conjunct of ThInvMFA along tstepMF_stepW (tstepMF_stepWFA, tstep_footprintWFA).
echo "building TermFreshArr.lean ..."
if ! tfresharr_out=$(leanb TermFreshArr 2>&1); then
  echo "$tfresharr_out"
  echo 'FAIL: TermFreshArr.lean does not compile.'
  fail=1
fi
case "$tfresharr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFreshArr.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermStep.FreshArr_vac TermStep.ThInvMFA.weakA TermStep.ThInvMFWA.toW TermStep.tstepMF_stepWFA TermStep.tstep_footprintWFA; do
  if ! echo "$tfresharr_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnK1.lean ---------------------------------------------------------------
echo "building TermOwnK1.lean ..."
if ! townk1_out=$(leanb TermOwnK1 2>&1); then
  echo "$townk1_out"
  echo 'FAIL: TermOwnK1.lean does not compile.'
  fail=1
fi
case "$townk1_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnK1.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in scopeR_of_pkg1 memHeldP_promSt totStep_own_le stoNIE_efootW stoNIE_footW ownXStep_k1 ownXStepP_all; do
  if ! echo "$townk1_out" | grep -qE "'TermOwnK1.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnK1.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnK2.lean ---------------------------------------------------------------
echo "building TermOwnK2.lean ..."
if ! townk2_out=$(leanb TermOwnK2 2>&1); then
  echo "$townk2_out"
  echo 'FAIL: TermOwnK2.lean does not compile.'
  fail=1
fi
case "$townk2_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnK2.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in k2_loadOwn k2_loadLoc k2_loadAt k2_loadAtF k2_loadPub k2_loadPubLoc k2_loadWordOwn k2_loadWordPub k2_loadWordLoc k2_storeOwn k2_storeLoc k2_storePub k2_storePubLoc k2_xchgOwn k2_xchgLoc k2_storeWordAny ownXStep_k2; do
  if ! echo "$townk2_out" | grep -qE "'TermOwnK2.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnK2.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnK3.lean ---------------------------------------------------------------
echo "building TermOwnK3.lean ..."
if ! townk3_out=$(leanb TermOwnK3 2>&1); then
  echo "$townk3_out"
  echo 'FAIL: TermOwnK3.lean does not compile.'
  fail=1
fi
case "$townk3_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnK3.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ownXStep_k3 ownXStepL_k3 ownXStep_k3_of heldBufInitP stepK3_ldl stepK3_ldlw stepK3_xchgAt stepK3_xchgAtF stepK3_stlw stepK3_stl stepK3_bufInit stepK3_new stepK3_newBuf oldValF privOff heldBufInitF ownXStepL_bufInit ownXStepL_xchgAt ownXStepL_xchgAtF ownXStepL_stl ownXStepL_stlw ownXStepL_ldl ownXStepL_ldlw ownXStepL_new ownXStepL_newBuf; do
  if ! echo "$townk3_out" | grep -qE "'TermOwnK3.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnK3.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnK4.lean ---------------------------------------------------------------
echo "building TermOwnK4.lean ..."
if ! townk4_out=$(leanb TermOwnK4 2>&1); then
  echo "$townk4_out"
  echo 'FAIL: TermOwnK4.lean does not compile.'
  fail=1
fi
case "$townk4_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnK4.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in tgt_frame pub_step pubBuf_step memHeldP_shrink tgt_publish ownXPub1 mkWord_step mkWord2_step mkEPair_step tgt_easy ownXStep_k4 totStep_own_le ownXLe_of_src tgt_same tgt_pstore tgt_stp tgt_rmw tgt_fetch tgt_cas tgt_casp memHeldP_box tgt_box inlB_out inrB_out inlBB_out inrBB_out caseArmNB_out caseArmB_out caseB_out tgt_inl tgt_inr tgt_case; do
  if ! echo "$townk4_out" | grep -qE "'TermOwnK4.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnK4.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnK5.lean ---------------------------------------------------------------
echo "building TermOwnK5.lean ..."
if ! townk5_out=$(leanb TermOwnK5 2>&1); then
  echo "$townk5_out"
  echo 'FAIL: TermOwnK5.lean does not compile.'
  fail=1
fi
case "$townk5_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnK5.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in winQC winQP ownXStepT_all ownXLe_pub_chain ownXLe_pub_noOwnUse ownXLe0_run_noOwnUse ownXLe0_prom_noOwnUse sw_bufInit_label bufInit_ne_of_use bufInitIniF_pub bufInitIniT_pub; do
  if ! echo "$townk5_out" | grep -qE "'TermOwnK5.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnK5.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermRmw.lean ---------------------------------------------------------------
# rmw discharged from the scope and MemInv (OwnHidP); no run fact (B5, N2).
echo "building TermRmw.lean ..."
if ! trmw_out=$(leanb TermRmw 2>&1); then
  echo "$trmw_out"
  echo 'FAIL: TermRmw.lean does not compile.'
  fail=1
fi
case "$trmw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermRmw.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in rmw_mode rmw_ref noPlantRMW_core noPlantRMW_congr rmw_of; do
  if ! echo "$trmw_out" | grep -qE "'TermRmw.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermRmw.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPromStep.lean ----------------------------------------------------------
# hwu/hfw (P1/P1prime) discharged; HWU/HFW at the cut (CE eta = E).
echo "building TermPromStep.lean ..."
if ! tps_out=$(leanb TermPromStep 2>&1); then
  echo "$tps_out"
  echo 'FAIL: TermPromStep.lean does not compile.'
  fail=1
fi
case "$tps_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPromStep.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in firstW_of_exists lastMsg undef_nwordOK_one firstW_core prom_oneAt hfw_of hwu_of allocG_of; do
  if ! echo "$tps_out" | grep -qE "'TermPromStep.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPromStep.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermBNamed.lean ------------------------------------------------------------
# bnamedT (T18) discharged: GBoxNamed after a thread step.
echo "building TermBNamed.lean ..."
if ! tbn_out=$(leanb TermBNamed 2>&1); then
  echo "$tbn_out"
  echo 'FAIL: TermBNamed.lean does not compile.'
  fail=1
fi
case "$tbn_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBNamed.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in tstep_wrV evalOp_wrV zeroWords_nv vr_named projNV_use termWOK_of bnamedT_of; do
  if ! echo "$tbn_out" | grep -qE "'TermBNamed.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermBNamed.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermBoxOwn.lean ---------------------------------------------------------------
# Box clauses: thread/promise-step preservation.
echo "building TermBoxOwn.lean ..."
if ! tboxo_out=$(leanb TermBoxOwn 2>&1); then
  echo "$tboxo_out"
  echo 'FAIL: TermBoxOwn.lean does not compile.'
  fail=1
fi
case "$tboxo_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBoxOwn.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in vr_boxPay vr_boxPayT projNV_useA termWOK_cut newBoxOwn_of boxStoT_of payOwnT_of payOwn_egP boxFrLe_egP boxFrOwnT_of boxFrLeT_of boxFrOwn_promise; do
  if ! echo "$tboxo_out" | grep -qE "'TermBoxOwn.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermBoxOwn.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermVwrLt.lean ---------------------------------------------------------------
# tstep vWr bound.
echo "building TermVwrLt.lean ..."
if ! tvwl_out=$(leanb TermVwrLt 2>&1); then
  echo "$tvwl_out"
  echo 'FAIL: TermVwrLt.lean does not compile.'
  fail=1
fi
case "$tvwl_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermVwrLt.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in tstep_vWrLt VWrLt_init VWrLt_promise VWrLtT_of BoxFrLt_init BoxFrLt_promise boxFrLtT_of; do
  if ! echo "$tvwl_out" | grep -qE "'TermVwrLt.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermVwrLt.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermWin.lean ---------------------------------------------------------------
# win (T6) discharged: PubWinT at the step's typing (CertRunC at the stepping configuration).
echo "building TermWin.lean ..."
if ! twn_out=$(leanb TermWin 2>&1); then
  echo "$twn_out"
  echo 'FAIL: TermWin.lean does not compile.'
  fail=1
fi
case "$twn_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermWin.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in winM_of; do
  if ! echo "$twn_out" | grep -qE "'TermWin.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermWin.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantH.lean ---------------------------------------------------------------
# selfPlantRest narrowed to SelfPlantRestHF = R1 (affine, (H) proper) or R2prime (ill-formed mu).
echo "building TermPlantH.lean ..."
if ! tplh_out=$(leanb TermPlantH 2>&1); then
  echo "$tplh_out"
  echo 'FAIL: TermPlantH.lean does not compile.'
  fail=1
fi
case "$tplh_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantH.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in Np_le_slot hclass_of selfPlantRest_of; do
  if ! echo "$tplh_out" | grep -qE "'TermPlantH.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantH.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermW2Core.lean ---------------------------------------------------------------
# w2: splice/rebuild core.
echo "building TermW2Core.lean ..."
if ! tw2c_out=$(leanb TermW2Core 2>&1); then
  echo "$tw2c_out"
  echo 'FAIL: TermW2Core.lean does not compile.'
  fail=1
fi
case "$tw2c_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermW2Core.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in splice1_get splice_unit oneAt_of_noTwoT rebuild; do
  if ! echo "$tw2c_out" | grep -qE "'W2Core.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: W2Core.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermW2Pub.lean ---------------------------------------------------------------
# w2: PubWordWF proved.
echo "building TermW2Pub.lean ..."
if ! tw2u_out=$(leanb TermW2Pub 2>&1); then
  echo "$tw2u_out"
  echo 'FAIL: TermW2Pub.lean does not compile.'
  fail=1
fi
case "$tw2u_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermW2Pub.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in pubWordW_of; do
  if ! echo "$tw2u_out" | grep -qE "'W2Pub.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: W2Pub.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermW2Prom.lean ---------------------------------------------------------------
# w2: PromWordWF from PromWordNewF.
echo "building TermW2Prom.lean ..."
if ! tw2p_out=$(leanb TermW2Prom 2>&1); then
  echo "$tw2p_out"
  echo 'FAIL: TermW2Prom.lean does not compile.'
  fail=1
fi
case "$tw2p_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermW2Prom.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in promWordW_of; do
  if ! echo "$tw2p_out" | grep -qE "'W2Prom.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: W2Prom.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermW2New.lean ---------------------------------------------------------------
# w2: PromWordNewF proved.
echo "building TermW2New.lean ..."
if ! tw2n_out=$(leanb TermW2New 2>&1); then
  echo "$tw2n_out"
  echo 'FAIL: TermW2New.lean does not compile.'
  fail=1
fi
case "$tw2n_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermW2New.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in solo_mem wordOK_seg assembleSlot promWordNew_of; do
  if ! echo "$tw2n_out" | grep -qE "'W2New.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: W2New.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantW2.lean ---------------------------------------------------------------
# w2 discharged: field removed.
echo "building TermPlantW2.lean ..."
if ! tpw2_out=$(leanb TermPlantW2 2>&1); then
  echo "$tpw2_out"
  echo 'FAIL: TermPlantW2.lean does not compile.'
  fail=1
fi
case "$tpw2_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantW2.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in plantInhW_of plantInh_ofP promWordW_of pubWordW_of; do
  if ! echo "$tpw2_out" | grep -qE "'TermPlantW2.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantW2.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermStepPred.lean ---------------------------------------------------------------
# promPred; PubStorePred discharged (B5).
echo "building TermStepPred.lean ..."
if ! tspr_out=$(leanb TermStepPred 2>&1); then
  echo "$tspr_out"
  echo 'FAIL: TermStepPred.lean does not compile.'
  fail=1
fi
case "$tspr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermStepPred.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in stepPredNumX_of certified_promPredEX promPredTX promPred_of; do
  if ! echo "$tspr_out" | grep -qE "'TermStepPred.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermStepPred.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPredHoldW.lean ---------------------------------------------------------------
# BH2prime from PredHoldG: bh2_of.
echo "building TermPredHoldW.lean ..."
if ! tphw_out=$(leanb TermPredHoldW 2>&1); then
  echo "$tphw_out"
  echo 'FAIL: TermPredHoldW.lean does not compile.'
  fail=1
fi
case "$tphw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPredHoldW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in bufInit_ownNP bh2_of; do
  if ! echo "$tphw_out" | grep -qE "'TermPredHoldW.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPredHoldW.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermZwIniP.lean ---------------------------------------------------------------
# zwIni preservation at promise steps / plants.
echo "building TermZwIniP.lean ..."
if ! tzwip_out=$(leanb TermZwIniP 2>&1); then
  echo "$tzwip_out"
  echo 'FAIL: TermZwIniP.lean does not compile.'
  fail=1
fi
case "$tzwip_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermZwIniP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in promIniE_cut bufInit_notPubd zwIni_plantG plantN_zw zwIni_prom zwIni_EgT; do
  if ! echo "$tzwip_out" | grep -qE "'TermZwIniP.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermZwIniP.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermUndefInv.lean ---------------------------------------------------------------
# SysInvN undefAt: preservation (B2, U243).
echo "building TermUndefInv.lean ..."
if ! tundi_out=$(leanb TermUndefInv 2>&1); then
  echo "$tundi_out"
  echo 'FAIL: TermUndefInv.lean does not compile.'
  fail=1
fi
case "$tundi_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermUndefInv.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in undefAtG_ext undefAtG_empty undefAtG_prom undefAtG_post undefAtG_thread undefAt_cut; do
  if ! echo "$tundi_out" | grep -qE "'TermUndefInv.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermUndefInv.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCoh.lean ---------------------------------------------------------------
# SysInvN ownCoh (N16, formerly ownCohInv).
echo "building TermOwnCoh.lean ..."
if ! towc_out=$(leanb TermOwnCoh 2>&1); then
  echo "$towc_out"
  echo 'FAIL: TermOwnCoh.lean does not compile.'
  fail=1
fi
case "$towc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCoh.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ownCoh_seen ownCoh_gfoot ownCoh_empty ownCoh_sto plantG_pfr_none ownCohZ_iff ownCoh_initW ownCohInvT_of ownCoh_stepper; do
  if ! echo "$towc_out" | grep -qE "'TermOwnCoh.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCoh.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermRunPay.lean ---------------------------------------------------------------
# RunAgreeF from RunAgreeF2 + box clauses (pay retired).
echo "building TermRunPay.lean ..."
if ! trunp_out=$(leanb TermRunPay 2>&1); then
  echo "$trunp_out"
  echo 'FAIL: TermRunPay.lean does not compile.'
  fail=1
fi
case "$trunp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermRunPay.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in plantL_sto runAgreeF_of; do
  if ! echo "$trunp_out" | grep -qE "'TermRunPay.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermRunPay.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPromClos.lean ---------------------------------------------------------------
# promClos (SysInvN, last) + PubClosT from PromAllocF; plantClos -> promAlloc.
echo "building TermPromClos.lean ..."
if ! tpcl_out=$(leanb TermPromClos 2>&1); then
  echo "$tpcl_out"
  echo 'FAIL: TermPromClos.lean does not compile.'
  fail=1
fi
case "$tpcl_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPromClos.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in gfoot_pfr promClos_thread promClos_prom pubClosT_of foreign_priv; do
  if ! echo "$tpcl_out" | grep -qE "'TermPromClos.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPromClos.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPromAlloc.lean ---------------------------------------------------------------
# PromAllocF proved except zeroable fresh cells (PromAllocZF).
echo "building TermPromAlloc.lean ..."
if ! tpal_out=$(leanb TermPromAlloc 2>&1); then
  echo "$tpal_out"
  echo 'FAIL: TermPromAlloc.lean does not compile.'
  fail=1
fi
case "$tpal_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPromAlloc.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in decodeArm_locV encodeArm_locV locPubV_VR ofArm_locV oneAt_lt_acc oneAt_lt_arr oneAt_lt_cellOK promAllocF_of promAlloc_loc promAlloc_val wordOK_locPubV; do
  if ! echo "$tpal_out" | grep -qE "'TermPromAlloc.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPromAlloc.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPlantPair.lean ---------------------------------------------------------------
# plantPair discharged (guarded PlantPairF).
echo "building TermPlantPair.lean ..."
if ! tppr_out=$(leanb TermPlantPair 2>&1); then
  echo "$tppr_out"
  echo 'FAIL: TermPlantPair.lean does not compile.'
  fail=1
fi
case "$tppr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantPair.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in plantPair_of; do
  if ! echo "$tppr_out" | grep -qE "'TermPlantPair.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantPair.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermEnvExt.lean ---------------------------------------------------------------
# Env extension facts for box payload views.
echo "building TermEnvExt.lean ..."
if ! tenvext_out=$(leanb TermEnvExt 2>&1); then
  echo "$tenvext_out"
  echo 'FAIL: TermEnvExt.lean does not compile.'
  fail=1
fi
case "$tenvext_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermEnvExt.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in tstep_env_ext mem_ol enter_nalloc; do
  if ! echo "$tenvext_out" | grep -qE "'TermEnvExt.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermEnvExt.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermBoxPV.lean ---------------------------------------------------------------
# boxPVT discharged.
echo "building TermBoxPV.lean ..."
if ! tboxpv_out=$(leanb TermBoxPV 2>&1); then
  echo "$tboxpv_out"
  echo 'FAIL: TermBoxPV.lean does not compile.'
  fail=1
fi
case "$tboxpv_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBoxPV.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in boxPV_thread; do
  if ! echo "$tboxpv_out" | grep -qE "'TermBoxPV.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermBoxPV.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermRunPayT.lean ---------------------------------------------------------------
# RunAgree thread-step part.
echo "building TermRunPayT.lean ..."
if ! trpt_out=$(leanb TermRunPayT 2>&1); then
  echo "$trpt_out"
  echo 'FAIL: TermRunPayT.lean does not compile.'
  fail=1
fi
case "$trpt_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermRunPayT.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in runAgreeT_of runAgreeFT2_of; do
  if ! echo "$trpt_out" | grep -qE "'TermRunPayT.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermRunPayT.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermLocal.lean ----------------------------------------------------------
# Liveness L5: soundness of the `local` window check. Robust.walk (structural)
# is sound for WinW (checkProgL_window: accepts (checkProgL p) gives WinW); a thread that entered a
# window stays in it, on its entry stack, with the token binding in its env,
# until the leaving store (local_confined), within esize body own steps
# (local_bounded_release). Hypothesis Follows: the machine never takes an arm
# the checker typed without the token.
echo "building TermLocal.lean ..."
if ! tloc_out=$(leanb TermLocal 2>&1); then
  echo "$tloc_out"
  echo 'FAIL: TermLocal.lean does not compile: the local-window soundness no longer goes through.'
  fail=1
fi
case "$tloc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermLocal.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in tstep_shape tstep_cas walkT_sound localDeclT_sound winW_let inWin_enter local_confined local_bounded_release checkProgL_window; do
  if ! echo "$tloc_out" | grep -qE "'TermLocal.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermLocal.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermPlantWin.lean ---------------------------------------------------------------
# BH1 from the zwIni clause: bh1_of.
echo "building TermPlantWin.lean ..."
if ! tpwin_out=$(leanb TermPlantWin 2>&1); then
  echo "$tpwin_out"
  echo 'FAIL: TermPlantWin.lean does not compile.'
  fail=1
fi
case "$tpwin_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantWin.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in plantMax_create storeUnits_first_ful storeUnits_two_grow bufInit_tstep_ful IniR_nil VR_nil_congr inhZ_of_envVal bh1_of; do
  if ! echo "$tpwin_out" | grep -qE "'TermPlantWin.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPlantWin.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnG0W.lean ---------------------------------------------------------------
# G-b.
echo "building TermOwnG0W.lean ..."
if ! towng0w_out=$(leanb TermOwnG0W 2>&1); then
  echo "$towng0w_out"
  echo 'FAIL: TermOwnG0W.lean does not compile.'
  fail=1
fi
case "$towng0w_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnG0W.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in G0WinW_of_G0Win g0WinW_of_g0Win; do
  if ! echo "$towng0w_out" | grep -qE "'TermOwnG0W.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnG0W.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermGbLp.lean ---------------------------------------------------------------
# G-b.
echo "building TermGbLp.lean ..."
if ! tgblp_out=$(leanb TermGbLp 2>&1); then
  echo "$tgblp_out"
  echo 'FAIL: TermGbLp.lean does not compile.'
  fail=1
fi
case "$tgblp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermGbLp.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in bufCap_of iniLp_of capNAt_of; do
  if ! echo "$tgblp_out" | grep -qE "'TermGbLp.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermGbLp.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermK5Lp.lean ---------------------------------------------------------------
# S1b (iv): iniLp_ofV.
echo "building TermK5Lp.lean ..."
if ! tk5lp_out=$(leanb TermK5Lp 2>&1); then
  echo "$tk5lp_out"
  echo 'FAIL: TermK5Lp.lean does not compile.'
  fail=1
fi
case "$tk5lp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK5Lp.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in iniLp_ofV; do
  if ! echo "$tk5lp_out" | grep -qE "'TermK5Lp.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermK5Lp.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnG0.lean ---------------------------------------------------------------
# G-b.
echo "building TermOwnG0.lean ..."
if ! towng0_out=$(leanb TermOwnG0 2>&1); then
  echo "$towng0_out"
  echo 'FAIL: TermOwnG0.lean does not compile.'
  fail=1
fi
case "$towng0_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnG0.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermOwnG0.lean (extern steps under outstanding promises): std axioms only
for thm in TermOwnG0.soloNP_snoc_ext; do
  if ! echo "$towng0_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnG0.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in soloNP_snoc_thread soloNP_snoc_prom memT memB noFulT noFul winLe_cert g0WinT_of g0Win_of; do
  if ! echo "$towng0_out" | grep -qE "'TermOwnG0.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnG0.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOwnG0P.lean ---------------------------------------------------------------
# gb2: PfrX discharged via the ghost G.pf (needs the TermPf / EFoot tags).
echo "building TermOwnG0P.lean ..."
if ! towng0p_out=$(leanb TermOwnG0P 2>&1); then
  echo "$towng0p_out"
  echo 'FAIL: TermOwnG0P.lean does not compile.'
  fail=1
fi
case "$towng0p_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnG0P.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermOwnG0P.lean (extern steps under outstanding promises): std axioms only
for thm in TermOwnG0.invAtXRB_ext; do
  if ! echo "$towng0p_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnG0P.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in soloNP_trans runNP_inv invAtXRB_prom solo_typedXRP PfrX_of g0WinT_ofP g0Win_ofP; do
  if ! echo "$towng0p_out" | grep -qE "'TermOwnG0.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermOwnG0.$thm (TermOwnG0P) missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermRunLoc.lean ---------------------------------------------------------------
# RunAgree residual iniOwn, RunAgreeFT4.
echo "building TermRunLoc.lean ..."
if ! trloc_out=$(leanb TermRunLoc 2>&1); then
  echo "$trloc_out"
  echo 'FAIL: TermRunLoc.lean does not compile.'
  fail=1
fi
case "$trloc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermRunLoc.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in runAgreeW2_of runAgreeF2_of runAgreeT2_of runAgreeFT3_of runAgreeW3_of_iniLoc plantRoot runAgreeW3Z_of_G runAgreeF3_of_old runAgreeFT4_old_imp_new rootH0P runAgreeF3_of_gb runAgreeFT4_gb_imp_new runAgreeW3Z_of_K runAgreeF3_of_gb2 runAgreeFT4_gb2_imp_new; do
  if ! echo "$trloc_out" | grep -qE "'TermRunLoc.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermRunLoc.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPredStoreFree.lean ---------------------------------------------------------------
# ownPredStoreFree discharged.
echo "building TermPredStoreFree.lean ..."
if ! tpsf_out=$(leanb TermPredStoreFree 2>&1); then
  echo "$tpsf_out"
  echo 'FAIL: TermPredStoreFree.lean does not compile.'
  fail=1
fi
case "$tpsf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPredStoreFree.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in ownPredStoreFree_of; do
  if ! echo "$tpsf_out" | grep -qE "'TermPredStoreFree.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermPredStoreFree.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPubCons.lean -----------------------------------------------------------
# Pool cover (routeb).
echo "building TermPubCons.lean ..."
if ! g265_pubcons_out=$(leanb TermPubCons 2>&1); then
  echo "$g265_pubcons_out"
  echo 'FAIL: TermPubCons.lean does not compile.'
  fail=1
fi
case "$g265_pubcons_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPubCons.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPubCons.pubCons_iff TermPubCons.pubAt_consume; do
  if ! echo "$g265_pubcons_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermMsgWords.lean ----------------------------------------------------------
# Pool cover (msgwords).
echo "building TermMsgWords.lean ..."
if ! g265_msgwords_out=$(leanb TermMsgWords 2>&1); then
  echo "$g265_msgwords_out"
  echo 'FAIL: TermMsgWords.lean does not compile.'
  fail=1
fi
case "$g265_msgwords_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermMsgWords.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermMsgWords.wordOK_inWords TermMsgWords.role_inWords TermMsgWords.msgWords_thread TermMsgWords.promWords_of TermMsgWords.msgWords_prom TermMsgWords.msgInCell_of; do
  if ! echo "$g265_msgwords_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermUndefLow.lean ----------------------------------------------------------
# Pool cover (undefLow).
echo "building TermUndefLow.lean ..."
if ! g265_undeflow_out=$(leanb TermUndefLow 2>&1); then
  echo "$g265_undeflow_out"
  echo 'FAIL: TermUndefLow.lean does not compile.'
  fail=1
fi
case "$g265_undeflow_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermUndefLow.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermUndefLow.inAcc_single_oneAt TermUndefLow.two_not_oneU TermUndefLow.onePc_oneU TermUndefLow.storeUnits_newInj TermUndefLow.newOrd_alloc TermUndefLow.newOrd_allocBuf TermUndefLow.newOrd_rmw TermUndefLow.newOrd_rmwPair TermUndefLow.newOrd_projInj TermUndefLow.evalOp_newOrd TermUndefLow.tstep_newOrd TermUndefLow.storeUnits_newV TermUndefLow.evalOp_newV TermUndefLow.tstep_newV; do
  if ! echo "$g265_undeflow_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermUndefLowF.lean ---------------------------------------------------------
# Pool cover (undefLow).
echo "building TermUndefLowF.lean ..."
if ! g265_undeflowf_out=$(leanb TermUndefLowF 2>&1); then
  echo "$g265_undeflowf_out"
  echo 'FAIL: TermUndefLowF.lean does not compile.'
  fail=1
fi
case "$g265_undeflowf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermUndefLowF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermUndefLow.fetch_new_core TermUndefLow.fetch_new_num; do
  if ! echo "$g265_undeflowf_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermUndefLowT.lean ---------------------------------------------------------
# Pool cover (undefLow).
echo "building TermUndefLowT.lean ..."
if ! g265_undeflowt_out=$(leanb TermUndefLowT 2>&1); then
  echo "$g265_undeflowt_out"
  echo 'FAIL: TermUndefLowT.lean does not compile.'
  fail=1
fi
case "$g265_undeflowt_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermUndefLowT.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermUndefLow.tstep_newUndef TermUndefLow.undefLow_thread TermUndefLow.undefLow_prom; do
  if ! echo "$g265_undeflowt_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOverCr5.lean -----------------------------------------------------------
# Pool cover (opgQ sidecar).
echo "building TermOverCr5.lean ..."
if ! g265_overcr5_out=$(leanb TermOverCr5 2>&1); then
  echo "$g265_overcr5_out"
  echo 'FAIL: TermOverCr5.lean does not compile.'
  fail=1
fi
case "$g265_overcr5_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCr5.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermOverCr5.fulfil_low TermOverCr5.crItem_keep TermOverCr5.overCr_ownop TermOverCr5.covU_keep TermOverCr5.covU_of_initR TermOverCr5.overCr_ownopR; do
  if ! echo "$g265_overcr5_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrW.lean -----------------------------------------------------------
# Pool cover (opgQ sidecar).
echo "building TermOverCrW.lean ..."
if ! g265_overcrw_out=$(leanb TermOverCrW 2>&1); then
  echo "$g265_overcrw_out"
  echo 'FAIL: TermOverCrW.lean does not compile.'
  fail=1
fi
case "$g265_overcrw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermOverCrW.winG_back TermOverCrW.gd_itemW TermOverCrW.gd_itemWQ TermOverCrW.winG_sibling_false TermOverCrW.wa_old_over TermOverCrW.hcovN_of TermOverCrW.witB_of_witH TermOverCrW.witH_keep TermOverCrW.crItem_merge TermOverCrW.overCr_interfM TermOverCrW.upgrade_of TermOverCrW.target_eq_holder; do
  if ! echo "$g265_overcrw_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPromAboveG.lean --------------------------------------------------------
# Pool cover (promAbove): PromAboveG along Step.
echo "building TermPromAboveG.lean ..."
if ! g265_promaboveg_out=$(leanb TermPromAboveG 2>&1); then
  echo "$g265_promaboveg_out"
  echo 'FAIL: TermPromAboveG.lean does not compile.'
  fail=1
fi
case "$g265_promaboveg_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPromAboveG.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPromAboveG.promAboveG_Step TermPromAboveG.promAboveG_noProm; do
  if ! echo "$g265_promaboveg_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermPtrRts.lean ------------------------------------------------------------
# p265b (promInCut_bII).
echo "building TermPtrRts.lean ..."
if ! g265_ptrrts_out=$(leanb TermPtrRts 2>&1); then
  echo "$g265_ptrrts_out"
  echo 'FAIL: TermPtrRts.lean does not compile.'
  fail=1
fi
case "$g265_ptrrts_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPtrRts.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermPtrStab.lean -----------------------------------------------------------
# p265b + promInCut_bII: PromInCut, nonPromLbl_of.
echo "building TermPtrStab.lean ..."
if ! g265_ptrstab_out=$(leanb TermPtrStab 2>&1); then
  echo "$g265_ptrstab_out"
  echo 'FAIL: TermPtrStab.lean does not compile.'
  fail=1
fi
case "$g265_ptrstab_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPtrStab.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermFgnClos.lean -----------------------------------------------------------
# FgnPromClosG discharge (fgnClos_*).
echo "building TermFgnClos.lean ..."
if ! g265_fgnclos_out=$(leanb TermFgnClos 2>&1); then
  echo "$g265_fgnclos_out"
  echo 'FAIL: TermFgnClos.lean does not compile.'
  fail=1
fi
case "$g265_fgnclos_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFgnClos.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFgnClos.fgnClos_use TermFgnClos.solo_typedXB TermFgnClos.certified_promTgt TermFgnClos.fgnClos_none TermFgnClos.fgnClos_prom TermFgnClos.fgnClos_thread; do
  if ! echo "$g265_fgnclos_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermCellOwn.lean -----------------------------------------------------------
# CellOwnerLiveM discharge (cellOwn_*).
echo "building TermCellOwn.lean ..."
if ! g265_cellown_out=$(leanb TermCellOwn 2>&1); then
  echo "$g265_cellown_out"
  echo 'FAIL: TermCellOwn.lean does not compile.'
  fail=1
fi
case "$g265_cellown_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCellOwn.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermCellOwn.cellOwn_use TermCellOwn.cellOwn_init TermCellOwn.cellOwn_thread TermCellOwn.cellOwn_prom TermCellOwn.nonPromLbl_ofM; do
  if ! echo "$g265_cellown_out" | grep -qE "'$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermStoreCrZE.lean ----------------------------------------------------------
# the epoch half of ObligationsF.nonEpochFree (ex storeCrZH): StoreCrZ0 from NonEpochFree
# [, PIN-D1b: ObligationsF has no nonEpochFree field any more (TermDwf.storeCrZ_of proves
# StoreCrZ from TermPiece.storeLeafPay_of); this module stays as a library and is still checked.]
# (StoreNI => non-undef predecessor, numeric by PromTyAOK / MemOKP).
echo "building TermStoreCrZE.lean ..."
if ! g270_scze_out=$(leanb TermStoreCrZE 2>&1); then
  echo "$g270_scze_out"
  echo 'FAIL: TermStoreCrZE.lean does not compile.'
  fail=1
fi
case "$g270_scze_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermStoreCrZE.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermStoreCrZE.nonEpochFree_of_storeCrZ0 TermStoreCrZE.VRes_noWord TermStoreCrZE.pred_of_not_initAt TermStoreCrZE.pred_num TermStoreCrZE.storeCrZ0_of_nonEpochFree TermStoreCrZE.storeCrZH_of_nonEpochFree; do
  if ! echo "$g270_scze_out" | grep -qE "'$thm' depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermBiiT.lean --------------------------------------------------------------
# (bufInit rework, items 1+2) the internal BufInitIniT half of the old bufInitIni field, derived
# from BufInitIniF + PfrG.  (BII) ObligationsF has no bufInitIni field: BufInitIniF is
# TermBiiF.bufInitIniF_of.
echo "building TermBiiT.lean ..."
if ! g272_biit_out=$(leanb TermBiiT 2>&1); then
  echo "$g272_biit_out"
  echo 'FAIL: TermBiiT.lean does not compile.'
  fail=1
fi
case "$g272_biit_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBiiT.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermBiiT.bufInitIniT_pfr TermBiiT.bufInitIniT_of; do
  if ! echo "$g272_biit_out" | grep -qE "'$thm' depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]"; then
    echo "FAIL: $thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- OwnFreshW5.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building OwnFreshW5.lean ..."
if ! k1a_ownfreshw5_out=$(leanb OwnFreshW5 2>&1); then
  echo "$k1a_ownfreshw5_out"
  echo 'FAIL: OwnFreshW5.lean does not compile.'
  fail=1
fi
case "$k1a_ownfreshw5_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a OwnFreshW5.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPtrRtsK.ownProm_sto_keep; do
  if ! echo "$k1a_ownfreshw5_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: OwnFreshW5.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermCntLoc.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermCntLoc.lean ..."
if ! k1a_termcntloc_out=$(leanb TermCntLoc 2>&1); then
  echo "$k1a_termcntloc_out"
  echo 'FAIL: TermCntLoc.lean does not compile.'
  fail=1
fi
case "$k1a_termcntloc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCntLoc.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermCntLoc.pubWords_vr TermCntLoc.pubWords_rts TermCntLoc.cnt_prefix TermCntLoc.cnt_window TermCntLoc.cntOK_typed TermCntLoc.cntPairOK_typed; do
  if ! echo "$k1a_termcntloc_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermCntLoc.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootNC.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootNC.lean ..."
if ! k1a_termfootnc_out=$(leanb TermFootNC 2>&1); then
  echo "$k1a_termfootnc_out"
  echo 'FAIL: TermFootNC.lean does not compile.'
  fail=1
fi
case "$k1a_termfootnc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootNC.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFootNC.footNC_sto TermFootNC.footNC_efoot TermFootNC.fenceS_nalloc TermFootNC.ls_nal TermFootNC.evalOp_nalloc TermFootNC.tstep_nalloc TermFootNC.getP TermFootNC.getP_lt TermFootNC.locNC_push TermFootNC.locNC_pushPair TermFootNC.locNC_erase TermFootNC.stepStore_casesP TermFootNC.locNC_storeUnits TermFootNC.locNC_init TermFootNC.layT_of_accs TermFootNC.locNC_alloc TermFootNC.footNC_ofLoc TermFootNC.footNC_alloc; do
  if ! echo "$k1a_termfootnc_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootNC.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootNP.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootNP.lean ..."
if ! k1a_termfootnp_out=$(leanb TermFootNP 2>&1); then
  echo "$k1a_termfootnp_out"
  echo 'FAIL: TermFootNP.lean does not compile.'
  fail=1
fi
case "$k1a_termfootnp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootNP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFootNP.tstepMR_newN TermFootNP.tstepMR_newBufN TermFootNP.liftMRN TermFootNP.tstepMR_inlBN TermFootNP.tstepMR_inrBN TermFootNP.tstepMR_inlBBN TermFootNP.tstepMR_inrBBN TermFootNP.tstepMR_inlTN TermFootNP.tstepMR_inrTN TermFootNP.case_armNBRN TermFootNP.case_armBRN TermFootNP.tstepMR_caseBN TermFootNP.tstepMR_caseTN TermFootNP.locNC_allocBuf TermFootNP.footNC_ofLocS TermFootNP.ThInvMKQ.mono; do
  if ! echo "$k1a_termfootnp_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootNP.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootNF.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootNF.lean ..."
if ! k1a_termfootnf_out=$(leanb TermFootNF 2>&1); then
  echo "$k1a_termfootnf_out"
  echo 'FAIL: TermFootNF.lean does not compile.'
  fail=1
fi
case "$k1a_termfootnf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootNF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFootNF.ThInvMFQ.mono TermFootNF.ThInvMF_congrN TermFootNF.liftN TermFootNF.tstepM_inlN TermFootNF.tstepM_inrN TermFootNF.tstepM_caseN TermFootNF.tstepM_inlBN TermFootNF.tstepM_inrBN TermFootNF.tstepM_inlBBN TermFootNF.tstepM_inrBBN TermFootNF.tstepM_inlTN TermFootNF.tstepM_inrTN TermFootNF.case_armNBN TermFootNF.case_armBN TermFootNF.tstepM_caseBN TermFootNF.tstepM_caseTN TermFootNF.tstepM_newN TermFootNF.tstepM_newBufN; do
  if ! echo "$k1a_termfootnf_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootNF.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootNG.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootNG.lean ..."
if ! k1a_termfootng_out=$(leanb TermFootNG 2>&1); then
  echo "$k1a_termfootng_out"
  echo 'FAIL: TermFootNG.lean does not compile.'
  fail=1
fi
case "$k1a_termfootng_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootNG.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFootNG.tstepMF_stepN TermFootNG.tstep_footprintK_nc; do
  if ! echo "$k1a_termfootng_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootNG.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootBP0.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootBP0.lean ..."
if ! k1a_termfootbp0_out=$(leanb TermFootBP0 2>&1); then
  echo "$k1a_termfootbp0_out"
  echo 'FAIL: TermFootBP0.lean does not compile.'
  fail=1
fi
case "$k1a_termfootbp0_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootBP0.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFootBP0.footBP_of TermFootBP0.footB1_nalloc TermFootBP0.footB1_cons TermFootBP0.freshIn_one TermFootBP0.footB1_box TermFootBP0.nalloc_alloc_boxE TermFootBP0.footB1_new TermFootBP0.footB1_newBuf TermFootBP0.pubAt_eq TermFootBP0.pubAt_not TermFootBP0.pubAt_nopub; do
  if ! echo "$k1a_termfootbp0_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootBP0.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootBPP.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootBPP.lean ..."
if ! k1a_termfootbpp_out=$(leanb TermFootBPP 2>&1); then
  echo "$k1a_termfootbpp_out"
  echo 'FAIL: TermFootBPP.lean does not compile.'
  fail=1
fi
case "$k1a_termfootbpp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootBPP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFootBPP.liftMRNB TermFootBPP.tstepMR_inlBNB TermFootBPP.tstepMR_inrBNB TermFootBPP.tstepMR_inlBBNB TermFootBPP.tstepMR_inrBBNB TermFootBPP.case_armNBRNB TermFootBPP.case_armBRNB TermFootBPP.tstepMR_inlTNB TermFootBPP.tstepMR_inrTNB TermFootBPP.tstepMR_caseBNB TermFootBPP.tstepMR_caseTNB; do
  if ! echo "$k1a_termfootbpp_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootBPP.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootNCB.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootNCB.lean ..."
if ! k1a_termfootncb_out=$(leanb TermFootNCB 2>&1); then
  echo "$k1a_termfootncb_out"
  echo 'FAIL: TermFootNCB.lean does not compile.'
  fail=1
fi
case "$k1a_termfootncb_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootNCB.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFootNCB.footB1_boxFr TermFootNCB.tstepMF_stepNB TermFootNCB.tstep_footprintK_ncB; do
  if ! echo "$k1a_termfootncb_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootNCB.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootNK.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootNK.lean ..."
if ! k1a_termfootnk_out=$(leanb TermFootNK 2>&1); then
  echo "$k1a_termfootnk_out"
  echo 'FAIL: TermFootNK.lean does not compile.'
  fail=1
fi
case "$k1a_termfootnk_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootNK.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFootNK.frame_nalloc TermFootNK.tstepMCF_stepKN TermFootNK.tstepMCF_stepTKA_zfN TermFootNK.mcfs_addFoot TermFootNK.mc_ofKFQ TermFootNK.cNQ TermFootNK.mc_liftFN TermFootNK.mc_liftSN; do
  if ! echo "$k1a_termfootnk_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootNK.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootBPK.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootBPK.lean ..."
if ! k1a_termfootbpk_out=$(leanb TermFootBPK 2>&1); then
  echo "$k1a_termfootbpk_out"
  echo 'FAIL: TermFootBPK.lean does not compile.'
  fail=1
fi
case "$k1a_termfootbpk_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootBPK.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFootBPK.mcfs_addFootB TermFootBPK.mc_liftSNB TermFootBPK.addB1 TermFootBPK.tstepMR_publishB TermFootBPK.tstepMC_publishPB TermFootBPK.tstepMCF_stepKAB TermFootBPK.tstepMCF_stepTKA_zfNB; do
  if ! echo "$k1a_termfootbpk_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootBPK.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# R4 route: theorems added to TermFootBPK.lean.
for thm in \
    TermFootBPK.tstepMCF_stepTKA_zfNBC; do
  if ! echo "$k1a_termfootbpk_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootBPK.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermGranW.lean ------------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermGranW.lean ..."
if ! k1a_termgranw_out=$(leanb TermGranW 2>&1); then
  echo "$k1a_termgranw_out"
  echo 'FAIL: TermGranW.lean does not compile.'
  fail=1
fi
case "$k1a_termgranw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermGranW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermGranW.granuleW_init TermGranW.granuleW_partner TermGranW.granuleW_pushOne TermGranW.granuleW_pushPair TermGranW.granuleW_push_fresh TermGranW.granuleW_pushOne_notTwo TermGranW.granuleW_sto TermGranW.TwoAtT_not_succ TermGranW.OneAt_not_TwoAtT TermGranW.OneAt_not_snd TermGranW.TwoAt_succ_not_TwoAtT TermGranW.granuleW_storeUnits TermGranW.granuleW_storeAt TermGranW.granuleWP_of TermGranW.granuleWP_partner TermGranW.granuleWP_setP TermGranW.granuleWP_fulfil_notTwo TermGranW.granuleWP_promise; do
  if ! echo "$k1a_termgranw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermGranW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- FootNCE.lean --------------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building FootNCE.lean ..."
if ! k1a_footnce_out=$(leanb FootNCE 2>&1); then
  echo "$k1a_footnce_out"
  echo 'FAIL: FootNCE.lean does not compile.'
  fail=1
fi
case "$k1a_footnce_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a FootNCE.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermGranP.lean ------------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermGranP.lean ..."
if ! k1a_termgranp_out=$(leanb TermGranP 2>&1); then
  echo "$k1a_termgranp_out"
  echo 'FAIL: TermGranP.lean does not compile.'
  fail=1
fi
case "$k1a_termgranp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermGranP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermGranP.twoAtT_of_atOff TermGranP.notTwoAtT_of_oneAt TermGranP.granuleWP_nil_iff TermGranP.granuleWP_sto TermGranP.granuleWP_pushOne TermGranP.granuleWP_pushOne_notTwo TermGranP.granuleWP_push_fresh TermGranP.granuleWP_pushPair TermGranP.granuleWP_storeUnits TermGranP.granuleWP_storeUnitsF TermGranP.granuleWP_foldPush TermGranP.granuleWP_alloc TermGranP.granuleWP_allocBuf TermGranP.granuleWP_stepRmw TermGranP.granuleWP_stepRmwPair TermGranP.granuleWP_lift; do
  if ! echo "$k1a_termgranp_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermGranP.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermGranStep.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermGranStep.lean ..."
if ! k1a_termgranstep_out=$(leanb TermGranStep 2>&1); then
  echo "$k1a_termgranstep_out"
  echo 'FAIL: TermGranStep.lean does not compile.'
  fail=1
fi
case "$k1a_termgranstep_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermGranStep.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermGranStep.evalOp_gran TermGranStep.tstep_gran TermGranStep.tstep_granT TermGranStep.granuleW_stepNF TermGranStep.sw_at TermGranStep.granuleWP_toSto TermGranStep.freshOK_of TermGranStep.granuleWP_step TermGranStep.granuleW_step; do
  if ! echo "$k1a_termgranstep_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermGranStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aRts.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aRts.lean ..."
if ! k1a_termk2arts_out=$(leanb TermK2aRts 2>&1); then
  echo "$k1a_termk2arts_out"
  echo 'FAIL: TermK2aRts.lean does not compile.'
  fail=1
fi
case "$k1a_termk2arts_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aRts.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2a.rtsSub_trans TermK2a.decodeArm_rtsSub TermK2a.pubWords_rtsSub; do
  if ! echo "$k1a_termk2arts_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aRts.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermNoFul.lean ------------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermNoFul.lean ..."
if ! k1a_termnoful_out=$(leanb TermNoFul 2>&1); then
  echo "$k1a_termnoful_out"
  echo 'FAIL: TermNoFul.lean does not compile.'
  fail=1
fi
case "$k1a_termnoful_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermNoFul.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermPlantAtF.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPlantAtF.lean ..."
if ! k1a_termplantatf_out=$(leanb TermPlantAtF 2>&1); then
  echo "$k1a_termplantatf_out"
  echo 'FAIL: TermPlantAtF.lean does not compile.'
  fail=1
fi
case "$k1a_termplantatf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantAtF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPlantAtF.FM.trans TermPlantAtF.stepStore_fulM TermPlantAtF.stepRmw_fulM TermPlantAtF.stepRmwPair_fulM TermPlantAtF.tstep_fm TermPlantAtF.tstep_fulCoh; do
  if ! echo "$k1a_termplantatf_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtF.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantAtPos.lean -------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPlantAtPos.lean ..."
if ! k1a_termplantatpos_out=$(leanb TermPlantAtPos 2>&1); then
  echo "$k1a_termplantatpos_out"
  echo 'FAIL: TermPlantAtPos.lean does not compile.'
  fail=1
fi
case "$k1a_termplantatpos_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantAtPos.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPlantAtPos.promPos_steps TermPlantAtPos.promPos_run; do
  if ! echo "$k1a_termplantatpos_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtPos.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# (2b) theorems added to TermPlantAtPos.lean.
for thm in \
    "TermPlantAtPos.promPosR_of"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${k1a_termplantatpos_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtPos.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantAtT.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPlantAtT.lean ..."
if ! k1a_termplantatt_out=$(leanb TermPlantAtT 2>&1); then
  echo "$k1a_termplantatt_out"
  echo 'FAIL: TermPlantAtT.lean does not compile.'
  fail=1
fi
case "$k1a_termplantatt_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantAtT.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPlantAtT.mem_fpAt_cut TermPlantAtT.sto_of_cut TermPlantAtT.fp_pos TermPlantAtT.key_not_pubd TermPlantAtT.plantAtT_of; do
  if ! echo "$k1a_termplantatt_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtT.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantAtN.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPlantAtN.lean ..."
if ! k1a_termplantatn_out=$(leanb TermPlantAtN 2>&1); then
  echo "$k1a_termplantatn_out"
  echo 'FAIL: TermPlantAtN.lean does not compile.'
  fail=1
fi
case "$k1a_termplantatn_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantAtN.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPlantAtN.tstep_publish_vWr TermPlantAtN.noFul_pub TermPlantAtN.mem_along TermPlantAtN.noFulT_of; do
  if ! echo "$k1a_termplantatn_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtN.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPtrKey.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPtrKey.lean ..."
if ! k1a_termptrkey_out=$(leanb TermPtrKey 2>&1); then
  echo "$k1a_termptrkey_out"
  echo 'FAIL: TermPtrKey.lean does not compile.'
  fail=1
fi
case "$k1a_termptrkey_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPtrKey.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPtrKey.ownKey_noIncrease_thread TermPtrKey.ownKey_noIncrease_thread_upd TermPtrKey.ownKey_noIncrease_other TermPtrKey.ownKey_noIncrease_prom TermPtrKey.ownKey_noIncrease_prom_upd TermPtrKey.valOfR_own_zero TermPtrKey.cellOKR_own_zero TermPtrKey.heldS_own_zero TermPtrKey.heldS_own_zero_pre TermPtrKey.heldS_own_zero_post TermPtrKey.ownKey_noIncrease_thread_noHS TermPtrKey.ownKey_noIncrease_prom_noHS TermPtrKey.keyHeld_not_seen TermPtrKey.keyHeld_not_seen_contra TermPtrKey.keyHeld_not_pub TermPtrKey.keyHeld_not_newPub TermPtrKey.keyHeld_not_pub_C TermPtrKey.keyHeld_not_pub_C_contra TermPtrKey.ownKey_prom_le TermPtrKey.ptrRtsGL_promX TermPtrKey.promAlloc_locS TermPtrKey.thLbl_cut TermPtrKey.fresh_sto_none; do
  if ! echo "$k1a_termptrkey_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPtrKey.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPtrRtsK.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPtrRtsK.lean ..."
if ! k1a_termptrrtsk_out=$(leanb TermPtrRtsK 2>&1); then
  echo "$k1a_termptrrtsk_out"
  echo 'FAIL: TermPtrRtsK.lean does not compile.'
  fail=1
fi
case "$k1a_termptrrtsk_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPtrRtsK.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPtrRtsK.granuleW_prom TermPtrRtsK.ptrRtsGL_init TermPtrRtsK.stoLay_thread TermPtrRtsK.stoLay_egP TermPtrRtsK.stoLay_empty; do
  if ! echo "$k1a_termptrrtsk_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPtrRtsK.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPtrRtsThr.lean --------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPtrRtsThr.lean ..."
if ! k1a_termptrrtsthr_out=$(leanb TermPtrRtsThr 2>&1); then
  echo "$k1a_termptrrtsthr_out"
  echo 'FAIL: TermPtrRtsThr.lean does not compile.'
  fail=1
fi
case "$k1a_termptrrtsthr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPtrRtsThr.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPtrRtsThr.alloc_noFulfil; do
  if ! echo "$k1a_termptrrtsthr_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPtrRtsThr.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- OwnFreshW5b.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building OwnFreshW5b.lean ..."
if ! k1a_ownfreshw5b_out=$(leanb OwnFreshW5b 2>&1); then
  echo "$k1a_ownfreshw5b_out"
  echo 'FAIL: OwnFreshW5b.lean does not compile.'
  fail=1
fi
case "$k1a_ownfreshw5b_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a OwnFreshW5b.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPtrRtsK.oldMsg_not_fresh; do
  if ! echo "$k1a_ownfreshw5b_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: OwnFreshW5b.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPtrRtsGLT.lean --------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPtrRtsGLT.lean ..."
if ! k1a_termptrrtsglt_out=$(leanb TermPtrRtsGLT 2>&1); then
  echo "$k1a_termptrrtsglt_out"
  echo 'FAIL: TermPtrRtsGLT.lean does not compile.'
  fail=1
fi
case "$k1a_termptrrtsglt_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPtrRtsGLT.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPtrRtsK.ptrRtsGL_thread TermPtrRtsK.msgStoKeep TermPtrRtsK.exists_free; do
  if ! echo "$k1a_termptrrtsglt_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPtrRtsGLT.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermBoxPlantSep.lean ------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermBoxPlantSep.lean ..."
if ! k1a_termboxplantsep_out=$(leanb TermBoxPlantSep 2>&1); then
  echo "$k1a_termboxplantsep_out"
  echo 'FAIL: TermBoxPlantSep.lean does not compile.'
  fail=1
fi
case "$k1a_termboxplantsep_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBoxPlantSep.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPtrRtsK.boxPlantSep_thread TermPtrRtsK.boxPlantSep_prom TermPtrRtsK.boxPlantSep_none TermPtrRtsK.boxPlantSep_noProm; do
  if ! echo "$k1a_termboxplantsep_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBoxPlantSep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPubOnly.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPubOnly.lean ..."
if ! k1a_termpubonly_out=$(leanb TermPubOnly 2>&1); then
  echo "$k1a_termpubonly_out"
  echo 'FAIL: TermPubOnly.lean does not compile.'
  fail=1
fi
case "$k1a_termpubonly_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPubOnly.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPubOnly.sNo_Fd TermPubOnly.sNo_substTs_sub TermPubOnly.sNo_lay TermPubOnly.sNo_of_noOwn TermPubOnly.sNo_store TermPubOnly.sNo_store_ptr TermPubOnly.pubWords_store TermPubOnly.sNo_of_use TermPubOnly.sNo_writeFrom TermPubOnly.noFul_step_typed; do
  if ! echo "$k1a_termpubonly_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPubOnly.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermCntEmb.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermCntEmb.lean ..."
if ! k1a_termcntemb_out=$(leanb TermCntEmb 2>&1); then
  echo "$k1a_termcntemb_out"
  echo 'FAIL: TermCntEmb.lean does not compile.'
  fail=1
fi
case "$k1a_termcntemb_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCntEmb.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermCntEmb.pubWords_cl_guard TermCntEmb.pubWords_cl_unfold TermCntEmb.cnt_atOff TermCntEmb.cntK_shift TermCntEmb.cntOK_of_comp TermCntEmb.cntPairOK_of_comp; do
  if ! echo "$k1a_termcntemb_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermCntEmb.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermAdaptPW.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermAdaptPW.lean ..."
if ! k1a_termadaptpw_out=$(leanb TermAdaptPW 2>&1); then
  echo "$k1a_termadaptpw_out"
  echo 'FAIL: TermAdaptPW.lean does not compile.'
  fail=1
fi
case "$k1a_termadaptpw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermAdaptPW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermAdaptPW.pubWords_cl_adaptG TermAdaptPW.pubWords_cl_adapt0; do
  if ! echo "$k1a_termadaptpw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermAdaptPW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2a.lean --------------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2a.lean ..."
if ! k1a_termk2a_out=$(leanb TermK2a 2>&1); then
  echo "$k1a_termk2a_out"
  echo 'FAIL: TermK2a.lean does not compile.'
  fail=1
fi
case "$k1a_termk2a_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2a.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2a.tminOf_step TermK2a.ptrRtsE_step TermK2a.stepB_let TermK2a.thRts_of_stepB; do
  if ! echo "$k1a_termk2a_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2a.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aMem.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aMem.lean ..."
if ! k1a_termk2amem_out=$(leanb TermK2aMem 2>&1); then
  echo "$k1a_termk2amem_out"
  echo 'FAIL: TermK2aMem.lean does not compile.'
  fail=1
fi
case "$k1a_termk2amem_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aMem.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2a.fulCnt_le TermK2a.memRtsC_step TermK2a.memRtsC_stepGL; do
  if ! echo "$k1a_termk2amem_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aMem.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFulCntR.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFulCntR.lean ..."
if ! k1a_termfulcntr_out=$(leanb TermFulCntR 2>&1); then
  echo "$k1a_termfulcntr_out"
  echo 'FAIL: TermFulCntR.lean does not compile.'
  fail=1
fi
case "$k1a_termfulcntr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFulCntR.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2a.fulCntR_of_fulCnt TermK2a.fulCnt_leR TermK2a.memRtsC_stepR TermK2a.memRtsC_stepGLR; do
  if ! echo "$k1a_termfulcntr_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFulCntR.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aOps.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aOps.lean ..."
if ! k1a_termk2aops_out=$(leanb TermK2aOps 2>&1); then
  echo "$k1a_termk2aops_out"
  echo 'FAIL: TermK2aOps.lean does not compile.'
  fail=1
fi
case "$k1a_termk2aops_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aOps.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2a.valB_of_cntOld TermK2a.cntOld_evalAt TermK2a.cntOld_of_rtsSub TermK2a.cntOld_append TermK2a.cntOld_nil TermK2a.cntOld_bind TermK2a.mem_binds_of_env TermK2a.cntOld_env TermK2a.cntOld_lookup TermK2a.cntOld_noNames TermK2a.cntOld_pub_noNames TermK2a.not_names_num TermK2a.not_names_addW TermK2a.not_names_subW TermK2a.valB_add TermK2a.valB_sub TermK2a.valB_cvt TermK2a.valB_toInt TermK2a.valB_asLanes TermK2a.valB_fop TermK2a.valB_fcmp TermK2a.valB_fop1 TermK2a.valB_lane TermK2a.valB_setLane TermK2a.valB_rem TermK2a.valB_bits TermK2a.valB_bit1 TermK2a.valB_vmatch TermK2a.valB_band TermK2a.valB_nil TermK2a.valB_of_nil TermK2a.valB_store TermK2a.valB_stl TermK2a.valB_stlw TermK2a.valB_stp TermK2a.valB_fence TermK2a.valB_borrow TermK2a.valB_call TermK2a.valB_zero TermK2a.valB_claim TermK2a.valB_freeze TermK2a.valB_endBorrow TermK2a.valB_callc TermK2a.valB_atom TermK2a.valB_nameI TermK2a.valB_validate TermK2a.valB_null TermK2a.valB_fnptr TermK2a.valB_of_pubNil TermK2a.valB_new TermK2a.valB_newBuf TermK2a.valB_intoRgn TermK2a.pubWords_cellOf TermK2a.pubWords_loc TermK2a.pubWords_bufElem TermK2a.valB_reword TermK2a.names_offs TermK2a.valB_fld TermK2a.valB_idx TermK2a.valB_bufRes TermK2a.valB_bufInit TermK2a.not_names_of_num TermK2a.num_of_intIdx TermK2a.cntOld_num TermK2a.valB_pair TermK2a.valB_mkWord TermK2a.valB_mkWord2 TermK2a.valB_mkEPair TermK2a.valB_mkTicket TermK2a.newW_of_cntOld TermK2a.stepB_push TermK2a.stepB_same TermK2a.stepB_split TermK2a.stepB_unpack TermK2a.stepB_ifnull TermK2a.stepB_parity TermK2a.stepB_ifeq TermK2a.guardT_shiftIN TermK2a.guardT_shiftTN TermK2a.guardT_substTs TermK2a.stepB_unpackT; do
  if ! echo "$k1a_termk2aops_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aOps.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aRet.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aRet.lean ..."
if ! k1a_termk2aret_out=$(leanb TermK2aRet 2>&1); then
  echo "$k1a_termk2aret_out"
  echo 'FAIL: TermK2aRet.lean does not compile.'
  fail=1
fi
case "$k1a_termk2aret_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aRet.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2a.pubWords_rf TermK2a.armsOf_len_skel TermK2a.armsOf_len_er TermK2a.pubWords_er TermK2a.pubWords_skel TermK2a.pubWords_sig TermK2a.pubArm_sig TermK2a.pubWords_of_skel TermK2a.pubWords_subS TermK2a.pubWords_iex_eq TermK2a.pubWords_tex_eq TermK2a.pubWords_foldOK TermK2a.pubWords_pack TermK2a.pubWords_packT TermK2a.valB_retype TermK2a.valB_fold TermK2a.valB_pack TermK2a.valB_packT TermK2a.stepB_sub TermK2a.stepB_call TermK2a.stepB_tail TermK2a.stepB_ret TermK2a.stepB_callc; do
  if ! echo "$k1a_termk2aret_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aRet.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aLink.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aLink.lean ..."
if ! k1a_termk2alink_out=$(leanb TermK2aLink 2>&1); then
  echo "$k1a_termk2alink_out"
  echo 'FAIL: TermK2aLink.lean does not compile.'
  fail=1
fi
case "$k1a_termk2alink_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aLink.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aLink.hlink_of TermK2aLink.stepB_retK; do
  if ! echo "$k1a_termk2alink_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aLink.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aLinkPw.lean --------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aLinkPw.lean ..."
if ! k1a_termk2alinkpw_out=$(leanb TermK2aLinkPw 2>&1); then
  echo "$k1a_termk2alinkpw_out"
  echo 'FAIL: TermK2aLinkPw.lean does not compile.'
  fail=1
fi
case "$k1a_termk2alinkpw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aLinkPw.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aLinkPw.hlink_of TermK2aLinkPw.stepB_retK; do
  if ! echo "$k1a_termk2alinkpw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aLinkPw.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPubPos.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPubPos.lean ..."
if ! k1a_termpubpos_out=$(leanb TermPubPos 2>&1); then
  echo "$k1a_termpubpos_out"
  echo 'FAIL: TermPubPos.lean does not compile.'
  fail=1
fi
case "$k1a_termpubpos_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPubPos.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPubPos.pubWords_nr TermPubPos.pubWords_pos; do
  if ! echo "$k1a_termpubpos_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPubPos.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermCntPub.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermCntPub.lean ..."
if ! k1a_termcntpub_out=$(leanb TermCntPub 2>&1); then
  echo "$k1a_termcntpub_out"
  echo 'FAIL: TermCntPub.lean does not compile.'
  fail=1
fi
case "$k1a_termcntpub_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermCntPub.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermCntPub.pubWords_nb TermCntPub.cnt_pubWords; do
  if ! echo "$k1a_termcntpub_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermCntPub.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aLoad.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aLoad.lean ..."
if ! k1a_termk2aload_out=$(leanb TermK2aLoad 2>&1); then
  echo "$k1a_termk2aload_out"
  echo 'FAIL: TermK2aLoad.lean does not compile.'
  fail=1
fi
case "$k1a_termk2aload_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aLoad.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aLoad.loadUnits_readsR TermK2aLoad.readsR_len TermK2aLoad.readsR_at TermK2aLoad.notSnd_of_comp TermK2aLoad.loadW_of_reads TermK2aLoad.valB_of_reads; do
  if ! echo "$k1a_termk2aload_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aLoad.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aLd.lean ------------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aLd.lean ..."
if ! k1a_termk2ald_out=$(leanb TermK2aLd 2>&1); then
  echo "$k1a_termk2ald_out"
  echo 'FAIL: TermK2aLd.lean does not compile.'
  fail=1
fi
case "$k1a_termk2ald_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aLd.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermBufPW.lean ------------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermBufPW.lean ..."
if ! k1a_termbufpw_out=$(leanb TermBufPW 2>&1); then
  echo "$k1a_termbufpw_out"
  echo 'FAIL: TermBufPW.lean does not compile.'
  fail=1
fi
case "$k1a_termbufpw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBufPW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermBufPW.pw_chain TermBufPW.xchgAt_pw TermBufPW.xchgAtF_pw TermBufPW.bufInit_pw; do
  if ! echo "$k1a_termbufpw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBufPW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFulCntROf.lean --------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFulCntROf.lean ..."
if ! k1a_termfulcntrof_out=$(leanb TermFulCntROf 2>&1); then
  echo "$k1a_termfulcntrof_out"
  echo 'FAIL: TermFulCntROf.lean does not compile.'
  fail=1
fi
case "$k1a_termfulcntrof_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFulCntROf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFulCntROf.cnt_core TermFulCntROf.cell_pw TermFulCntROf.fulCntR_of; do
  if ! echo "$k1a_termfulcntrof_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFulCntROf.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aBox.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aBox.lean ..."
if ! k1a_termk2abox_out=$(leanb TermK2aBox 2>&1); then
  echo "$k1a_termk2abox_out"
  echo 'FAIL: TermK2aBox.lean does not compile.'
  fail=1
fi
case "$k1a_termk2abox_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aBox.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aBox.stepOKX_of_stepOK TermK2aBox.thRts_of_stepBX TermK2aBox.thLbl_of_stepOKX; do
  if ! echo "$k1a_termk2abox_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aBox.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aLabsV.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aLabsV.lean ..."
if ! k1a_termk2alabsv_out=$(leanb TermK2aLabsV 2>&1); then
  echo "$k1a_termk2alabsv_out"
  echo 'FAIL: TermK2aLabsV.lean does not compile.'
  fail=1
fi
case "$k1a_termk2alabsv_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aLabsV.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aLabsV.labsV_pubVR TermK2aLabsV.labsV_cnt; do
  if ! echo "$k1a_termk2alabsv_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aLabsV.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFgnCnt.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFgnCnt.lean ..."
if ! k1a_termfgncnt_out=$(leanb TermFgnCnt 2>&1); then
  echo "$k1a_termfgncnt_out"
  echo 'FAIL: TermFgnCnt.lean does not compile.'
  fail=1
fi
case "$k1a_termfgncnt_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFgnCnt.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermFgnCnt.fgnCnt_none TermFgnCnt.solo_typedXC TermFgnCnt.certified_promTgtC TermFgnCnt.fgnCnt_prom TermFgnCnt.fgnCnt_thread; do
  if ! echo "$k1a_termfgncnt_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFgnCnt.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aLdW.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aLdW.lean ..."
if ! k1a_termk2aldw_out=$(leanb TermK2aLdW 2>&1); then
  echo "$k1a_termk2aldw_out"
  echo 'FAIL: TermK2aLdW.lean does not compile.'
  fail=1
fi
case "$k1a_termk2aldw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aLdW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aLdW.ld_wordOwn TermK2aLdW.ld_wordPub TermK2aLdW.ld_wordLoc TermK2aLdW.ld_pOwn TermK2aLdW.ld_pPub TermK2aLdW.ld_pLoc TermK2aLdW.ld_lw TermK2aLdW.ld_l TermK2aLdW.ld_at TermK2aLdW.ld_atF; do
  if ! echo "$k1a_termk2aldw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aLdW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aMain.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aMain.lean ..."
if ! k1a_termk2amain_out=$(leanb TermK2aMain 2>&1); then
  echo "$k1a_termk2amain_out"
  echo 'FAIL: TermK2aMain.lean does not compile.'
  fail=1
fi
case "$k1a_termk2amain_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aMain.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aMain.stepOK_of_stepB_nil TermK2aMain.ful_edge_ge TermK2aMain.memRts_step; do
  if ! echo "$k1a_termk2amain_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aMain.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aRmw.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aRmw.lean ..."
if ! k1a_termk2armw_out=$(leanb TermK2aRmw 2>&1); then
  echo "$k1a_termk2armw_out"
  echo 'FAIL: TermK2aRmw.lean does not compile.'
  fail=1
fi
case "$k1a_termk2armw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aRmw.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aRmw.cas_shape TermK2aRmw.casp_shape TermK2aRmw.rmw_casWord TermK2aRmw.rmw_casCell TermK2aRmw.rmw_casWordLoc TermK2aRmw.rmw_casCellLoc TermK2aRmw.rmw_casp TermK2aRmw.rmw_caspLoc TermK2aRmw.fetch_coreK TermK2aRmw.noName_pub TermK2aRmw.ldOK_noName TermK2aRmw.stepOK_same TermK2aRmw.noName_num TermK2aRmw.stepOK_casLike TermK2aRmw.rmw_fetch TermK2aRmw.rmw_fetchLoc TermK2aRmw.xchg_out TermK2aRmw.rmw_xchgOwn TermK2aRmw.rmw_xchgLoc TermK2aRmw.rmw_xchgAt TermK2aRmw.rmw_xchgAtF; do
  if ! echo "$k1a_termk2armw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aRmw.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aSum.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aSum.lean ..."
if ! k1a_termk2asum_out=$(leanb TermK2aSum 2>&1); then
  echo "$k1a_termk2asum_out"
  echo 'FAIL: TermK2aSum.lean does not compile.'
  fail=1
fi
case "$k1a_termk2asum_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aSum.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aSum.sum_inl TermK2aSum.sum_inr TermK2aSum.sum_case TermK2aSum.sum_inlBR TermK2aSum.sum_inrBR TermK2aSum.sum_inlTR TermK2aSum.sum_inrTR TermK2aSum.sum_caseBR TermK2aSum.sum_caseTR TermK2aSum.pub_publish TermK2aSum.rgn_region TermK2aSum.rgn_openPub; do
  if ! echo "$k1a_termk2asum_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aSum.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aCaseB.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aCaseB.lean ..."
if ! k1a_termk2acaseb_out=$(leanb TermK2aCaseB 2>&1); then
  echo "$k1a_termk2acaseb_out"
  echo 'FAIL: TermK2aCaseB.lean does not compile.'
  fail=1
fi
case "$k1a_termk2acaseb_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aCaseB.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aCaseB.projM_pos TermK2aCaseB.boxLW_arm TermK2aCaseB.sum_caseBX TermK2aCaseB.sum_caseTX; do
  if ! echo "$k1a_termk2acaseb_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aCaseB.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aDisp.lean ----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aDisp.lean ..."
if ! k1a_termk2adisp_out=$(leanb TermK2aDisp 2>&1); then
  echo "$k1a_termk2adisp_out"
  echo 'FAIL: TermK2aDisp.lean does not compile.'
  fail=1
fi
case "$k1a_termk2adisp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aDisp.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermK2aDispX.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aDispX.lean ..."
if ! k1a_termk2adispx_out=$(leanb TermK2aDispX 2>&1); then
  echo "$k1a_termk2adispx_out"
  echo 'FAIL: TermK2aDispX.lean does not compile.'
  fail=1
fi
case "$k1a_termk2adispx_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aDispX.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aDispX.stepOKX_disp; do
  if ! echo "$k1a_termk2adispx_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aDispX.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermK2aFin.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermK2aFin.lean ..."
if ! k1a_termk2afin_out=$(leanb TermK2aFin 2>&1); then
  echo "$k1a_termk2afin_out"
  echo 'FAIL: TermK2aFin.lean does not compile.'
  fail=1
fi
case "$k1a_termk2afin_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK2aFin.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermK2aFin.ptrRtsThreadGL_v3d; do
  if ! echo "$k1a_termk2afin_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK2aFin.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermMemRtsProm.lean -------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermMemRtsProm.lean ..."
if ! k1a_termmemrtsprom_out=$(leanb TermMemRtsProm 2>&1); then
  echo "$k1a_termmemrtsprom_out"
  echo 'FAIL: TermMemRtsProm.lean does not compile.'
  fail=1
fi
case "$k1a_termmemrtsprom_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermMemRtsProm.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermMemRtsProm.noCnt_unpl TermMemRtsProm.memRtsCG_prom TermMemRtsProm.memRtsCG_promX; do
  if ! echo "$k1a_termmemrtsprom_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMemRtsProm.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermDBWire.lean -----------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermDBWire.lean ..."
if ! k1a_termdbwire_out=$(leanb TermDBWire 2>&1); then
  echo "$k1a_termdbwire_out"
  echo 'FAIL: TermDBWire.lean does not compile.'
  fail=1
fi
case "$k1a_termdbwire_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermDBWire.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPtrRtsK.granuleW_T TermPtrRtsK.granuleW_thread TermPtrRtsK.ptrGL_promW; do
  if ! echo "$k1a_termdbwire_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermDBWire.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermNoFulRun.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermNoFulRun.lean ..."
if ! k1a_termnofulrun_out=$(leanb TermNoFulRun 2>&1); then
  echo "$k1a_termnofulrun_out"
  echo 'FAIL: TermNoFulRun.lean does not compile.'
  fail=1
fi
case "$k1a_termnofulrun_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermNoFulRun.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermNoFulRun.lean (extern steps under outstanding promises): std axioms only
for thm in TermPtrKey.nfInv_ext; do
  if ! echo "$k1a_termnofulrun_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermNoFulRun.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in TermPtrKey.noFulPlRunGL_of; do
  if ! echo "$k1a_termnofulrun_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermNoFulRun.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootNCBOf.lean --------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermFootNCBOf.lean ..."
if ! k1a_termfootncbof_out=$(leanb TermFootNCBOf 2>&1); then
  echo "$k1a_termfootncbof_out"
  echo 'FAIL: TermFootNCBOf.lean does not compile.'
  fail=1
fi
case "$k1a_termfootncbof_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootNCBOf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPtrKey.footNCB_of; do
  if ! echo "$k1a_termfootncbof_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootNCBOf.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantAtI.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPlantAtI.lean ..."
if ! k1a_termplantati_out=$(leanb TermPlantAtI 2>&1); then
  echo "$k1a_termplantati_out"
  echo 'FAIL: TermPlantAtI.lean does not compile.'
  fail=1
fi
case "$k1a_termplantati_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantAtI.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPlantAtI.idxBody_keep TermPlantAtI.idxBody_plant TermPlantAtI.cfgCoh_run TermPlantAtI.plant_vWr TermPlantAtI.wordOK_lt TermPlantAtI.priv_le_coh_def TermPlantAtI.priv_le_coh; do
  if ! echo "$k1a_termplantati_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtI.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantAtJ.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPlantAtJ.lean ..."
if ! k1a_termplantatj_out=$(leanb TermPlantAtJ 2>&1); then
  echo "$k1a_termplantatj_out"
  echo 'FAIL: TermPlantAtJ.lean does not compile.'
  fail=1
fi
case "$k1a_termplantatj_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantAtJ.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPlantAtJ.plantIdx_thread TermPlantAtJ.plantIdx_prom; do
  if ! echo "$k1a_termplantatj_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtJ.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantAtW.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPlantAtW.lean ..."
if ! k1a_termplantatw_out=$(leanb TermPlantAtW 2>&1); then
  echo "$k1a_termplantatw_out"
  echo 'FAIL: TermPlantAtW.lean does not compile.'
  fail=1
fi
case "$k1a_termplantatw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantAtW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPlantAtW.postTyped TermPlantAtW.noFulStepT_of TermPlantAtW.noFul_pre TermPlantAtW.winAfterT_of TermPlantAtW.noFulT_tminG; do
  if ! echo "$k1a_termplantatw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermNoBufOwn.lean ----------------------------------------------------------
# New module.
echo "building TermNoBufOwn.lean ..."
if ! g277_termnobufown_out=$(leanb TermNoBufOwn 2>&1); then
  echo "$g277_termnobufown_out"
  echo 'FAIL: TermNoBufOwn.lean does not compile.'
  fail=1
fi
case "$g277_termnobufown_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermNoBufOwn.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermNoBufOwn.not_bufInitOn \
    TermNoBufOwn.noBufF_noKey \
    TermNoBufOwn.noBufT_noKey \
    TermNoBufOwn.noFul_preP \
    TermNoBufOwn.winF \
    TermNoBufOwn.solo_split \
    TermNoBufOwn.noBufT_pub \
    TermNoBufOwn.winT; do
  if ! echo "$g277_termnobufown_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermNoBufOwn.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermIniOpK.lean ---------------------------------------------------------------
echo "building TermIniOpK.lean ..."
if ! tiniopk_out=$(leanb TermIniOpK 2>&1); then
  echo "$tiniopk_out"
  echo 'FAIL: TermIniOpK.lean does not compile.'
  fail=1
fi
case "$tiniopk_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermIniOpK.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in bufInitPubF_of bufInitPubT_of; do
  if ! echo "$tiniopk_out" | grep -qE "'TermIniOpK.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermIniOpK.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermK5R.lean ---------------------------------------------------------------
# S1b stage (i): bufInit exclusion at cells published during a promise step's cert run.
# Placed after the TermOwnG0Defs block (TermK5R imports TermIniOpK and TermOwnG0Defs).
echo "building TermK5R.lean ..."
if ! tk5r_out=$(leanb TermK5R 2>&1); then
  echo "$tk5r_out"
  echo 'FAIL: TermK5R.lean does not compile.'
  fail=1
fi
case "$tk5r_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK5R.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in bufInitPubFR bufInitPubFR_plant; do
  if ! echo "$tk5r_out" | grep -qE "'TermK5R.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermK5R.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermK5Z.lean ---------------------------------------------------------------
# S1b (iv): hZp_of, bufInitPubFR_of.
echo "building TermK5Z.lean ..."
if ! tk5z_out=$(leanb TermK5Z 2>&1); then
  echo "$tk5z_out"
  echo 'FAIL: TermK5Z.lean does not compile.'
  fail=1
fi
case "$tk5z_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermK5Z.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in hZp_of bufInitPubFR_of; do
  if ! echo "$tk5z_out" | grep -qE "'TermK5Z.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermK5Z.$thm missing or uses non-standard axioms"
    fail=1
  fi
done

# --- TermBufPubT.lean -----------------------------------------------------------
# New module.
echo "building TermBufPubT.lean ..."
if ! g277_termbufpubt_out=$(leanb TermBufPubT 2>&1); then
  echo "$g277_termbufpubt_out"
  echo 'FAIL: TermBufPubT.lean does not compile.'
  fail=1
fi
case "$g277_termbufpubt_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBufPubT.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermBufPubT.pubStep_of \
    TermBufPubT.post_pfr_sto \
    TermBufPubT.bufInitPubTR_of; do
  if ! echo "$g277_termbufpubt_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBufPubT.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermRunLocK.lean -----------------------------------------------------------
# New module.
echo "building TermRunLocK.lean ..."
if ! g277_termrunlock_out=$(leanb TermRunLocK 2>&1); then
  echo "$g277_termrunlock_out"
  echo 'FAIL: TermRunLocK.lean does not compile.'
  fail=1
fi
case "$g277_termrunlock_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermRunLocK.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermRunLocK.iniK_core \
    TermRunLocK.w3K_F \
    TermRunLocK.w3K_T \
    TermRunLocK.runAgreeF3K_of \
    TermRunLocK.runAgreeT3K_of \
    TermRunLocK.runAgreeFT3_holds; do
  if ! echo "$g277_termrunlock_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermRunLocK.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantAtB.lean ---------------------------------------------------
# RetPw + PIDX/plantIdx + D-B: new module.
echo "building TermPlantAtB.lean ..."
if ! k1a_termplantatb_out=$(leanb TermPlantAtB 2>&1); then
  echo "$k1a_termplantatb_out"
  echo 'FAIL: TermPlantAtB.lean does not compile.'
  fail=1
fi
case "$k1a_termplantatb_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantAtB.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermPlantAtB.plantIdxT_of TermPlantAtB.plantIdxP_of TermPlantAtB.plantAtT_ofB; do
  if ! echo "$k1a_termplantatb_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtB.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermA4R.lean ---------------------------------------------------------------
# (A1 checker) D4: a value at an rcar-free type has the zero resource (vrr_zero_of_rcar, VR_VRR_rc).
echo "building TermA4R.lean ..."
if ! gd9_terma4r_out=$(leanb TermA4R 2>&1); then
  echo "$gd9_terma4r_out"
  echo 'FAIL: TermA4R.lean does not compile.'
  fail=1
fi
case "$gd9_terma4r_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermA4R.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermA4.vrr_zero_of_rcar TermA4.VR_VRR_rc TermA4.VR_VRR_rc_closed; do
  if ! echo "$gd9_terma4r_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermA4R.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermA4P.lean ---------------------------------------------------------------
# (A1 checker) D4: pieces of a wrapOK, closed, noOR cell type are FreeP (freeP_of_piece).
echo "building TermA4P.lean ..."
if ! gd9_terma4p_out=$(leanb TermA4P 2>&1); then
  echo "$gd9_terma4p_out"
  echo 'FAIL: TermA4P.lean does not compile.'
  fail=1
fi
case "$gd9_terma4p_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermA4P.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermA4.rcar_mu_fix TermA4.wrapOK_unfold TermA4.noOR_unfold TermA4.AtOff_wrap TermA4.freeP_of_piece; do
  if ! echo "$gd9_terma4p_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermA4P.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrF.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrF.lean ..."
if ! r4_termovercrf_out=$(leanb TermOverCrF 2>&1); then
  echo "$r4_termovercrf_out"
  echo 'FAIL: TermOverCrF.lean does not compile.'
  fail=1
fi
case "$r4_termovercrf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.initRr_back \
    TermOverCrW.overCr_interfMO \
    TermOverCrW.overCr_foreignOG \
    TermOverCrW.overCr_foreign \
    TermOverCrW.dnOf_facts; do
  if ! echo "$r4_termovercrf_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrF.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrD.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrD.lean ..."
if ! r4_termovercrd_out=$(leanb TermOverCrD 2>&1); then
  echo "$r4_termovercrd_out"
  echo 'FAIL: TermOverCrD.lean does not compile.'
  fail=1
fi
case "$r4_termovercrd_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrD.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.kfOf_spec \
    TermOverCrW.dn_items; do
  if ! echo "$r4_termovercrd_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrD.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrH.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrH.lean ..."
if ! r4_termovercrh_out=$(leanb TermOverCrH 2>&1); then
  echo "$r4_termovercrh_out"
  echo 'FAIL: TermOverCrH.lean does not compile.'
  fail=1
fi
case "$r4_termovercrh_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrH.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.plantCr_low \
    TermOverCrW.holderLow_dnOf \
    TermOverCrW.holderLow_back \
    TermOverCrW.tg_inj \
    TermOverCrW.kfOf_single \
    TermOverCrW.hcovD_core \
    TermOverCrW.mem_promAt_own; do
  if ! echo "$r4_termovercrh_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrH.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrN.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrN.lean ..."
if ! r4_termovercrn_out=$(leanb TermOverCrN 2>&1); then
  echo "$r4_termovercrn_out"
  echo 'FAIL: TermOverCrN.lean does not compile.'
  fail=1
fi
case "$r4_termovercrn_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrN.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.twoAtT_of_comp \
    TermOverCrW.inAcc_single; do
  if ! echo "$r4_termovercrn_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrN.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrP.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrP.lean ..."
if ! r4_termovercrp_out=$(leanb TermOverCrP 2>&1); then
  echo "$r4_termovercrp_out"
  echo 'FAIL: TermOverCrP.lean does not compile.'
  fail=1
fi
case "$r4_termovercrp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.exists_min_nat \
    TermOverCrW.plantCr_mk \
    TermOverCrW.lowest_in_piece \
    TermOverCrW.tgIn_isSome; do
  if ! echo "$r4_termovercrp_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrP.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPromAtFW.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermPromAtFW.lean ..."
if ! r4_termpromatfw_out=$(leanb TermPromAtFW 2>&1); then
  echo "$r4_termpromatfw_out"
  echo 'FAIL: TermPromAtFW.lean does not compile.'
  fail=1
fi
case "$r4_termpromatfw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPromAtFW.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermOverCrQ.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrQ.lean ..."
if ! r4_termovercrq_out=$(leanb TermOverCrQ 2>&1); then
  echo "$r4_termovercrq_out"
  echo 'FAIL: TermOverCrQ.lean does not compile.'
  fail=1
fi
case "$r4_termovercrq_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrQ.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.plantCr_add \
    TermOverCrW.crKeys_add \
    TermOverCrW.plantCrK_add \
    TermOverCrW.seg_of_atOff \
    TermOverCrW.piece_target \
    TermOverCrW.not_predU_of_initRr \
    TermOverCrW.covU_back \
    TermOverCrW.hcovD_coreQ \
    TermOverCrW.mem_fpOf_of_prom \
    TermOverCrW.mem_cut_fp_of_prom; do
  if ! echo "$r4_termovercrq_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrQ.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrR.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrR.lean ..."
if ! r4_termovercrr_out=$(leanb TermOverCrR 2>&1); then
  echo "$r4_termovercrr_out"
  echo 'FAIL: TermOverCrR.lean does not compile.'
  fail=1
fi
case "$r4_termovercrr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrR.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.predU_mono_cut \
    TermOverCrW.foreign_overCr \
    TermOverCrW.newOver_inTgt \
    TermOverCrW.inAcc_ex \
    TermOverCrW.hent_of; do
  if ! echo "$r4_termovercrr_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrR.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrS.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrS.lean ..."
if ! r4_termovercrs_out=$(leanb TermOverCrS 2>&1); then
  echo "$r4_termovercrs_out"
  echo 'FAIL: TermOverCrS.lean does not compile.'
  fail=1
fi
case "$r4_termovercrs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrS.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.plantCr_low_back \
    TermOverCrW.holderLow_dnOfL \
    TermOverCrW.crKeys_gd \
    TermOverCrW.pd_pre \
    TermOverCrW.htg_pre; do
  if ! echo "$r4_termovercrs_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrS.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrT.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrT.lean ..."
if ! r4_termovercrt_out=$(leanb TermOverCrT 2>&1); then
  echo "$r4_termovercrt_out"
  echo 'FAIL: TermOverCrT.lean does not compile.'
  fail=1
fi
case "$r4_termovercrt_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrT.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.pd_witness \
    TermOverCrW.plantCr_post; do
  if ! echo "$r4_termovercrt_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrT.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrU.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrU.lean ..."
if ! r4_termovercru_out=$(leanb TermOverCrU 2>&1); then
  echo "$r4_termovercru_out"
  echo 'FAIL: TermOverCrU.lean does not compile.'
  fail=1
fi
case "$r4_termovercru_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrU.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.hL_of; do
  if ! echo "$r4_termovercru_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrU.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# (PIN-D1b) theorems added to TermOverCrU.lean.
for thm in \
    TermOverCrW.newOver_L0; do
  if ! echo "$r4_termovercru_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrU.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrV.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrV.lean ..."
if ! r4_termovercrv_out=$(leanb TermOverCrV 2>&1); then
  echo "$r4_termovercrv_out"
  echo 'FAIL: TermOverCrV.lean does not compile.'
  fail=1
fi
case "$r4_termovercrv_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrV.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.crItem_mergeR \
    TermOverCrW.sumH_le_of_nodup \
    TermOverCrW.crItems_dedup \
    TermOverCr5.overCr_ownopD; do
  if ! echo "$r4_termovercrv_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrV.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrX.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrX.lean ..."
if ! r4_termovercrx_out=$(leanb TermOverCrX 2>&1); then
  echo "$r4_termovercrx_out"
  echo 'FAIL: TermOverCrX.lean does not compile.'
  fail=1
fi
case "$r4_termovercrx_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrX.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrX.sumH_rpL_le \
    TermOverCrX.overCr_ownopRS; do
  if ! echo "$r4_termovercrx_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrX.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrY.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrY.lean ..."
if ! r4_termovercry_out=$(leanb TermOverCrY 2>&1); then
  echo "$r4_termovercry_out"
  echo 'FAIL: TermOverCrY.lean does not compile.'
  fail=1
fi
case "$r4_termovercry_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrY.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.foreign_overCrP \
    TermOverCrW.hleft_of \
    TermOverCrW.fpT_of \
    TermOverCrW.foreign_overCrH \
    TermOverCrW.hent_vac; do
  if ! echo "$r4_termovercry_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrY.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrZ.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrZ.lean ..."
if ! r4_termovercrz_out=$(leanb TermOverCrZ 2>&1); then
  echo "$r4_termovercrz_out"
  echo 'FAIL: TermOverCrZ.lean does not compile.'
  fail=1
fi
case "$r4_termovercrz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrZ.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.valOfR_zero_of_wordOK \
    TermOverCrW.crItemQ_free \
    TermOverCrW.overCr_foreignM \
    TermOverCrW.hcovD_unit \
    TermOverCrW.foreign_overCrPZ; do
  if ! echo "$r4_termovercrz_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrZ.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPieceCov.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermPieceCov.lean ..."
if ! r4_termpiececov_out=$(leanb TermPieceCov 2>&1); then
  echo "$r4_termpiececov_out"
  echo 'FAIL: TermPieceCov.lean does not compile.'
  fail=1
fi
case "$r4_termpiececov_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPieceCov.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermOverCrC.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrC.lean ..."
if ! r4_termovercrc_out=$(leanb TermOverCrC 2>&1); then
  echo "$r4_termovercrc_out"
  echo 'FAIL: TermOverCrC.lean does not compile.'
  fail=1
fi
case "$r4_termovercrc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrC.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.own_agree \
    TermOverCrW.promAt_congr \
    TermOverCrW.stepper_set_post \
    TermOverCrW.piece_of_wordOK \
    TermOverCrW.hent_ofC; do
  if ! echo "$r4_termovercrc_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrC.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermForWU.lean -------------------------------------------------------------
# R4 route: new module.
echo "building TermForWU.lean ..."
if ! r4_termforwu_out=$(leanb TermForWU 2>&1); then
  echo "$r4_termforwu_out"
  echo 'FAIL: TermForWU.lean does not compile.'
  fail=1
fi
case "$r4_termforwu_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermForWU.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermForWU.cell_tgt \
    TermForWU.word_tgt \
    TermForWU.word2_tgt \
    TermForWU.epair_tgt \
    TermForWU.int_tgt \
    TermForWU.w2_wu \
    TermForWU.rmw_at \
    TermForWU.affine_substT \
    TermForWU.one_leafM \
    TermForWU.units_cls \
    TermForWU.fetch_cls \
    TermForWU.cas_cls \
    TermForWU.casp_cls \
    TermForWU.tstep_newFW \
    TermForWU.tstep_lostFW \
    TermForWU.tctx_forWU; do
  if ! echo "$r4_termforwu_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermForWU.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrE.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrE.lean ..."
if ! r4_termovercre_out=$(leanb TermOverCrE 2>&1); then
  echo "$r4_termovercre_out"
  echo 'FAIL: TermOverCrE.lean does not compile.'
  fail=1
fi
case "$r4_termovercre_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrE.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.solid_int \
    TermOverCrW.crItemQ_rmw; do
  if ! echo "$r4_termovercre_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrE.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrG.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrG.lean ..."
if ! r4_termovercrg_out=$(leanb TermOverCrG 2>&1); then
  echo "$r4_termovercrg_out"
  echo 'FAIL: TermOverCrG.lean does not compile.'
  fail=1
fi
case "$r4_termovercrg_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrG.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.newOver_src \
    TermOverCrW.crItemQ_freeQ \
    TermOverCrW.freeIt_spec \
    TermOverCrW.mem_freeL \
    TermOverCrW.freeL_item \
    TermOverCrW.freeL_zero \
    TermOverCrW.freeL_wa \
    TermOverCrW.freeL_holder \
    TermOverCrW.freeL_cover \
    TermOverCrW.hent_free; do
  if ! echo "$r4_termovercrg_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrG.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrNP.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrNP.lean ..."
if ! r4_termovercrnp_out=$(leanb TermOverCrNP 2>&1); then
  echo "$r4_termovercrnp_out"
  echo 'FAIL: TermOverCrNP.lean does not compile.'
  fail=1
fi
case "$r4_termovercrnp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrNP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.rmwAtom_congr \
    TermOverCrW.rmw_leaf \
    TermOverCrW.lostFp_stepper \
    TermOverCrW.epair_twoAtT \
    TermOverCrW.noLowOwn_two \
    TermOverCrW.wordOK_one_nundef \
    TermOverCrW.valOf_nundefU \
    TermOverCrW.own_valU \
    TermOverCrW.predAt_above \
    TermOverCrW.predNU_of_promAbove \
    TermOverCrW.np_hfree \
    TermOverCrW.foreign_overCrNP; do
  if ! echo "$r4_termovercrnp_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrNP.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrWb.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrWb.lean ..."
if ! r4_termovercrwb_out=$(leanb TermOverCrWb 2>&1); then
  echo "$r4_termovercrwb_out"
  echo 'FAIL: TermOverCrWb.lean does not compile.'
  fail=1
fi
case "$r4_termovercrwb_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrWb.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.overCr_foreignO \
    TermOverCrW.overCr_foreignMOG \
    TermOverCrW.overCr_foreignMO \
    TermOverCrW.hcovD_unitO \
    TermOverCrW.foreign_overCrPZOG \
    TermOverCrW.foreign_overCrPZO \
    TermOverCrW.hT_low_of_plantCr \
    TermOverCrW.winG_backK \
    TermOverCrW.winG_or_lost \
    TermOverCrW.hWbO_of_keep \
    TermOverCrW.hent_freeO \
    TermOverCrW.foreign_overCrNPG \
    TermOverCrW.foreign_overCrNPO \
    TermOverCrW.hWbT_of_keep \
    TermOverCrW.hent_ofCO; do
  if ! echo "$r4_termovercrwb_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrWb.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFreeQW.lean ------------------------------------------------------------
# R4 route: new module.
echo "building TermFreeQW.lean ..."
if ! r4_termfreeqw_out=$(leanb TermFreeQW 2>&1); then
  echo "$r4_termfreeqw_out"
  echo 'FAIL: TermFreeQW.lean does not compile.'
  fail=1
fi
case "$r4_termfreeqw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFreeQW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermFreeQW.valOfR_zero_fill \
    TermFreeQW.crItemQ_freeG \
    TermFreeQW.crItemQ_freeQW \
    TermFreeQW.freeQW_wa \
    TermFreeQW.noWU_piece \
    TermFreeQW.freeWL_cover \
    TermFreeQW.freeQW_exists \
    TermFreeQW.winG_or_lost2 \
    TermFreeQW.hent_ofCOW \
    TermFreeQW.valOfR_zero_fillP \
    TermFreeQW.freeQW_existsP \
    TermFreeQW.foreign_overCrCfgM \
    TermFreeQW.htgW_of1 \
    TermFreeQW.hWbRUp_of_hWbR \
    TermFreeQW.foreign_overCrCfgW \
    TermFreeQW.foreign_overCrCfg1W \
    TermOverCrW.foreign_overCrCfgO \
    TermOverCrW.foreign_overCrCfg1O \
    TermOverCrW.foreign_overCrCfg \
    TermOverCrW.foreign_overCrCfg1; do
  if ! echo "$r4_termfreeqw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFreeQW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFreeQWP.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermFreeQWP.lean ..."
if ! r4_termfreeqwp_out=$(leanb TermFreeQWP 2>&1); then
  echo "$r4_termfreeqwp_out"
  echo 'FAIL: TermFreeQWP.lean does not compile.'
  fail=1
fi
case "$r4_termfreeqwp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFreeQWP.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermPdR.lean ---------------------------------------------------------------
# R4 route: new module.
echo "building TermPdR.lean ..."
if ! r4_termpdr_out=$(leanb TermPdR 2>&1); then
  echo "$r4_termpdr_out"
  echo 'FAIL: TermPdR.lean does not compile.'
  fail=1
fi
case "$r4_termpdr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPdR.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.pd_witnessR \
    TermOverCrW.predNU_of_UL \
    TermOverCrW.foreign_overCrNPOU \
    TermOverCrW.htg_preT0 \
    TermOverCrW.noOR_atOffR \
    TermOverCrW.foreign_overCrCfg1PVG \
    TermOverCrW.foreign_overCrCfg1P; do
  if ! echo "$r4_termpdr_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPdR.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrPoolF.lean -------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrPoolF.lean ..."
if ! r4_termovercrpoolf_out=$(leanb TermOverCrPoolF 2>&1); then
  echo "$r4_termovercrpoolf_out"
  echo 'FAIL: TermOverCrPoolF.lean does not compile.'
  fail=1
fi
case "$r4_termovercrpoolf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrPoolF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermFreeQW.foreign_overCrCfgWV \
    TermFreeQW.foreign_overCrCfg1WV \
    TermOverCrW.foreign_overCrNPOUV \
    TermOverCrW.foreign_overCrCfg1PV; do
  if ! echo "$r4_termovercrpoolf_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrPoolF.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrPoolG.lean -------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrPoolG.lean ..."
if ! r4_termovercrpoolg_out=$(leanb TermOverCrPoolG 2>&1); then
  echo "$r4_termovercrpoolg_out"
  echo 'FAIL: TermOverCrPoolG.lean does not compile.'
  fail=1
fi
case "$r4_termovercrpoolg_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrPoolG.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.overCr_foreignOG \
    TermOverCrW.overCr_foreignMOG \
    TermOverCrW.foreign_overCrPZOG \
    TermFreeQW.foreign_overCrCfgWVG \
    TermFreeQW.foreign_overCrCfg1WVG \
    TermOverCrW.foreign_overCrCfg1PVG; do
  if ! echo "$r4_termovercrpoolg_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrPoolG.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrRepin.lean -------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrRepin.lean ..."
if ! r4_termovercrrepin_out=$(leanb TermOverCrRepin 2>&1); then
  echo "$r4_termovercrrepin_out"
  echo 'FAIL: TermOverCrRepin.lean does not compile.'
  fail=1
fi
case "$r4_termovercrrepin_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrRepin.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrW.crItemQ_repin \
    TermOverCrW.predAt_lost \
    TermOverCrW.foreign_overCrPZOR; do
  if ! echo "$r4_termovercrrepin_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrRepin.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermAffAt.lean -------------------------------------------------------------
# R4 route: new module.
echo "building TermAffAt.lean ..."
if ! r4_termaffat_out=$(leanb TermAffAt 2>&1); then
  echo "$r4_termaffat_out"
  echo 'FAIL: TermAffAt.lean does not compile.'
  fail=1
fi
case "$r4_termaffat_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermAffAt.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermAffAt.affine_of_substTA \
    TermAffAt.affine_unfoldA \
    TermAffAt.affine_foldA \
    TermAffAt.affine_fdA \
    TermAffAt.affine_atOffA \
    TermAffAt.affine_loadCell; do
  if ! echo "$r4_termaffat_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermAffAt.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFulW.lean --------------------------------------------------------------
# R4 route: new module.
echo "building TermFulW.lean ..."
if ! r4_termfulw_out=$(leanb TermFulW 2>&1); then
  echo "$r4_termfulw_out"
  echo 'FAIL: TermFulW.lean does not compile.'
  fail=1
fi
case "$r4_termfulw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFulW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermFulW.fetch_cls1 \
    TermFulW.cas_cls1 \
    TermFulW.evalOp_units \
    TermFulW.tstep_lostNA \
    TermFulW.tctx_lostNA \
    TermFulW.tstep_wpd \
    TermFulW.tctx_wpd; do
  if ! echo "$r4_termfulw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFulW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCF.lean -------------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCF.lean ..."
if ! r4_termowncf_out=$(leanb TermOwnCF 2>&1); then
  echo "$r4_termowncf_out"
  echo 'FAIL: TermOwnCF.lean does not compile.'
  fail=1
fi
case "$r4_termowncf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCF.overCrL_frame \
    TermOwnCF.winG_back \
    TermOwnCF.overT_back; do
  if ! echo "$r4_termowncf_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCF.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCP.lean -------------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCP.lean ..."
if ! r4_termowncp_out=$(leanb TermOwnCP 2>&1); then
  echo "$r4_termowncp_out"
  echo 'FAIL: TermOwnCP.lean does not compile.'
  fail=1
fi
case "$r4_termowncp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCP.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCP.overCr_assemble \
    TermOwnCP.firstW_ex \
    TermOwnCP.noOver_tail; do
  if ! echo "$r4_termowncp_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCP.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCR5.lean ------------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCR5.lean ..."
if ! r4_termowncr5_out=$(leanb TermOwnCR5 2>&1); then
  echo "$r4_termowncr5_out"
  echo 'FAIL: TermOwnCR5.lean does not compile.'
  fail=1
fi
case "$r4_termowncr5_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCR5.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCR5.fetch_cls2 \
    TermOwnCR5.cas_cls2 \
    TermOwnCR5.freeQW_rmw \
    TermOwnCR5.pin_wordOK \
    TermOwnCR5.overCr_keepZ \
    TermOwnCR5.crItemQ_frameP \
    TermOwnCR5.overCr_rmw; do
  if ! echo "$r4_termowncr5_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCR5.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCLoad.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCLoad.lean ..."
if ! r4_termowncload_out=$(leanb TermOwnCLoad 2>&1); then
  echo "$r4_termowncload_out"
  echo 'FAIL: TermOwnCLoad.lean does not compile.'
  fail=1
fi
case "$r4_termowncload_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCLoad.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCLoad.valOfR_copy_zero \
    TermOwnCLoad.atOff_tb \
    TermOwnCLoad.piece_in_comp \
    TermOwnCLoad.load_piece_affine; do
  if ! echo "$r4_termowncload_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCLoad.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCPin.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCPin.lean ..."
if ! r4_termowncpin_out=$(leanb TermOwnCPin 2>&1); then
  echo "$r4_termowncpin_out"
  echo 'FAIL: TermOwnCPin.lean does not compile.'
  fail=1
fi
case "$r4_termowncpin_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCPin.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCPin.predAt_coh \
    TermOwnCPin.coh_wordOK \
    TermOwnCPin.pin_of_winG; do
  if ! echo "$r4_termowncpin_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCPin.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCOld.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCOld.lean ..."
if ! r4_termowncold_out=$(leanb TermOwnCOld 2>&1); then
  echo "$r4_termowncold_out"
  echo 'FAIL: TermOwnCOld.lean does not compile.'
  fail=1
fi
case "$r4_termowncold_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCOld.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCOld.overCr_keepZI \
    TermOwnCOld.overCr_old; do
  if ! echo "$r4_termowncold_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCOld.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCH.lean -------------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCH.lean ..."
if ! r4_termownch_out=$(leanb TermOwnCH 2>&1); then
  echo "$r4_termownch_out"
  echo 'FAIL: TermOwnCH.lean does not compile.'
  fail=1
fi
case "$r4_termownch_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCH.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCH.zeroIt_unit \
    TermOwnCH.hno_of_promNoTwo; do
  if ! echo "$r4_termownch_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCH.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCRmw.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCRmw.lean ..."
if ! r4_termowncrmw_out=$(leanb TermOwnCRmw 2>&1); then
  echo "$r4_termowncrmw_out"
  echo 'FAIL: TermOwnCRmw.lean does not compile.'
  fail=1
fi
case "$r4_termowncrmw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCRmw.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCRmw.hFP_rmw; do
  if ! echo "$r4_termowncrmw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCRmw.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnFree.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnFree.lean ..."
if ! r4_termownfree_out=$(leanb TermOwnFree 2>&1); then
  echo "$r4_termownfree_out"
  echo 'FAIL: TermOwnFree.lean does not compile.'
  fail=1
fi
case "$r4_termownfree_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnFree.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnFree.overCrL_addFree \
    TermOwnFree.overCrL_addFreeWL; do
  if ! echo "$r4_termownfree_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnFree.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermA4P2.lean --------------------------------------------------------------
# (A1 checker) D4: freeP_of_pieceT, the piece discharge at wrapTop (SysInvN.stoW), for hWbR.
echo "building TermA4P2.lean ..."
if ! gd9_terma4p2_out=$(leanb TermA4P2 2>&1); then
  echo "$gd9_terma4p2_out"
  echo 'FAIL: TermA4P2.lean does not compile.'
  fail=1
fi
case "$gd9_terma4p2_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermA4P2.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermA4.wrapT_cl_ge TermA4.wrapTop_unfold TermA4.AtOff_wrapT TermA4.freeP_of_pieceT; do
  if ! echo "$gd9_terma4p2_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermA4P2.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPinDet.lean ------------------------------------------------------------
# (PIN-D1a) new module.
echo "building TermPinDet.lean ..."
if ! g276_termpindet_out=$(leanb TermPinDet 2>&1); then
  echo "$g276_termpindet_out"
  echo 'FAIL: TermPinDet.lean does not compile.'
  fail=1
fi
case "$g276_termpindet_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPinDet.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPinDet.vrr_kf \
    TermPinDet.vrr_detW \
    TermPinDet.cellR_detW \
    TermPinDet.atoms_detW \
    TermPinDet.noOR_of_noOwnIn \
    TermPinDet.atomR_const; do
  if ! echo "$g276_termpindet_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPinDet.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPinBI.lean -------------------------------------------------------------
# (PIN-D1a) new module.
echo "building TermPinBI.lean ..."
if ! g276_termpinbi_out=$(leanb TermPinBI 2>&1); then
  echo "$g276_termpinbi_out"
  echo 'FAIL: TermPinBI.lean does not compile.'
  fail=1
fi
case "$g276_termpinbi_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPinBI.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPinBI.atomL_of_atOff \
    TermPinBI.atomL_off_inj \
    TermPinBI.atomL_wrapTop \
    TermPinBI.atomL_zwL \
    TermPinBI.value_sumR \
    TermPinBI.dbF_le_val; do
  if ! echo "$g276_termpinbi_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPinBI.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPinBIOf.lean -----------------------------------------------------------
# (PIN-D1a) new module.
echo "building TermPinBIOf.lean ..."
if ! g276_termpinbiof_out=$(leanb TermPinBIOf 2>&1); then
  echo "$g276_termpinbiof_out"
  echo 'FAIL: TermPinBIOf.lean does not compile.'
  fail=1
fi
case "$g276_termpinbiof_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPinBIOf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPinBIOf.bufInitHeld_of; do
  if ! echo "$g276_termpinbiof_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPinBIOf.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- PoolCovB.lean --------------------------------------------------------------
# R4 route: new module.
echo "building PoolCovB.lean ..."
if ! r4_poolcovb_out=$(leanb PoolCovB 2>&1); then
  echo "$r4_poolcovb_out"
  echo 'FAIL: PoolCovB.lean does not compile.'
  fail=1
fi
case "$r4_poolcovb_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a PoolCovB.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolCovB.poolCovU_nil \
    TermPoolCovB.poolCovU_of_L \
    TermPoolCovB.poolCovUL_nil; do
  if ! echo "$r4_poolcovb_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: PoolCovB.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolMainAux.lean -------------------------------------------------------
# R4 route: new module.
echo "building TermPoolMainAux.lean ..."
if ! r4_termpoolmainaux_out=$(leanb TermPoolMainAux 2>&1); then
  echo "$r4_termpoolmainaux_out"
  echo 'FAIL: TermPoolMainAux.lean does not compile.'
  fail=1
fi
case "$r4_termpoolmainaux_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolMainAux.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolMainAux.crKeys_dh; do
  if ! echo "$r4_termpoolmainaux_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolMainAux.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermHtgW1.lean -------------------------------------------------------------
# R4 route: new module.
echo "building TermHtgW1.lean ..."
if ! r4_termhtgw1_out=$(leanb TermHtgW1 2>&1); then
  echo "$r4_termhtgw1_out"
  echo 'FAIL: TermHtgW1.lean does not compile.'
  fail=1
fi
case "$r4_termhtgw1_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermHtgW1.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermHtgW1.nw_piece \
    TermHtgW1.htgW1_sup \
    TermHtgW1.hPd_sup; do
  if ! echo "$r4_termhtgw1_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermHtgW1.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolStepTgt.lean -------------------------------------------------------
# R4 route: new module.
echo "building TermPoolStepTgt.lean ..."
if ! r4_termpoolsteptgt_out=$(leanb TermPoolStepTgt 2>&1); then
  echo "$r4_termpoolsteptgt_out"
  echo 'FAIL: TermPoolStepTgt.lean does not compile.'
  fail=1
fi
case "$r4_termpoolsteptgt_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolStepTgt.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolStepTgt.stepTgt_supply; do
  if ! echo "$r4_termpoolsteptgt_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolStepTgt.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrProm.lean --------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrProm.lean ..."
if ! r4_termovercrprom_out=$(leanb TermOverCrProm 2>&1); then
  echo "$r4_termovercrprom_out"
  echo 'FAIL: TermOverCrProm.lean does not compile.'
  fail=1
fi
case "$r4_termovercrprom_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrProm.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrProm.mem_promAt_above \
    TermOverCrProm.crItemQ_cr \
    TermOverCrProm.unit_congr \
    TermOverCrProm.overCr_frameD \
    TermOverCrProm.promAt_mono \
    TermOverCrProm.priv_le_coh \
    TermOverCrProm.valOfR_EgP \
    TermOverCrProm.plantCr_cutS \
    TermOverCrProm.newD_ex \
    TermOverCrProm.overCr_prom_other \
    TermOverCrProm.overCr_prom_self \
    TermOverCrProm.openOverCrProm_holds; do
  if ! echo "$r4_termovercrprom_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrProm.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermReadClsDefs.lean -------------------------------------------------------
# R4 route: new module.
echo "building TermReadClsDefs.lean ..."
if ! r4_termreadclsdefs_out=$(leanb TermReadClsDefs 2>&1); then
  echo "$r4_termreadclsdefs_out"
  echo 'FAIL: TermReadClsDefs.lean does not compile.'
  fail=1
fi
case "$r4_termreadclsdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermReadClsDefs.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermNewCoh.lean ------------------------------------------------------------
# R4 route: new module.
echo "building TermNewCoh.lean ..."
if ! r4_termnewcoh_out=$(leanb TermNewCoh 2>&1); then
  echo "$r4_termnewcoh_out"
  echo 'FAIL: TermNewCoh.lean does not compile.'
  fail=1
fi
case "$r4_termnewcoh_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermNewCoh.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermNewCoh.tctx_newCoh; do
  if ! echo "$r4_termnewcoh_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermNewCoh.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnNF.lean -------------------------------------------------------------
# R4 route: new module.
echo "building TermOwnNF.lean ..."
if ! r4_termownnf_out=$(leanb TermOwnNF 2>&1); then
  echo "$r4_termownnf_out"
  echo 'FAIL: TermOwnNF.lean does not compile.'
  fail=1
fi
case "$r4_termownnf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnNF.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnNF.nf_of; do
  if ! echo "$r4_termownnf_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnNF.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolThread.lean --------------------------------------------------------
# R4 route: new module.
echo "building TermPoolThread.lean ..."
if ! r4_termpoolthread_out=$(leanb TermPoolThread 2>&1); then
  echo "$r4_termpoolthread_out"
  echo 'FAIL: TermPoolThread.lean does not compile.'
  fail=1
fi
case "$r4_termpoolthread_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolThread.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolThread.poolThread \
    TermPoolThread.poolProm; do
  if ! echo "$r4_termpoolthread_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolThread.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermULBr.lean --------------------------------------------------------------
# R4 route: new module.
echo "building TermULBr.lean ..."
if ! r4_termulbr_out=$(leanb TermULBr 2>&1); then
  echo "$r4_termulbr_out"
  echo 'FAIL: TermULBr.lean does not compile.'
  fail=1
fi
case "$r4_termulbr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermULBr.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermULBr.hUL_of \
    TermULBr.hUL_cut \
    TermULBr.hUL_step; do
  if ! echo "$r4_termulbr_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermULBr.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolFgnCov.lean --------------------------------------------------------
# R4 route: new module.
echo "building TermPoolFgnCov.lean ..."
if ! r4_termpoolfgncov_out=$(leanb TermPoolFgnCov 2>&1); then
  echo "$r4_termpoolfgncov_out"
  echo 'FAIL: TermPoolFgnCov.lean does not compile.'
  fail=1
fi
case "$r4_termpoolfgncov_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolFgnCov.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolFgnCov.crN_cover \
    TermPoolFgnCov.fgnCov_of \
    TermPoolFgnCov.cover_cv; do
  if ! echo "$r4_termpoolfgncov_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolFgnCov.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolSupp.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermPoolSupp.lean ..."
if ! r4_termpoolsupp_out=$(leanb TermPoolSupp 2>&1); then
  echo "$r4_termpoolsupp_out"
  echo 'FAIL: TermPoolSupp.lean does not compile.'
  fail=1
fi
case "$r4_termpoolsupp_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolSupp.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolSupp.crKeys_entry \
    TermPoolSupp.tgtSupp_of \
    TermPoolSupp.suppAll_of \
    TermPoolSupp.fgnCov_of_wb; do
  if ! echo "$r4_termpoolsupp_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolSupp.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolCovFgn.lean --------------------------------------------------------
# R4 route: new module.
echo "building TermPoolCovFgn.lean ..."
if ! r4_termpoolcovfgn_out=$(leanb TermPoolCovFgn 2>&1); then
  echo "$r4_termpoolcovfgn_out"
  echo 'FAIL: TermPoolCovFgn.lean does not compile.'
  fail=1
fi
case "$r4_termpoolcovfgn_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolCovFgn.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolCovFgn.δh_eq \
    TermPoolCovFgn.slotFW_of_unit \
    TermPoolCovFgn.poolCovU_create \
    TermPoolCovFgn.poolCovU_fgn \
    TermPoolCovFgn.predU_piece \
    TermPoolCovFgn.slotFW_of_piece; do
  if ! echo "$r4_termpoolcovfgn_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolCovFgn.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFgnNew.lean ------------------------------------------------------------
# R4 route: new module.
echo "building TermFgnNew.lean ..."
if ! r4_termfgnnew_out=$(leanb TermFgnNew 2>&1); then
  echo "$r4_termfgnnew_out"
  echo 'FAIL: TermFgnNew.lean does not compile.'
  fail=1
fi
case "$r4_termfgnnew_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFgnNew.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermFgnNew.fgnNew_of; do
  if ! echo "$r4_termfgnnew_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFgnNew.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPlantBI.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermPlantBI.lean ..."
if ! r4_termplantbi_out=$(leanb TermPlantBI 2>&1); then
  echo "$r4_termplantbi_out"
  echo 'FAIL: TermPlantBI.lean does not compile.'
  fail=1
fi
case "$r4_termplantbi_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPlantBI.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPlant.keepQRSB_of_exP \
    TermPlant.rpSum_append \
    TermPlant.promCrK_addRS \
    TermPlant.keepQRSB_addRS \
    TermPlant.biSum_filter_le \
    TermPlant.biSum_filter2_le \
    TermPlant.biSum_split \
    TermPlant.biSum_group \
    TermPlant.biPool \
    TermPlant.tstepMCF_stepTKA_zfB; do
  if ! echo "$r4_termplantbi_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantBI.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFootBPKB.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermFootBPKB.lean ..."
if ! r4_termfootbpkb_out=$(leanb TermFootBPKB 2>&1); then
  echo "$r4_termfootbpkb_out"
  echo 'FAIL: TermFootBPKB.lean does not compile.'
  fail=1
fi
case "$r4_termfootbpkb_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFootBPKB.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermFootBPKB.tstepMCF_stepTKA_zfNBB; do
  if ! echo "$r4_termfootbpkb_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFootBPKB.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermHWbRWrap.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermHWbRWrap.lean ..."
if ! r4_termhwbrwrap_out=$(leanb TermHWbRWrap 2>&1); then
  echo "$r4_termhwbrwrap_out"
  echo 'FAIL: TermHWbRWrap.lean does not compile.'
  fail=1
fi
case "$r4_termhwbrwrap_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermHWbRWrap.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermHWbRWrap.hWbRUp_of_wrap \
    TermHWbRWrap.fgnCov_of_wrap; do
  if ! echo "$r4_termhwbrwrap_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermHWbRWrap.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolResplit.lean -------------------------------------------------------
# R4 route: new module.
echo "building TermPoolResplit.lean ..."
if ! r4_termpoolresplit_out=$(leanb TermPoolResplit 2>&1); then
  echo "$r4_termpoolresplit_out"
  echo 'FAIL: TermPoolResplit.lean does not compile.'
  fail=1
fi
case "$r4_termpoolresplit_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolResplit.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolResplit.crPl_R \
    TermPoolResplit.crR_own \
    TermPoolResplit.promCrK_R; do
  if ! echo "$r4_termpoolresplit_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolResplit.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermHbiPOf.lean ------------------------------------------------------------
# R4 route: new module.
echo "building TermHbiPOf.lean ..."
if ! r4_termhbipof_out=$(leanb TermHbiPOf 2>&1); then
  echo "$r4_termhbipof_out"
  echo 'FAIL: TermHbiPOf.lean does not compile.'
  fail=1
fi
case "$r4_termhbipof_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermHbiPOf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermHbiPOf.stepCrQ_of \
    TermHbiPOf.crS_le \
    TermHbiPOf.hbiP_of; do
  if ! echo "$r4_termhbipof_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermHbiPOf.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCr5D.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCr5D.lean ..."
if ! r4_termovercr5d_out=$(leanb TermOverCr5D 2>&1); then
  echo "$r4_termovercr5d_out"
  echo 'FAIL: TermOverCr5D.lean does not compile.'
  fail=1
fi
case "$r4_termovercr5d_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCr5D.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCr5D.hpi_of_promIni; do
  if ! echo "$r4_termovercr5d_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCr5D.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrOwnCommon.lean ---------------------------------------------------
# R4 route: new module.
echo "building TermOverCrOwnCommon.lean ..."
if ! r4_termovercrowncommon_out=$(leanb TermOverCrOwnCommon 2>&1); then
  echo "$r4_termovercrowncommon_out"
  echo 'FAIL: TermOverCrOwnCommon.lean does not compile.'
  fail=1
fi
case "$r4_termovercrowncommon_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrOwnCommon.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrOwnCommon.cutT_self \
    TermOverCrOwnCommon.overCrE_cutT \
    TermOverCrOwnCommon.cutT_sto \
    TermOverCrOwnCommon.cutT_pfr \
    TermOverCrOwnCommon.cutT_ini \
    TermOverCrOwnCommon.cutT_rini \
    TermOverCrOwnCommon.cutT_tid \
    TermOverCrOwnCommon.cutT_fp \
    TermOverCrOwnCommon.pre_overCrE \
    TermOverCrOwnCommon.valOfR_step \
    TermOverCrOwnCommon.old_of_new \
    TermOverCrOwnCommon.old_of_newP; do
  if ! echo "$r4_termovercrowncommon_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrOwnCommon.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermUnitKeepC.lean ---------------------------------------------------------
# R4 route: new module.
echo "building TermUnitKeepC.lean ..."
if ! r4_termunitkeepc_out=$(leanb TermUnitKeepC 2>&1); then
  echo "$r4_termunitkeepc_out"
  echo 'FAIL: TermUnitKeepC.lean does not compile.'
  fail=1
fi
case "$r4_termunitkeepc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermUnitKeepC.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermUnitKeepC.loadUnits_cohOff \
    TermUnitKeepC.loadUnits_keepMP \
    TermUnitKeepC.LS_cohKeep \
    TermUnitKeepC.opAtom_shapes \
    TermUnitKeepC.tstep_LS; do
  if ! echo "$r4_termunitkeepc_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermUnitKeepC.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOverCrA3.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermOverCrA3.lean ..."
if ! r4_termovercra3_out=$(leanb TermOverCrA3 2>&1); then
  echo "$r4_termovercra3_out"
  echo 'FAIL: TermOverCrA3.lean does not compile.'
  fail=1
fi
case "$r4_termovercra3_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOverCrA3.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOverCrA3.le_rpSum \
    TermOverCrA3.rpSum_append \
    TermOverCrA3.repinQh_of_U \
    TermOverCrA3.repinQh_append \
    TermOverCrA3.overCr_ownopH \
    TermOverCrA3.repinCov_full \
    TermOverCrA3.piece_of_wordOKA \
    TermOverCrA3.predU_iff \
    TermOverCrA3.item_piece \
    TermOverCrA3.cover_core \
    TermOverCrA3.openOverCrOwnA_of; do
  if ! echo "$r4_termovercra3_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrA3.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCOldR.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCOldR.lean ..."
if ! r4_termowncoldr_out=$(leanb TermOwnCOldR 2>&1); then
  echo "$r4_termowncoldr_out"
  echo 'FAIL: TermOwnCOldR.lean does not compile.'
  fail=1
fi
case "$r4_termowncoldr_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCOldR.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCOldR.le_rpSum \
    TermOwnCOldR.overCr_oldR; do
  if ! echo "$r4_termowncoldr_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCOldR.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCGlue.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCGlue.lean ..."
if ! r4_termowncglue_out=$(leanb TermOwnCGlue 2>&1); then
  echo "$r4_termowncglue_out"
  echo 'FAIL: TermOwnCGlue.lean does not compile.'
  fail=1
fi
case "$r4_termowncglue_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCGlue.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCGlue.hcovN_of; do
  if ! echo "$r4_termowncglue_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCGlue.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCPU.lean ------------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCPU.lean ..."
if ! r4_termowncpu_out=$(leanb TermOwnCPU 2>&1); then
  echo "$r4_termowncpu_out"
  echo 'FAIL: TermOwnCPU.lean does not compile.'
  fail=1
fi
case "$r4_termowncpu_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCPU.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCPU.oneAt_of_single \
    TermOwnCPU.hPU_core; do
  if ! echo "$r4_termowncpu_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCPU.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCT.lean -------------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCT.lean ..."
if ! r4_termownct_out=$(leanb TermOwnCT 2>&1); then
  echo "$r4_termownct_out"
  echo 'FAIL: TermOwnCT.lean does not compile.'
  fail=1
fi
case "$r4_termownct_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCT.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCT.items_of_list \
    TermOwnCT.overCr_tail; do
  if ! echo "$r4_termownct_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCT.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCPub.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCPub.lean ..."
if ! r4_termowncpub_out=$(leanb TermOwnCPub 2>&1); then
  echo "$r4_termowncpub_out"
  echo 'FAIL: TermOwnCPub.lean does not compile.'
  fail=1
fi
case "$r4_termowncpub_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCPub.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCPub.tstep_publish_keep \
    TermOwnCPub.rpSum_ne \
    TermOwnCPub.cut_wit \
    TermOwnCPub.ownC_pub; do
  if ! echo "$r4_termowncpub_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCPub.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCWpd.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCWpd.lean ..."
if ! r4_termowncwpd_out=$(leanb TermOwnCWpd 2>&1); then
  echo "$r4_termowncwpd_out"
  echo 'FAIL: TermOwnCWpd.lean does not compile.'
  fail=1
fi
case "$r4_termowncwpd_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCWpd.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCWpd.hFP_of_wpd; do
  if ! echo "$r4_termowncwpd_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCWpd.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCTop.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCTop.lean ..."
if ! r4_termownctop_out=$(leanb TermOwnCTop 2>&1); then
  echo "$r4_termownctop_out"
  echo 'FAIL: TermOwnCTop.lean does not compile.'
  fail=1
fi
case "$r4_termownctop_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCTop.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCTop.openOverCrOwnC_of; do
  if ! echo "$r4_termownctop_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCTop.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermRiseLoc.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermRiseLoc.lean ..."
if ! r4_termriseloc_out=$(leanb TermRiseLoc 2>&1); then
  echo "$r4_termriseloc_out"
  echo 'FAIL: TermRiseLoc.lean does not compile.'
  fail=1
fi
case "$r4_termriseloc_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermRiseLoc.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermRiseLoc.tstep_riseLoc; do
  if ! echo "$r4_termriseloc_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermRiseLoc.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCFul.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCFul.lean ..."
if ! r4_termowncful_out=$(leanb TermOwnCFul 2>&1); then
  echo "$r4_termowncful_out"
  echo 'FAIL: TermOwnCFul.lean does not compile.'
  fail=1
fi
case "$r4_termowncful_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCFul.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCFul.opTgt_of_units \
    TermOwnCFul.tstep_fulCls \
    TermOwnCFul.tctx_fulCls \
    TermOwnCFul.caseB_of; do
  if ! echo "$r4_termowncful_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCFul.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermReadClsM.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermReadClsM.lean ..."
if ! r4_termreadclsm_out=$(leanb TermReadClsM 2>&1); then
  echo "$r4_termreadclsm_out"
  echo 'FAIL: TermReadClsM.lean does not compile.'
  fail=1
fi
case "$r4_termreadclsm_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermReadClsM.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermReadClsM.evalOp_rd \
    TermReadClsM.tstep_rd; do
  if ! echo "$r4_termreadclsm_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermReadClsM.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermReadCls.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermReadCls.lean ..."
if ! r4_termreadcls_out=$(leanb TermReadCls 2>&1); then
  echo "$r4_termreadcls_out"
  echo 'FAIL: TermReadCls.lean does not compile.'
  fail=1
fi
case "$r4_termreadcls_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermReadCls.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermReadCls.readAt_goal \
    TermReadCls.box_none \
    TermReadCls.pair_rd \
    TermReadCls.load_rdC \
    TermReadCls.loadAt_rdC \
    TermReadCls.loadAtF_rdC \
    TermReadCls.ldl_rdC \
    TermReadCls.ldlw_rdC \
    TermReadCls.op_rdC \
    TermReadCls.tstep_rdC \
    TermReadCls.tstep_readCls \
    TermReadCls.tctx_readCls; do
  if ! echo "$r4_termreadcls_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermReadCls.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPredRdM.lean -----------------------------------------------------------
# R4 route: new module.
echo "building TermPredRdM.lean ..."
if ! r4_termpredrdm_out=$(leanb TermPredRdM 2>&1); then
  echo "$r4_termpredrdm_out"
  echo 'FAIL: TermPredRdM.lean does not compile.'
  fail=1
fi
case "$r4_termpredrdm_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPredRdM.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPredRdM.stepLoadPair_rd \
    TermPredRdM.stepRmw_rd \
    TermPredRdM.stepRmwPair_rd \
    TermPredRdM.loadUnits_rdv \
    TermPredRdM.fetch_rdv \
    TermPredRdM.cas_ev \
    TermPredRdM.casp_ev \
    TermPredRdM.tstep_rdv; do
  if ! echo "$r4_termpredrdm_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPredRdM.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPredRd.lean ------------------------------------------------------------
# R4 route: new module.
echo "building TermPredRd.lean ..."
if ! r4_termpredrd_out=$(leanb TermPredRd 2>&1); then
  echo "$r4_termpredrd_out"
  echo 'FAIL: TermPredRd.lean does not compile.'
  fail=1
fi
case "$r4_termpredrd_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPredRd.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPredRd.oneAt_of_noTwo \
    TermPredRd.noTwo_oneAt \
    TermPredRd.foot_false \
    TermPredRd.load_foot \
    TermPredRd.loadAt_foot \
    TermPredRd.loadAtF_foot \
    TermPredRd.ldl_foot \
    TermPredRd.ldlw_foot \
    TermPredRd.fetch_foot \
    TermPredRd.cas_foot \
    TermPredRd.op_foot \
    TermPredRd.tstep_predRd \
    TermPredRd.tctx_predRd; do
  if ! echo "$r4_termpredrd_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPredRd.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCRead.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCRead.lean ..."
if ! r4_termowncread_out=$(leanb TermOwnCRead 2>&1); then
  echo "$r4_termowncread_out"
  echo 'FAIL: TermOwnCRead.lean does not compile.'
  fail=1
fi
case "$r4_termowncread_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCRead.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCRead.vals_at \
    TermOwnCRead.caseC_of \
    TermOwnCRead.openOverCrOwnC_of2; do
  if ! echo "$r4_termowncread_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCRead.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermOwnCMain.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermOwnCMain.lean ..."
if ! r4_termowncmain_out=$(leanb TermOwnCMain 2>&1); then
  echo "$r4_termowncmain_out"
  echo 'FAIL: TermOwnCMain.lean does not compile.'
  fail=1
fi
case "$r4_termowncmain_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermOwnCMain.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermOwnCMain.ownC_of_prov; do
  if ! echo "$r4_termowncmain_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnCMain.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolF1.lean ------------------------------------------------------------
# R4 route: new module.
echo "building TermPoolF1.lean ..."
if ! r4_termpoolf1_out=$(leanb TermPoolF1 2>&1); then
  echo "$r4_termpoolf1_out"
  echo 'FAIL: TermPoolF1.lean does not compile.'
  fail=1
fi
case "$r4_termpoolf1_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolF1.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolF1.ptag_conv \
    TermPoolF1.ptag_keep \
    TermPoolF1.not_conv \
    TermPoolF1.crItem_of_crItemQ_mask \
    TermPoolF1.f1T_of; do
  if ! echo "$r4_termpoolf1_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolF1.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolTagOwn.lean --------------------------------------------------------
# R4 route: new module.
echo "building TermPoolTagOwn.lean ..."
if ! r4_termpooltagown_out=$(leanb TermPoolTagOwn 2>&1); then
  echo "$r4_termpooltagown_out"
  echo 'FAIL: TermPoolTagOwn.lean does not compile.'
  fail=1
fi
case "$r4_termpooltagown_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolTagOwn.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolTagOwn.addr_eq \
    TermPoolTagOwn.le_rpSum \
    TermPoolTagOwn.crKeys_add \
    TermPoolTagOwn.nWords_take_le \
    TermPoolTagOwn.inAcc_lt \
    TermPoolTagOwn.rpSum_ne \
    TermPoolTagOwn.piece_of_crIt \
    TermPoolTagOwn.poolTagOwnT_of; do
  if ! echo "$r4_termpooltagown_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolTagOwn.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPoolTagW.lean ----------------------------------------------------------
# R4 route: new module.
echo "building TermPoolTagW.lean ..."
if ! r4_termpooltagw_out=$(leanb TermPoolTagW 2>&1); then
  echo "$r4_termpooltagw_out"
  echo 'FAIL: TermPoolTagW.lean does not compile.'
  fail=1
fi
case "$r4_termpooltagw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermPoolTagW.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermPoolTagW.cutSto_egP \
    TermPoolTagW.fpAt_egP \
    TermPoolTagW.crItem_tr \
    TermPoolTagW.crItemQ_mask \
    TermPoolTagW.covL_tr \
    TermPoolTagW.promTwoNew_of \
    TermPoolTagW.poolTagP_of; do
  if ! echo "$r4_termpooltagw_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolTagW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSelfPlantK.lean --------------------------------------------------------
# R4 route: new module.
echo "building TermSelfPlantK.lean ..."
if ! r4_termselfplantk_out=$(leanb TermSelfPlantK 2>&1); then
  echo "$r4_termselfplantk_out"
  echo 'FAIL: TermSelfPlantK.lean does not compile.'
  fail=1
fi
case "$r4_termselfplantk_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSelfPlantK.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermSelfPlantK.selfPlantK_of \
    TermSelfPlantK.selfPlant_ofNK; do
  if ! echo "$r4_termselfplantk_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSelfPlantK.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermAnch.lean -----------------------------------------------------------
# certWin-D: `TermTyped.WrIniC` (the write-site anchor fact) holds; installed as a
# local instance in TermMain/TermSpawnRun proofs only (no statement mentions it).
echo "building TermAnch.lean ..."
if ! tanch_out=$(leanb TermAnch 2>&1); then
  echo "$tanch_out"
  echo 'FAIL: TermAnch.lean does not compile.'
  fail=1
fi
case "$tanch_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermAnch.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermAnch.wrSite_ok; do
  if ! echo "$tanch_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermAnch.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermWrSiteA.lean -----------------------------------------------------------
# (A″ plantcut) new module.
echo "building TermWrSiteA.lean ..."
if ! g282_termwrsitea_out=$(leanb TermWrSiteA 2>&1); then
  echo "$g282_termwrsitea_out"
  echo 'FAIL: TermWrSiteA.lean does not compile.'
  fail=1
fi
case "$g282_termwrsitea_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermWrSiteA.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    TermWrSiteA.wrSiteA_ok \
    TermWrSiteA.wrIniC \
    TermWrSiteA.wrSiteA_okU; do
  if ! echo "$g282_termwrsitea_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermWrSiteA.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermKidLabel.lean ------------------------------------------------
# (M0) kid-label arithmetic at stride c.n (kidLabel_*, kidFresh).
echo "building TermKidLabel.lean ..."
if ! m0_termkidlabel_out=$(leanb TermKidLabel 2>&1); then
  echo "$m0_termkidlabel_out"
  echo 'FAIL: TermKidLabel.lean does not compile.'
  fail=1
fi
case "$m0_termkidlabel_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermKidLabel.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermSys.kidLabel_eq" \
    "TermSys.kidLabel_cases" \
    "TermSys.kidLabel_of" \
    "TermSys.kidFresh"; do
  if ! echo "$m0_termkidlabel_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermKidLabel.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFreshU.lean --------------------------------------------------
# (M0) FreshU: unborn stripes fresh and unowned; preserved by thread/promise steps, holds at init.
echo "building TermFreshU.lean ..."
if ! m0_termfreshu_out=$(leanb TermFreshU 2>&1); then
  echo "$m0_termfreshu_out"
  echo 'FAIL: TermFreshU.lean does not compile.'
  fail=1
fi
case "$m0_termfreshu_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFreshU.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermFreshU.freshX_thread" \
    "TermFreshU.ownZ_thread" \
    "TermFreshU.freshX_prom" \
    "TermFreshU.ownZ_prom" \
    "TermFreshU.freshU_thread" \
    "TermFreshU.freshU_prom" \
    "TermFreshU.ownZ_mono" \
    "TermFreshU.freshU_le" \
    "TermFreshU.hD_thread" \
    "TermFreshU.hD_prom" \
    "TermFreshU.freshU_init"; do
  if ! echo "$m0_termfreshu_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFreshU.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermScalIni.lean ------------------------------------------------------------
# (scalIni) the scalar clause `SysInvN.scalIni`: kept by the plant, the thread step, withFp, the box.
echo "building TermScalIni.lean ..."
if ! s1_termscalini_out=$(leanb TermScalIni 2>&1); then
  echo "$s1_termscalini_out"
  echo 'FAIL: TermScalIni.lean does not compile.'
  fail=1
fi
case "$s1_termscalini_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermScalIni.lean theorem has a sorry"
    fail=1 ;;
esac
# TermScalIni: every #print axioms theorem, std axioms only.
for thm in \
    "TermScalIni.scalIni_le" \
    "TermScalIni.scalIni_init" \
    "TermScalIni.scalIni_ini0" \
    "TermScalIni.slotCnt_nonarr" \
    "TermScalIni.np_nonarr" \
    "TermScalIni.npZ_nonarr" \
    "TermScalIni.plantN_nonarr" \
    "TermScalIni.ini_le_rini_of_ownHid" \
    "TermScalIni.fresh_pfr_none" \
    "TermScalIni.cut_ini_le" \
    "TermScalIni.scalIni_egP" \
    "TermScalIni.plantN0_of" \
    "TermScalIni.scalIni_egT" \
    "TermScalIni.hscal_of" \
    "TermScalIni.scalIni_withFp"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${s1_termscalini_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermScalIni.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- G5: the certificate-window proof (84 modules, CertWinProof) -------------
# (G5) `CertWinProof.certWinC_of`/`certWinP_of` and their layers, built before TermMain, which
# imports them (TermMainPre, EtaCertWinSnd).  The *Axioms modules print their axiom census.
echo "building the 84 G5 certificate-window modules ..."
for g5m in AxAll VRb Emb PubPos VRbClosure TvarB Head VRzLemmas PubPosL FlagB GenLayer KLayer ShadowPub ShadowPubStep ShadowPubAxioms ShadowWinChain ShadowWinChainAxioms WLayer WrIniInst ELayer ELayerAxioms TermMainPre AnchorFrameTyping AnchorFrameAxioms WinScope WinScopeAxioms WinStart WinStartAxioms WinPubSplit WinPremises WinPremisesAxioms KLayerAxioms MergeP MergeStmt MergeH Merge MergeQ PubPosM MergeV MergeW MergeR ZRel Frame CopyPlan PairNat EtaC LiftG LiftE LiftH Lift LiftPosZero DPub LiftTidBox LiftUpClosed VarBox EtaA EtaB EtaD StackFrameLevel StackInduction StackLevelZero VRLift StackResFree StackAxioms CopyPlanAxioms NLayer EtaL EtaS EtaP EtaNC EtaR ScalB PlantedHolder EtaN EtaO ContIV EtaFD BornU BornW EtaW EtaCertWinFst EtaCertWinSnd EtaCertWinAxioms OwnerExemptWitness; do
  if ! g5_out=$(leanb $g5m 2>&1); then
    echo "$g5_out"
    echo "FAIL: $g5m.lean does not compile: the certificate-window proof no longer goes through."
    fail=1
  fi
  case "$g5_out" in
    *"declaration uses"*|*sorryAx*)
      echo "FAIL: a $g5m.lean theorem has a sorry"
      fail=1 ;;
  esac
done

# --- TermMain.lean -----------------------------------------------------------
# Top-down skeleton of headline 1: every open proof
# obligation is a field of `Obligations`; `sysInv_step`/`sysInv_run` carry the
# net-key-bound invariant `SysInvN` along machine runs and `machine_tokens_main`
# is the headline modulo `Obligations`.  Discharging a field deletes it here.
echo "building TermMain.lean ..."
if ! tmain_out=$(leanb TermMain 2>&1); then
  echo "$tmain_out"
  echo 'FAIL: TermMain.lean does not compile: the top-down skeleton of headline 1 no longer goes through.'
  fail=1
fi
case "$tmain_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermMain.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in Obligations.seenHid EFoot_unpf MintStep_unpf cfgCoh_of_initShape pwf0_of_initOK promNodup_of_initOK Obligations.retIall Obligations.progT Obligations.scope Obligations.iall Obligations.dwf Obligations.residualNoTicket Obligations.noTicket initOK_of machine_tokens_main sysInv_step sysInv_run token_unique_net token_unique_final reachable_typed ObligationsF.toObligations machine_tokens_mainF token_unique_netF token_unique_finalF reachable_typedF niDeep_of_drf opAtom_free opNI_of Obligations.opNI; do
  if ! echo "$tmain_out" | grep -qF "'TermMain.$thm' "; then
    echo "FAIL: TermMain.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done
# R4 route: theorems added to TermMain.lean.
for thm in \
    TermMain.TOutC_mono \
    TermMain.poolStaging_of \
    TermMain.stepAtCrS \
    TermMain.sysInv_thread \
    TermMain.sysInv_threadR \
    TermMain.sysInv_threadRP; do
  if ! echo "$tmain_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMain.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# The witness-frame variants of the thread/promise masters.
for thm in \
    TermMain.sysInv_threadRPW \
    TermMain.sysInv_promPW; do
  if ! echo "$tmain_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMain.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# Shared obligation theorem in TermMain.lean.
for thm in \
    TermMain.ObligationsF.toObligationsC; do
  if ! echo "$tmain_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMain.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# (2b) theorems added to TermMain.lean.
for thm in \
    "tokUniq_of_knet" \
    "ofF_bot" \
    "SpArms.bot" \
    "ObligationsFX.toObligationsCX"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${tmain_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMain.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- C1.lean ----------------------------------------------------------
# (2b) C1 (after TermMain).
echo "building C1.lean ..."
if ! b2_c1_out=$(leanb C1 2>&1); then
  echo "$b2_c1_out"
  echo 'FAIL: C1.lean does not compile.'
  fail=1
fi
case "$b2_c1_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a C1.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) C1: every #print axioms theorem, std axioms only.
for thm in \
    "noPredU_sys" \
    "noPredU_of_noProm"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_c1_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: C1.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveMach.lean -------------------------------------------------------
# Liveness L1: labelled stuttering runs of the promise
# machine, crash sets (with the no-promise guard), F4 fairness, frozen
# suffixes (views stop rising, waiting cas stale, loads old), crash_sim, and
# class_run: a closed class with a thread step inside is a fair livelock run.
echo "building TermLiveMach.lean ..."
if ! tlm_out=$(leanb TermLiveMach 2>&1); then
  echo "$tlm_out"
  echo 'FAIL: TermLiveMach.lean does not compile: the machine-level liveness vocabulary no longer goes through.'
  fail=1
fi
case "$tlm_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermLiveMach.lean theorem has a sorry"
    fail=1 ;;
esac
# new theorems of TermLiveMach.lean (extern steps under outstanding promises): std axioms only
for thm in TermLiveMach.extSteps_setTh; do
  if ! echo "$tlm_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveMach.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# (F2) the explorer's extern moves are machine extern steps: std axioms only
if ! echo "$tlm_out" | grep -qE "'TermLiveMach.extSuccs_sound' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
  echo "FAIL: TermLiveMach.lean: '#print axioms extSuccs_sound' missing or non-standard axioms"
  fail=1
fi
for thm in run_freeze_or_grow frozen_noraise frozen_stale_cas frozen_load_stale crash_sim class_run certB_sound promised_rmw_may_block; do
  if ! echo "$tlm_out" | grep -qE "'TermLiveMach.$thm' (depends on axioms|does not depend on any axioms)"; then
    echo "FAIL: TermLiveMach.lean's '#print axioms $thm' is missing."
    fail=1
  fi
done

# --- TermLiveGrow.lean ------------------------------------------------
# (2b) new module.
echo "building TermLiveGrow.lean ..."
if ! b2_termlivegrow_out=$(leanb TermLiveGrow 2>&1); then
  echo "$b2_termlivegrow_out"
  echo 'FAIL: TermLiveGrow.lean does not compile.'
  fail=1
fi
case "$b2_termlivegrow_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermLiveGrow.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermLiveGrow: every #print axioms theorem, std axioms only.
for thm in \
    "inducedX_iff_shift" \
    "restrict_sound" \
    "soundX_of_sound" \
    "runX_size_mono" \
    "runX_cap" \
    "runX_size_le" \
    "runX_stable" \
    "eventually_restrict" \
    "ev_noGrow" \
    "fair_shift" \
    "runX_freeze_or_grow" \
    "frozenX_noraise" \
    "frozenX_views_const" \
    "frozenX_stale_cas" \
    "frozenX_load_stale" \
    "class_runX" \
    "reachS_mem_eq" \
    "reachS_size_eq" \
    "classS_coh_eq" \
    "TermLiveGrow.CohLeX.ofCohLe" \
    "TermLiveGrow.CohLeX.toCohLe" \
    "TermLiveGrow.CohLeX.refl" \
    "TermLiveGrow.CohLeX.trans" \
    "TermLiveGrow.restrict_S" \
    "TermLiveGrow.moveX_mem" \
    "TermLiveGrow.moveX_coh" \
    "TermLiveGrow.moveX_size" \
    "TermLiveGrow.run_of_restrict" \
    "TermLiveGrow.runX_mem" \
    "TermLiveGrow.runX_coh" \
    "TermLiveGrow.runX_size_cap" \
    "TermLiveGrow.shift_run" \
    "TermLiveGrow.ev_unshift" \
    "TermLiveGrow.ev_shift" \
    "TermLiveGrow.often_shift" \
    "TermLiveGrow.often_unshift" \
    "TermLiveGrow.ev_mono" \
    "TermLiveGrow.often_mono" \
    "TermLiveGrow.frozen_unshift" \
    "TermLiveGrow.frozen_shift" \
    "TermLiveGrow.liveX_of_live" \
    "TermLiveGrow.live_shift" \
    "TermLiveGrow.stable_past" \
    "TermLiveGrow.chain_size" \
    "TermLiveGrow.classHyp_restrict" \
    "TermLiveGrow.reachS_mem" \
    "TermLiveGrow.reachS_size" \
    "TermLiveGrow.reachS_coh" \
    "TermLiveGrow.livelockX_of_livelock"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termlivegrow_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveGrow.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveX.lean ---------------------------------------------------
# (2b) new module.
echo "building TermLiveX.lean ..."
if ! b2_termlivex_out=$(leanb TermLiveX 2>&1); then
  echo "$b2_termlivex_out"
  echo 'FAIL: TermLiveX.lean does not compile.'
  fail=1
fi
case "$b2_termlivex_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermLiveX.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermLiveX: every #print axioms theorem, std axioms only.
for thm in \
    "spawn_iff" \
    "spawnBy_sound" \
    "mstepX_iff_StepX" \
    "reachS_iff_stepsX" \
    "machineX_sound" \
    "restrict_machineX" \
    "machineX_size_mono" \
    "machineX_size_cap" \
    "machineX_ev_spawnFree" \
    "machineX_eventually_machine" \
    "TermLiveX.spawnS_coh" \
    "TermLiveX.spawnCfg_size" \
    "TermLiveX.spawnCfg_get" \
    "TermLiveX.mstepX_thr"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termlivex_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveX.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveXE.lean --------------------------------------------------
# (2b) new module.
echo "building TermLiveXE.lean ..."
if ! b2_termlivexe_out=$(leanb TermLiveXE 2>&1); then
  echo "$b2_termlivexe_out"
  echo 'FAIL: TermLiveXE.lean does not compile.'
  fail=1
fi
case "$b2_termlivexe_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermLiveXE.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermLiveXE: every #print axioms theorem, std axioms only.
for thm in \
    "spawnSucc_iff" \
    "spawnMoves_iff" \
    "spawn_offered" \
    "site_not_silent" \
    "spawn_exit" \
    "livelock_runX"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termlivexe_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveXE.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveM0.lean --------------------------------------------------
# (2b) new module.
echo "building TermLiveM0.lean ..."
if ! b2_termlivem0_out=$(leanb TermLiveM0 2>&1); then
  echo "$b2_termlivem0_out"
  echo 'FAIL: TermLiveM0.lean does not compile.'
  fail=1
fi
case "$b2_termlivem0_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermLiveM0.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermLiveM0: every #print axioms theorem, std axioms only.
for thm in \
    "TermLiveGrow.machine_cap" \
    "TermLiveGrow.machine_soundX"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termlivem0_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveM0.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveXM0.lean -------------------------------------------------
# (2b) new module.
echo "building TermLiveXM0.lean ..."
if ! b2_termlivexm0_out=$(leanb TermLiveXM0 2>&1); then
  echo "$b2_termlivexm0_out"
  echo 'FAIL: TermLiveXM0.lean does not compile.'
  fail=1
fi
case "$b2_termlivexm0_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermLiveXM0.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermLiveXM0: every #print axioms theorem, std axioms only.
for thm in \
    "spawnCfg_cap" \
    "mstepX_cap" \
    "machineXC_sound" \
    "reachS_iff_stepsXC"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termlivexm0_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveXM0.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermBufDefs.lean -----------------------------------------------------
# Spawn: (d') R1 buffer-scope check definitions (bufTable/bufWalk/ProgBufOK/InitBufOK).
echo "building TermBufDefs.lean ..."
if ! g266_bufdefs_out=$(leanb TermBufDefs 2>&1); then
  echo "$g266_bufdefs_out"
  echo 'FAIL: TermBufDefs.lean does not compile.'
  fail=1
fi
case "$g266_bufdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBufDefs.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermSpawnSim.lean ----------------------------------------------------
# Spawn: Phantom stack-bottom frame: tstep/threadSteps/certification commute with appending f0.
echo "building TermSpawnSim.lean ..."
if ! g266_spsim_out=$(leanb TermSpawnSim 2>&1); then
  echo "$g266_spsim_out"
  echo 'FAIL: TermSpawnSim.lean does not compile.'
  fail=1
fi
case "$g266_spsim_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnSim.lean theorem has a sorry"
    fail=1 ;;
esac

# new theorems of TermSpawnSim.lean (extern steps under outstanding promises): std axioms only
for thm in TermSpawnSim.extSteps_phantC; do
  if ! echo "$g266_spsim_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnSim.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# --- TermSpawnPh.lean -----------------------------------------------------
# Spawn: Phantom configuration phantC: SysInvW/InitOK transport.
echo "building TermSpawnPh.lean ..."
if ! g266_spph_out=$(leanb TermSpawnPh 2>&1); then
  echo "$g266_spph_out"
  echo 'FAIL: TermSpawnPh.lean does not compile.'
  fail=1
fi
case "$g266_spph_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnPh.lean theorem has a sorry"
    fail=1 ;;
esac

# (M0) new lemmas of TermSpawnPh.lean: std axioms only
for thm in "TermSpawnSim.phantC_n"; do
  if ! echo "$g266_spph_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnPh.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnDefs.lean ---------------------------------------------------
# Spawn: Spawn headline definitions (Kid, kidTh, spawnS, KidOK, f0, phant, StartOK) and the StartOK headline.
echo "building TermSpawnDefs.lean ..."
if ! g266_spdefs_out=$(leanb TermSpawnDefs 2>&1); then
  echo "$g266_spdefs_out"
  echo 'FAIL: TermSpawnDefs.lean does not compile.'
  fail=1
fi
case "$g266_spdefs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnDefs.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermSpawn.toObligationsS TermSpawn.machine_tokens_mainS TermSpawn.startOK_of_initOK; do
  if ! echo "$g266_spdefs_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnDefs.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- SpawnNoSpawn.lean ------------------------------------------------
# (2b) spawn-free programs: StepsX = Steps.
echo "building SpawnNoSpawn.lean ..."
if ! b2_spawnnospawn_out=$(leanb SpawnNoSpawn 2>&1); then
  echo "$b2_spawnnospawn_out"
  echo 'FAIL: SpawnNoSpawn.lean does not compile.'
  fail=1
fi
case "$b2_spawnnospawn_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a SpawnNoSpawn.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) SpawnNoSpawn: every #print axioms theorem, std axioms only.
for thm in \
    "enter_noS" \
    "mem_optList" \
    "callFrame_body" \
    "tstep_noS" \
    "noS_iff_expr" \
    "noS_of_expr" \
    "expr_of_noS" \
    "cfgNoS_iff" \
    "getElem?_set!_or" \
    "cfgNoS_thread" \
    "cfgNoS_prom" \
    "cfgNoS_step" \
    "no_spawn" \
    "stepsR_of_stepsX_aux" \
    "stepsX_iff_stepsNo_of_noSpawn" \
    "stepsNo_iff_steps" \
    "stepsX_iff_steps_of_noSpawn" \
    "noSpawnC_run" \
    "noSpawnC_spawnS"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_spawnnospawn_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: SpawnNoSpawn.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermArchE.lean / TermArchENS.lean / TermArchS.lean ---------------------
# TSO ⊆ ARM lifted from `Step` to runs with extern steps (and, under a spawn-simulation
# premise, to all of `StepsE`), traces equal.  ENS: spawn-free programs, no `SpawnSim` premise.
# S: the spawn simulation is proved (`spawn_sim`, with `TValLe.rts` relaxed to `≤`), so all
# of `StepsE` (spawning programs included) has no `SpawnSim` premise.
for mod in TermArchE TermArchENS TermArchS; do
  echo "building $mod.lean ..."
  if ! tae_out=$(leanb $mod 2>&1); then
    echo "$tae_out"
    echo "FAIL: $mod.lean does not compile: the TSO-to-ARM run/trace lift no longer goes through."
    fail=1
  fi
  case "$tae_out" in
    *"declaration uses"*|*sorryAx*)
      echo "FAIL: a $mod.lean theorem has a sorry"
      fail=1 ;;
  esac
  case $mod in
    TermArchE) thms="hwf_of_noProm Step_simT Ext_sim stepsG_sim tso_stepsG_subset_arm
      tso_extRuns_subset_arm tso_stepsE_subset_arm tso_extTraces_subset_arm tso_traces_subset_arm
      tso_stepsE_final_subset_arm" ;;
    TermArchENS) thms="cfgNoS_ext stepsE_extRuns_of_noSpawn tso_stepsE_subset_arm_noSpawn
      tso_traces_subset_arm_noSpawn" ;;
    TermArchS) thms="tvle_bump wsle_bump thsLe_push allP_spawnT spawn_sim tso_stepsE_subset_arm_full
      tso_traces_subset_arm_full tso_stepsE_final_subset_arm_full" ;;
  esac
  for thm in $thms; do
    if ! echo "$tae_out" | grep -qE "'$mod.$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
      echo "FAIL: $mod.lean: '#print axioms $thm' missing or non-standard axioms"
      fail=1
    fi
  done
done

# --- TermSpawn.lean -------------------------------------------------------
# Spawn: The spawn reshape keeps SysInvN (sysInvN_spawnS), kid and child-0 thread invariants.
echo "building TermSpawn.lean ..."
if ! g266_spawn_out=$(leanb TermSpawn 2>&1); then
  echo "$g266_spawn_out"
  echo 'FAIL: TermSpawn.lean does not compile.'
  fail=1
fi
case "$g266_spawn_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawn.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermSpawn.sysInvN_spawnS TermSpawn.thSys_kid TermSpawn.thSys_child0; do
  if ! echo "$g266_spawn_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawn.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# (M0) new lemmas of TermSpawn.lean: std axioms only
for thm in "TermSpawn.spawnS_n" "TermSpawn.spawnS_lbase_n1" "TermSpawn.kidP" "TermSpawn.gFreshL_of_X" "TermSpawn.kidG" "TermSpawn.kidOwn"; do
  if ! echo "$g266_spawn_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawn.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermInterfObs.lean ---------------------------------------------------
# Spawn: Observer (non-thread) variants of the PubDefP/PubPair/PubLive interference lemmas.
echo "building TermInterfObs.lean ..."
if ! g266_interfobs_out=$(leanb TermInterfObs 2>&1); then
  echo "$g266_interfobs_out"
  echo 'FAIL: TermInterfObs.lean does not compile.'
  fail=1
fi
case "$g266_interfobs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermInterfObs.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermInterfObs.pcl7_pubDefP_obs TermInterfObs.pcl9e_pubLive_obs TermInterfObs.pcl9d_pubPair_obs TermInterfObs.cl9e_pubLive_obs TermInterfObs.cl9d_pubPair_obs TermInterfObs.cl7_pubDefP_obs; do
  if ! echo "$g266_interfobs_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermInterfObs.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnRun.lean ----------------------------------------------------
# Spawn: SysInvO (SysInvN + OwnLive + ObsAll) along runs.
echo "building TermSpawnRun.lean ..."
if ! g266_sprun_out=$(leanb TermSpawnRun 2>&1); then
  echo "$g266_sprun_out"
  echo 'FAIL: TermSpawnRun.lean does not compile.'
  fail=1
fi
case "$g266_sprun_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnRun.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermSpawn.sysInvO_run TermSpawn.sysInvO_threadRW TermSpawn.sysInvO_promW; do
  if ! echo "$g266_sprun_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnRun.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnKidMem.lean ---------------------------------------------
# (2b) kid memory facts.
echo "building TermSpawnKidMem.lean ..."
if ! b2_termspawnkidmem_out=$(leanb TermSpawnKidMem 2>&1); then
  echo "$b2_termspawnkidmem_out"
  echo 'FAIL: TermSpawnKidMem.lean does not compile.'
  fail=1
fi
case "$b2_termspawnkidmem_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnKidMem.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnKidMem: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnKidMem.cutSto_kid" \
    "TermSpawnKidMem.cutSto_kid_own" \
    "TermSpawnKidMem.cut_withFp" \
    "TermSpawnKidMem.valOf_fp" \
    "TermSpawnKidMem.memInv_withFp" \
    "TermSpawnKidMem.pub3_withFp" \
    "TermSpawnKidMem.memInv_kidM0" \
    "TermSpawnKidMem.memInv_kidM" \
    "TermSpawnKidMem.obsAll_kid"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnkidmem_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnKidMem.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnF0.lean -----------------------------------------------------
# Spawn: Typing the phantom frame f0 and re-typing the setup frame above it.
echo "building TermSpawnF0.lean ..."
if ! g266_spf0_out=$(leanb TermSpawnF0 2>&1); then
  echo "$g266_spf0_out"
  echo 'FAIL: TermSpawnF0.lean does not compile.'
  fail=1
fi
case "$g266_spf0_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnF0.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermSpawnSim.initOK_phant; do
  if ! echo "$g266_spf0_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnF0.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnStart.lean --------------------------------------------------
# Spawn: SysInvO at the clean start and along the phantom setup run.
echo "building TermSpawnStart.lean ..."
if ! g266_spstart_out=$(leanb TermSpawnStart 2>&1); then
  echo "$g266_spstart_out"
  echo 'FAIL: TermSpawnStart.lean does not compile.'
  fail=1
fi
case "$g266_spstart_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnStart.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermSpawn.sysInvO_of_initOK TermSpawn.sysInvO_phant_run; do
  if ! echo "$g266_spstart_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnStart.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnKid.lean ----------------------------------------------------
# Spawn: The setup result is a value of R0 (vr_of_ret).
echo "building TermSpawnKid.lean ..."
if ! g266_spkid_out=$(leanb TermSpawnKid 2>&1); then
  echo "$g266_spkid_out"
  echo 'FAIL: TermSpawnKid.lean does not compile.'
  fail=1
fi
case "$g266_spkid_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnKid.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermSpawnEntry.lean --------------------------------------------------
# Spawn: A kid's entry frame at any cut (entryR_of).
echo "building TermSpawnEntry.lean ..."
if ! g266_spentry_out=$(leanb TermSpawnEntry 2>&1); then
  echo "$g266_spentry_out"
  echo 'FAIL: TermSpawnEntry.lean does not compile.'
  fail=1
fi
case "$g266_spentry_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnEntry.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermSpawnArg.lean ----------------------------------------------------
# Spawn: A kid's argument at its cut (kid_val).
echo "building TermSpawnArg.lean ..."
if ! g266_sparg_out=$(leanb TermSpawnArg 2>&1); then
  echo "$g266_sparg_out"
  echo 'FAIL: TermSpawnArg.lean does not compile.'
  fail=1
fi
case "$g266_sparg_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnArg.lean theorem has a sorry"
    fail=1 ;;
esac

# --- TermSpawnMid.lean ------------------------------------------------
# (2b) spawn mid-step invariant (exports TermSpawnStep.spawnT use).
echo "building TermSpawnMid.lean ..."
if ! b2_termspawnmid_out=$(leanb TermSpawnMid 2>&1); then
  echo "$b2_termspawnmid_out"
  echo 'FAIL: TermSpawnMid.lean does not compile.'
  fail=1
fi
case "$b2_termspawnmid_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnMid.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnMid: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnMid.memHeldG_spawnT" \
    "TermSpawnMid.promsOK_kid" \
    "TermSpawnMid.thSys_kidM" \
    "TermSpawnMid.arg_move" \
    "TermSpawnMid.kid_tyM" \
    "TermSpawnMid.thSys_parM" \
    "TermSpawnMid.thSys_otherM" \
    "TermSpawnMid.mem_allProms_spawnT" \
    "TermSpawnMid.spawnT_size" \
    "TermSpawnMid.spawnT_get_kid" \
    "TermSpawnMid.spawnT_get_par" \
    "TermSpawnMid.spawnT_get_ne" \
    "TermSpawnMid.EgK_fp_kid" \
    "TermSpawnMid.EgK_fp_ne" \
    "TermSpawnMid.cutSto_EgK" \
    "TermSpawnMid.cut_EgK_ne" \
    "TermSpawnMid.InclS_cut_EgK" \
    "TermSpawnMid.spawnT_get_cases" \
    "TermSpawnMid.PromAtG_EgK" \
    "TermSpawnMid.mem_PromAtG_spawnT" \
    "TermSpawnMid.finv_entryR" \
    "TermSpawnMid.entryR_ofR" \
    "TermSpawnMid.thSys_EgK" \
    "TermSpawnMid.stOf_par"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnmid_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMid.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnArms.lean -----------------------------------------------
# (2b) spawn single-step prom lemmas (copy-rule owner).
echo "building TermSpawnArms.lean ..."
if ! b2_termspawnarms_out=$(leanb TermSpawnArms 2>&1); then
  echo "$b2_termspawnarms_out"
  echo 'FAIL: TermSpawnArms.lean does not compile.'
  fail=1
fi
case "$b2_termspawnarms_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnArms.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnArms: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnMid.promViewLt_spawnT" \
    "TermSpawnMid.promPos_spawnT" \
    "TermSpawnMid.promNodupI_spawnT" \
    "TermSpawnMid.spawnT_prom"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnarms_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnArms.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnRunX.lean -----------------------------------------------
# (2b) runs with spawn steps.
echo "building TermSpawnRunX.lean ..."
if ! b2_termspawnrunx_out=$(leanb TermSpawnRunX 2>&1); then
  echo "$b2_termspawnrunx_out"
  echo 'FAIL: TermSpawnRunX.lean does not compile.'
  fail=1
fi
case "$b2_termspawnrunx_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnRunX.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnRunX: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnRunX.RunsG.snoc" \
    "TermSpawnRunX.ownLive_spawnT" \
    "TermSpawnRunX.obsAll_spawnT" \
    "TermSpawnRunX.sysInvO_spawnT" \
    "TermSpawnRunX.sysInvO_runG"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnrunx_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnRunX.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnGlobM.lean ----------------------------------------------
# (2b) TgtOK mono across spawnT.
echo "building TermSpawnGlobM.lean ..."
if ! b2_termspawnglobm_out=$(leanb TermSpawnGlobM 2>&1); then
  echo "$b2_termspawnglobm_out"
  echo 'FAIL: TermSpawnGlobM.lean does not compile.'
  fail=1
fi
case "$b2_termspawnglobm_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnGlobM.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnGlobM: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnGlobM.pSumAt_spawnT_lt" \
    "TermSpawnGlobM.pSumAt_spawnT_kid" \
    "TermSpawnGlobM.rsum_ext" \
    "TermSpawnGlobM.nsum_ext" \
    "TermSpawnGlobM.extZ_lt" \
    "TermSpawnGlobM.extZT_lt" \
    "TermSpawnGlobM.thSum_bal_spawnT" \
    "TermSpawnGlobM.thSum_db_spawnT" \
    "TermSpawnGlobM.nsum_cr_spawnT" \
    "TermSpawnGlobM.nsum_db_spawnT" \
    "TermSpawnGlobM.crPl_extZT" \
    "TermSpawnGlobM.poolTag_spawnT" \
    "TermSpawnGlobM.overCrG_spawnT" \
    "TermSpawnGlobM.tminG_spawnT_ne" \
    "TermSpawnGlobM.tminG_nil" \
    "TermSpawnGlobM.spawnT_idx" \
    "TermSpawnGlobM.bal_spawnT" \
    "TermSpawnGlobM.keyNet_spawnT" \
    "TermSpawnGlobM.ridOK_spawnT" \
    "TermSpawnGlobM.ownZ_spawnT" \
    "TermSpawnGlobM.pool_spawnT" \
    "TermSpawnGlobM.easy_spawnT" \
    "TermSpawnGlobM.ownKeyOwn_spawnT" \
    "TermSpawnGlobM.ownPub_spawnT" \
    "TermSpawnGlobM.boxFrOwn_spawnT" \
    "TermSpawnGlobM.cellOwn_spawnT" \
    "TermSpawnGlobM.granW_spawnT" \
    "TermSpawnGlobM.ptrGL_spawnT" \
    "TermSpawnGlobM.boxPlantSep_spawnT" \
    "TermSpawnGlobM.plantIdx_spawnT" \
    "TermSpawnGlobM.boxTop_spawnT" \
    "TermSpawnGlobM.predHold_spawnT"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnglobm_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnGlobM.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermFreshUSpawn.lean ---------------------------------------------
# (2b) freshU_spawnT.
echo "building TermFreshUSpawn.lean ..."
if ! b2_termfreshuspawn_out=$(leanb TermFreshUSpawn 2>&1); then
  echo "$b2_termfreshuspawn_out"
  echo 'FAIL: TermFreshUSpawn.lean does not compile.'
  fail=1
fi
case "$b2_termfreshuspawn_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermFreshUSpawn.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermFreshUSpawn: every #print axioms theorem, std axioms only.
for thm in \
    "TermFreshU.freshU_spawnT" \
    "TermFreshU.kid_of_freshU"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termfreshuspawn_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermFreshUSpawn.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnMidBridge.lean ------------------------------------------
# (2b) spawnPar/spawnKid shape bridges.
echo "building TermSpawnMidBridge.lean ..."
if ! b2_termspawnmidbridge_out=$(leanb TermSpawnMidBridge 2>&1); then
  echo "$b2_termspawnmidbridge_out"
  echo 'FAIL: TermSpawnMidBridge.lean does not compile.'
  fail=1
fi
case "$b2_termspawnmidbridge_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnMidBridge.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnMidBridge: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnMidZ.spawnPar_hpar" \
    "TermSpawnMidZ.spawnKid_shape" \
    "TermSpawnMidZ.spawnPar_shape"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnmidbridge_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMidBridge.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnTy.lean -------------------------------------------------
# (2b) spawn typing facts.
echo "building TermSpawnTy.lean ..."
if ! b2_termspawnty_out=$(leanb TermSpawnTy 2>&1); then
  echo "$b2_termspawnty_out"
  echo 'FAIL: TermSpawnTy.lean does not compile.'
  fail=1
fi
case "$b2_termspawnty_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnTy.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnTy: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnMid.kidEntryOK_of" \
    "TermSpawnMid.arg_of_site" \
    "TermSpawnMid.par_of_site" \
    "TermSpawnMid.wf_of_tb" \
    "TermSpawnMid.use_copy" \
    "TermSpawnMid.spawnPrem_of"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnty_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnTy.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnMidGlob.lean --------------------------------------------
# (2b) spawn mid: globals.
echo "building TermSpawnMidGlob.lean ..."
if ! b2_termspawnmidglob_out=$(leanb TermSpawnMidGlob 2>&1); then
  echo "$b2_termspawnmidglob_out"
  echo 'FAIL: TermSpawnMidGlob.lean does not compile.'
  fail=1
fi
case "$b2_termspawnmidglob_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnMidGlob.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnMidGlob: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnMid.plt_spawnT" \
    "TermSpawnMid.disj_spawnT" \
    "TermSpawnMid.promIni_spawnT" \
    "TermSpawnMid.promTy_spawnT" \
    "TermSpawnMid.promNU_spawnT" \
    "TermSpawnMid.promNoTwo_spawnT" \
    "TermSpawnMid.promInCut_spawnT" \
    "TermSpawnMid.promClos_spawnT" \
    "TermSpawnMid.fgnClos_spawnT" \
    "TermSpawnMid.promAbove_spawnT" \
    "TermSpawnMid.fpfree_spawnT" \
    "TermSpawnMid.proms_spawnT" \
    "TermSpawnMid.vwr_spawnT" \
    "TermSpawnMid.fpok_spawnT" \
    "TermSpawnMid.ownCoh_spawnT" \
    "TermSpawnMid.riniCoh_spawnT" \
    "TermSpawnMid.fresh_spawnT" \
    "TermSpawnMid.cfgCoh_spawnT" \
    "TermSpawnMid.fgnCnt_spawnT" \
    "TermSpawnMid.fenceSy_vWr" \
    "TermSpawnMid.fenceSy_coh" \
    "TermSpawnMid.spawnT_promAll" \
    "TermSpawnMid.spawnT_thAll" \
    "TermSpawnMid.bf_spawnT" \
    "TermSpawnMid.frle_spawnT" \
    "TermSpawnMid.frlt_spawnT" \
    "TermSpawnMid.rle_spawnT" \
    "TermSpawnMid.vWr_par" \
    "TermSpawnMid.stoW_spawnT"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnmidglob_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMidGlob.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnMidKid.lean ---------------------------------------------
# (2b) spawn mid: kid.
echo "building TermSpawnMidKid.lean ..."
if ! b2_termspawnmidkid_out=$(leanb TermSpawnMidKid 2>&1); then
  echo "$b2_termspawnmidkid_out"
  echo 'FAIL: TermSpawnMidKid.lean does not compile.'
  fail=1
fi
case "$b2_termspawnmidkid_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnMidKid.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnMidKid: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnMid.thSys_kidFull" \
    "TermSpawnMid.thr_spawnT" \
    "TermSpawnMid.thLbl_kid" \
    "TermSpawnMid.thLbl_par"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnmidkid_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMidKid.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnMidAsm.lean ---------------------------------------------
# (2b) sysInvN_spawnMid.
echo "building TermSpawnMidAsm.lean ..."
if ! b2_termspawnmidasm_out=$(leanb TermSpawnMidAsm 2>&1); then
  echo "$b2_termspawnmidasm_out"
  echo 'FAIL: TermSpawnMidAsm.lean does not compile.'
  fail=1
fi
case "$b2_termspawnmidasm_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnMidAsm.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnMidAsm: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnMid.sysInvN_spawnMid"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnmidasm_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMidAsm.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermBox.lean ---------------------------------------------------------------
# (E2, R2z) the ghost thread box `EgB` and its environment facts.
echo "building TermBox.lean ..."
if ! e2_termbox_out=$(leanb TermBox 2>&1); then
  echo "$e2_termbox_out"
  echo 'FAIL: TermBox.lean does not compile.'
  fail=1
fi
case "$e2_termbox_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBox.lean theorem has a sorry"
    fail=1 ;;
esac
# (E2) TermBox: every #print axioms theorem, std axioms only.
for thm in \
    "TermBox.EgB_sto_ne" \
    "TermBox.EgB_pfr_ne" \
    "TermBox.cutSto_EgB_ne" \
    "TermBox.cutSto_EgB_self" \
    "TermBox.cutSto_fresh" \
    "TermBox.cut_EgB" \
    "TermBox.incl_box" \
    "TermBox.thInvRE_box" \
    "TermBox.thInvE_box"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${e2_termbox_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBox.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermBoxT.lean --------------------------------------------------------------
# (E2, R2z) `thSys_box`: a thread invariant survives the box (one lemma per clause).
echo "building TermBoxT.lean ..."
if ! e2_termboxt_out=$(leanb TermBoxT 2>&1); then
  echo "$e2_termboxt_out"
  echo 'FAIL: TermBoxT.lean does not compile.'
  fail=1
fi
case "$e2_termboxt_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBoxT.lean theorem has a sorry"
    fail=1 ;;
esac
# (E2) TermBoxT: every #print axioms theorem, std axioms only.
for thm in \
    "TermBox.thSys_box" \
    "TermBox.boxE_sto_self" \
    "TermBox.boxE_pfr_self" \
    "TermBox.boxE_sto_ne" \
    "TermBox.boxE_pfr_ne" \
    "TermBox.boxE_rc" \
    "TermBox.boxE_own_ne" \
    "TermBox.boxE_sto_ne_of" \
    "TermBox.incl_boxE" \
    "TermBox.wordOK_boxE" \
    "TermBox.pairOK_boxE" \
    "TermBox.valOf_boxE" \
    "TermBox.hiddenP_boxE" \
    "TermBox.hiddenP_nomsg" \
    "TermBox.memOKP_boxE" \
    "TermBox.ownOKSF_boxE" \
    "TermBox.privCoh_boxE" \
    "TermBox.freshLP_boxE" \
    "TermBox.seenLE_boxE" \
    "TermBox.not_seen_of" \
    "TermBox.ownHidP_boxE" \
    "TermBox.pubDefP_boxE" \
    "TermBox.ownPubV_boxE" \
    "TermBox.segOf_unit" \
    "TermBox.accs_unit" \
    "TermBox.seenOwn_boxE" \
    "TermBox.inh_boxE" \
    "TermBox.pubCpl_boxE" \
    "TermBox.pubPair_boxE" \
    "TermBox.pubLive_boxE" \
    "TermBox.pubMem_boxE" \
    "TermBox.pubInv_boxE" \
    "TermBox.boxInv_boxE" \
    "TermBox.memInv_boxE" \
    "TermBox.heldEntry_boxE" \
    "TermBox.priv_boxE_iff" \
    "TermBox.memHeldP_boxE" \
    "TermBox.memHeldS_boxE" \
    "TermBox.promCrK_boxE"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${e2_termboxt_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBoxT.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSetTh.lean -------------------------------------------------------------
# (E2, R2z) `sysInvN_setC`: in-place replacement of one thread.
echo "building TermSetTh.lean ..."
if ! e2_termsetth_out=$(leanb TermSetTh 2>&1); then
  echo "$e2_termsetth_out"
  echo 'FAIL: TermSetTh.lean does not compile.'
  fail=1
fi
case "$e2_termsetth_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSetTh.lean theorem has a sorry"
    fail=1 ;;
esac
# (E2) TermSetTh: every #print axioms theorem, std axioms only.
for thm in \
    "TermSetTh.sysInvN_setC" \
    "TermSetTh.gOf_setC" \
    "TermSetTh.setC_get" \
    "TermSetTh.setC_self" \
    "TermSetTh.setC_other" \
    "TermSetTh.Same.st" \
    "TermSetTh.sc_get" \
    "TermSetTh.setC_promises" \
    "TermSetTh.allProms_setC" \
    "TermSetTh.pSumAt_setC" \
    "TermSetTh.promAtG_setC" \
    "TermSetTh.tminG_setC"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${e2_termsetth_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSetTh.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermBoxG.lean --------------------------------------------------------------
# (E2, R2z) `sysInvN_box`: the system invariant survives the box allocation.
echo "building TermBoxG.lean ..."
if ! e2_termboxg_out=$(leanb TermBoxG 2>&1); then
  echo "$e2_termboxg_out"
  echo 'FAIL: TermBoxG.lean does not compile.'
  fail=1
fi
case "$e2_termboxg_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBoxG.lean theorem has a sorry"
    fail=1 ;;
esac
# (E2) TermBoxG: every #print axioms theorem, std axioms only.
for thm in \
    "TermBox.sysInvN_box" \
    "TermBox.EgB_sto_cases" \
    "TermBox.EgB_pfr_cases" \
    "TermBox.thB_get" \
    "TermBox.allProms_thB" \
    "TermBox.pSumAt_thB" \
    "TermBox.gfresh_box" \
    "TermBox.tgtOK_box" \
    "TermBox.pubE_box_sto" \
    "TermBox.pubE_box_pfr" \
    "TermBox.vis_boxE" \
    "TermBox.predU_boxE_iff" \
    "TermBox.visU_boxE_iff" \
    "TermBox.promAt_boxE" \
    "TermBox.fpAt_boxE" \
    "TermBox.wordUnit_boxE_iff" \
    "TermBox.valOfR_boxE" \
    "TermBox.overT_boxE_iff" \
    "TermBox.winG_boxE_iff" \
    "TermBox.crItem_boxE" \
    "TermBox.crItemQ_boxE" \
    "TermBox.overCrE_boxE" \
    "TermBox.plantEdge_box" \
    "TermBox.tminOf_box" \
    "TermBox.tminG_box" \
    "TermBox.pfr_ne_none_box"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${e2_termboxg_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBoxG.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermBoxO.lean --------------------------------------------------------------
# (E2, R2z) `OwnLive`/`ObsAll` survive the box.
echo "building TermBoxO.lean ..."
if ! e2_termboxo_out=$(leanb TermBoxO 2>&1); then
  echo "$e2_termboxo_out"
  echo 'FAIL: TermBoxO.lean does not compile.'
  fail=1
fi
case "$e2_termboxo_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermBoxO.lean theorem has a sorry"
    fail=1 ;;
esac
# (E2) TermBoxO: every #print axioms theorem, std axioms only.
for thm in \
    "TermBox.ownLive_box" \
    "TermBox.obsAll_box"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${e2_termboxo_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBoxO.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnMidM0.lean ----------------------------------------------
# (2b) spawn mid on M0.
echo "building TermSpawnMidM0.lean ..."
if ! b2_termspawnmidm0_out=$(leanb TermSpawnMidM0 2>&1); then
  echo "$b2_termspawnmidm0_out"
  echo 'FAIL: TermSpawnMidM0.lean does not compile.'
  fail=1
fi
case "$b2_termspawnmidm0_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnMidM0.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnMidM0: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnMid.spawnT_n" \
    "TermSpawnMid.sysInvN_spawn_M0" \
    "TermSpawnMid.sysInvN_spawnStep" \
    "TermSpawnMid.sysInvN_spawnStepW" \
    "TermSpawnMid.spawnTy_of_sysInvN" \
    "TermSpawnMid.sysInvN_spawnArm" \
    "TermSpawnMid.StepsG.cap_eq" \
    "TermSpawnMid.gOf_spawnT"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnmidm0_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMidM0.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnFinal.lean --------------------------------------------------
# Spawn: startOK_spawnS, proved.
echo "building TermSpawnFinal.lean ..."
if ! g266_spfinal_out=$(leanb TermSpawnFinal 2>&1); then
  echo "$g266_spfinal_out"
  echo 'FAIL: TermSpawnFinal.lean does not compile.'
  fail=1
fi
case "$g266_spfinal_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnFinal.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermSpawn.startOK_spawnS_proved; do
  if ! echo "$g266_spfinal_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnFinal.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# (2b) theorems added to TermSpawnFinal.lean.
for thm in \
    "TermSpawn.spawnS_sysInvN_witness"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${g266_spfinal_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnFinal.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnStartO.lean ---------------------------------------------
# (2b) StartOKX at spawn.
echo "building TermSpawnStartO.lean ..."
if ! b2_termspawnstarto_out=$(leanb TermSpawnStartO 2>&1); then
  echo "$b2_termspawnstarto_out"
  echo 'FAIL: TermSpawnStartO.lean does not compile.'
  fail=1
fi
case "$b2_termspawnstarto_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnStartO.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) TermSpawnStartO: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawn.sysInvO_spawnS_proved"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnstarto_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnStartO.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- SpawnFinalX.lean -------------------------------------------------
# (2b) the X finals.
echo "building SpawnFinalX.lean ..."
if ! b2_spawnfinalx_out=$(leanb SpawnFinalX 2>&1); then
  echo "$b2_spawnfinalx_out"
  echo 'FAIL: SpawnFinalX.lean does not compile.'
  fail=1
fi
case "$b2_spawnfinalx_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a SpawnFinalX.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) SpawnFinalX: every #print axioms theorem, std axioms only.
for thm in \
    "StartOKX.toStartOK" \
    "startOKX_of_initOK" \
    "spArms_of" \
    "sysInv_runX" \
    "headline_of_sysInv" \
    "spLeafArms_bot" \
    "spawnArmX_bot" \
    "A9SpawnFinal.machine_tokens_mainX" \
    "A9SpawnFinal.token_unique_netX" \
    "A9SpawnFinal.token_unique_finalX" \
    "A9SpawnFinal.reachable_typedX" \
    "A9SpawnFinal.machine_tokens_mainX_init" \
    "A9SpawnFinal.stepArmX" \
    "A9SpawnFinal.mainX_bot" \
    "A9SpawnFinal.startOKX_spawnS" \
    "A9SpawnFinal.ObligationsFX.toF"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_spawnfinalx_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: SpawnFinalX.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- SpawnLeaf.lean ---------------------------------------------------
# (2b) spLeafArms_of_shape.
echo "building SpawnLeaf.lean ..."
if ! b2_spawnleaf_out=$(leanb SpawnLeaf 2>&1); then
  echo "$b2_spawnleaf_out"
  echo 'FAIL: SpawnLeaf.lean does not compile.'
  fail=1
fi
case "$b2_spawnleaf_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a SpawnLeaf.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) SpawnLeaf: every #print axioms theorem, std axioms only.
for thm in \
    "spLeafArms_of_shape" \
    "machine_tokens_mainX_shape" \
    "spawnShapeT_bot"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_spawnleaf_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: SpawnLeaf.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- SpawnLeafZ.lean --------------------------------------------------
# (2b) spLeafArms_spawn (SpawnShapeZ + SpawnVZ + TermSpawnScope).
echo "building SpawnLeafZ.lean ..."
if ! b2_spawnleafz_out=$(leanb SpawnLeafZ 2>&1); then
  echo "$b2_spawnleafz_out"
  echo 'FAIL: SpawnLeafZ.lean does not compile.'
  fail=1
fi
case "$b2_spawnleafz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a SpawnLeafZ.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) SpawnLeafZ: every #print axioms theorem, std axioms only.
for thm in \
    "spLeafArms_spawn"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_spawnleafz_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: SpawnLeafZ.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- SpawnArmZ.lean ---------------------------------------------------
# (2b) spawn arm leaf without SpawnTyHyp (guard root).
echo "building SpawnArmZ.lean ..."
if ! b2_spawnarmz_out=$(leanb SpawnArmZ 2>&1); then
  echo "$b2_spawnarmz_out"
  echo 'FAIL: SpawnArmZ.lean does not compile.'
  fail=1
fi
case "$b2_spawnarmz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a SpawnArmZ.lean theorem has a sorry"
    fail=1 ;;
esac
# (2b) SpawnArmZ: every #print axioms theorem, std axioms only.
for thm in \
    "spawnArmX_spawn" \
    "machine_tokens_main_spawn" \
    "token_unique_net_spawn" \
    "token_unique_final_spawn" \
    "reachable_typed_spawn" \
    "machine_tokens_main_spawn_init"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_spawnarmz_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: SpawnArmZ.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# (E2) TermSpawnMidM0: the new `spawnT_setC`.
for thm in \
    "spawnT_setC"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${b2_termspawnmidm0_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMidM0.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermExtMid.lean ------------------------------------------------------------
# (E2b) `sysInvN_extStep`: SysInvN across an extern step (emit/exitEv/current).
echo "building TermExtMid.lean ..."
if ! e2_termextmid_out=$(leanb TermExtMid 2>&1); then
  echo "$e2_termextmid_out"
  echo 'FAIL: TermExtMid.lean does not compile.'
  fail=1
fi
case "$e2_termextmid_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermExtMid.lean theorem has a sorry"
    fail=1 ;;
esac
# (E2) TermExtMid: every #print axioms theorem, std axioms only.
for thm in \
    "TermExtMid.ext_of_site" \
    "TermExtMid.vrr_unit" \
    "TermExtMid.vr_unit" \
    "TermExtMid.cutSto_box" \
    "TermExtMid.ownLive_setC" \
    "TermExtMid.obsAll_setC" \
    "TermExtMid.names_tid" \
    "TermExtMid.lay_tid" \
    "TermExtMid.vr_tid" \
    "TermExtMid.sysInvN_extSet" \
    "TermExtMid.pubWords_unit" \
    "TermExtMid.curCfg_some" \
    "TermExtMid.curCfg_none" \
    "TermExtMid.sysInvN_extStep" \
    "TermExtMid.sysInvN_extStepW"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${e2_termextmid_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermExtMid.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- ExtArmZ.lean ---------------------------------------------------------------
# (E2b) EM0 finals at `Spawn ∨ Ext`, leaf arms, runs.
echo "building ExtArmZ.lean ..."
if ! e2_extarmz_out=$(leanb ExtArmZ 2>&1); then
  echo "$e2_extarmz_out"
  echo 'FAIL: ExtArmZ.lean does not compile.'
  fail=1
fi
case "$e2_extarmz_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a ExtArmZ.lean theorem has a sorry"
    fail=1 ;;
esac
# (E2) ExtArmZ: every #print axioms theorem, std axioms only.
for thm in \
    "ExtArmZ.ext_shape" \
    "ExtArmZ.viewInv_ext" \
    "ExtArmZ.runScope_ext" \
    "ExtArmZ.promViewLt_ext" \
    "ExtArmZ.promPos_ext" \
    "ExtArmZ.promNodup_ext" \
    "ExtArmZ.spLeafArms_ext" \
    "ExtArmZ.SpLeafArms.or" \
    "ExtArmZ.spLeafArms_em0" \
    "ExtArmZ.Ext.cap_eq" \
    "ExtArmZ.stepsE_cap_eq" \
    "ExtArmZ.step_trace" \
    "ExtArmZ.spawn_trace" \
    "ExtArmZ.trace_mono" \
    "ExtArmZ.siteNoProm_ext" \
    "ExtArmZ.site_noPromE" \
    "ExtArmZ.spawnArmX_em0" \
    "ExtArmZ.machine_tokens_main_em0" \
    "ExtArmZ.token_unique_net_em0" \
    "ExtArmZ.token_unique_final_em0" \
    "ExtArmZ.reachable_typed_em0"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${e2_extarmz_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: ExtArmZ.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnMain.lean ---------------------------------------------------
# Spawn: The spawn lemma, at the frozen statement TermSpawnStmt minus
# `hbuf` (the buffer-walk hypothesis is dropped since WitBuf is dead; premise re-frozen by tools/premises).
echo "building TermSpawnMain.lean ..."
if ! g266_spmain_out=$(leanb TermSpawnMain 2>&1); then
  echo "$g266_spmain_out"
  echo 'FAIL: TermSpawnMain.lean does not compile.'
  fail=1
fi
case "$g266_spmain_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnMain.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in TermSpawn.startOK_spawnS; do
  if ! echo "$g266_spmain_out" | grep -qE "'$thm' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMain.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# ==== (A1 checker) A1 scope rule ProgScopeOKW + A1 checkW invariant + KidOK argOK/wrapOK + spawn R0 argOK + InitOK stoW ====
# --- BufSmoke.lean -----------------------------------------------------------
# Section 3.7 buffers: the checker's bounds and initialisation rules, each
# hazard rejected for its reason; on the machine, a published buffer never
# reads `undef`, an unpublished one passed plainly does (with a promise), and a
# Zeroable buffer passed plainly reads 0 or the value.
echo "building BufSmoke.lean ..."
if ! bs_out=$(leanb BufSmoke 2>&1); then
  echo "$bs_out"
  echo 'FAIL: BufSmoke.lean: a buffer guard failed.'
  fail=1
fi

# --- Typestate.lean ----------------------------------------------------------
# Ghost protocol words: a file handle whose double close, use after close and
# read while closed are each rejected for their reason, and whose ghost word
# leaves no message in memory when run.
echo "building Typestate.lean ..."
if ! ts_out=$(leanb Typestate 2>&1); then
  echo "$ts_out"
  echo 'FAIL: Typestate.lean: a ghost-protocol guard failed.'
  fail=1
fi

# --- RWLock.lean -------------------------------------------------------------
# Signed protocol transitions, `ifeq` learning in both branches, read shares,
# and the readers-writer lock as library code.
echo "building RWLock.lean ..."
if ! rw_out=$(leanb RWLock 2>&1); then
  echo "$rw_out"
  echo 'FAIL: RWLock.lean: a readers-writer guard failed.'
  fail=1
else
  # The one-promise explorer runs (2 min interpreted, seconds native).
  echo "running RWLockSlow.lean ..."
  if ! rws_out=$(leanr RWLockSlow.lean 2>&1); then
    echo "$rws_out"
    echo 'FAIL: RWLockSlow.lean: a one-promise readers-writer run failed.'
    fail=1
  fi
fi

# --- Caps.lean ---------------------------------------------------------------
# Capabilities: `openPub` for published memory, `borrow`/`endBorrow` lending a
# token or share as a second-class capability, one helper library called by
# own, lock-holding, share-holding and published-memory callers.
echo "building Caps.lean ..."
if ! caps_out=$(leanb Caps 2>&1); then
  echo "$caps_out"
  echo 'FAIL: Caps.lean: a capability guard failed.'
  fail=1
fi

# --- HashMap.lean, HashMapOwn.lean, HashMapLF.lean -----------------------------
# A polymorphic hash map written once over capabilities (own and readers-writer
# callers), a by-value own map for any value type, and a separate lock-free
# variant.  The *Slow files hold the long runs (minutes interpreted, seconds
# native); they used to be opt-in, behind WM_SLOW=1.
echo "building HashMap.lean ..."
if ! hm_out=$(leanb HashMap 2>&1); then
  echo "$hm_out"
  echo 'FAIL: HashMap.lean: a hash-map guard failed.'
  fail=1
else
  # Immutability, derived: a one-way lending protocol freezes a region.
  echo "building Freeze.lean ..."
  if ! fz_out=$(leanb Freeze 2>&1); then
    echo "$fz_out"
    echo 'FAIL: Freeze.lean: a frozen-region guard failed.'
    fail=1
  fi
  echo "building SubWord.lean ..."
  if ! sw_out=$(leanb SubWord 2>&1); then
    echo "$sw_out"
    echo 'FAIL: SubWord.lean: a fixed-width / packed-buffer guard failed.'
    fail=1
  fi
  echo "building HashMapOwn.lean ..."
  if ! ho_out=$(leanb HashMapOwn 2>&1); then
    echo "$ho_out"
    echo 'FAIL: HashMapOwn.lean: a by-value hash-map guard failed.'
    fail=1
  else
    # A SwissTable (flat_hash_map) by value: portable SWAR and x64 variants.
    echo "building FlatHashMap.lean ..."
    if ! fh_out=$(leanb FlatHashMap 2>&1); then
      echo "$fh_out"
      echo 'FAIL: FlatHashMap.lean: a SwissTable guard failed.'
      fail=1
    else
      echo "running FlatHashMapSlow.lean ..."
      if ! fhs_out=$(leanr FlatHashMapSlow.lean 2>&1); then
        echo "$fhs_out"
        echo 'FAIL: FlatHashMapSlow.lean: a long SwissTable run failed.'
        fail=1
      fi
    fi
  fi
  echo "building HashMapLF.lean ..."
  if ! lf_out=$(leanb HashMapLF 2>&1); then
    echo "$lf_out"
    echo 'FAIL: HashMapLF.lean: a lock-free hash-map guard failed.'
    fail=1
  else
    echo "running HashMapLFSlow.lean ..."
    if ! lfs_out=$(leanr HashMapLFSlow.lean 2>&1); then
      echo "$lfs_out"
      echo 'FAIL: HashMapLFSlow.lean: a concurrent lock-free run failed.'
      fail=1
    fi
  fi
fi

# --- Syntax.lean, SyntaxTest.lean ---------------------------------------------
# The concrete syntax: a parser and printer for CoreLang source text.  Its
# guards pin error positions and the refusal of index names across a load;
# SyntaxTest round-trips every library code block (print, parse, compare).
echo "building Syntax.lean ..."
if ! syn_out=$(leanb Syntax 2>&1); then
  echo "$syn_out"
  echo 'FAIL: Syntax.lean: a parser/printer guard failed.'
  fail=1
else
  echo "building SyntaxTest.lean ..."
  if ! synt_out=$(leanr SyntaxTest.lean 2>&1); then
    echo "$synt_out"
    echo 'FAIL: SyntaxTest.lean: a library code block does not survive print-then-parse.'
    fail=1
  fi
  # map / fold_left / iter / iter_i with closure-converted closures, written in
  # CoreLang source.
  echo "building ArrayLib.lean ..."
  if ! arr_out=$(leanb ArrayLib 2>&1); then
    echo "$arr_out"
    echo 'FAIL: ArrayLib.lean: an array-library guard (checker or machine) failed.'
    fail=1
  else
    # Probes: trait objects and interface upcasts over type
    # existentials, and the by-value-method refusal.
    for probe in probes/TraitObject.lean probes/Upcast.lean; do
      echo "checking $probe ..."
      if ! probe_out=$(leanr "$probe" 2>&1); then
        echo "$probe_out"
        echo "FAIL: $probe: a probe no longer checks or runs as stated."
        fail=1
      fi
    done
  fi
fi

# --- UnElab.lean, USyntax.lean, USyntaxTest.lean (UnElab M1) -----------------
# UnElab: the non-ANF surface language.  UnElab.lean is the AST and its elaboration to the core
# language (ANF with temporaries «%k»; elabT ∘ embed = id); USyntax.lean the .u/.i parser (a copy of Syntax's
# operation table with operands for atoms), the span table and the --print-elab printer;
# USyntaxTest.lean pins the parser: EM0 in UnElab parses, elaborates in the stated order and is
# accepted by checkProg, and the refused forms are refused with their messages.
echo "building UnElab.lean ..."
if ! unelab_out=$(leanb UnElab 2>&1); then
  echo "$unelab_out"
  echo 'FAIL: UnElab.lean: an elaboration guard failed.'
  fail=1
fi
case "$unelab_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a UnElab.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
for thm in "UnElab.setAts_opAts" "UnElab.elabArgs_ats" "UnElab.elabT_embed" "UnElab.elabDecl_embedDecl" \
    "UnElab.elabProg_embedProg"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${unelab_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: UnElab.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building USyntax.lean ..."
if ! usyn_out=$(leanb USyntax 2>&1); then
  echo "$usyn_out"
  echo 'FAIL: USyntax.lean does not compile.'
  fail=1
else
  echo "building USyntaxTest.lean ..."
  if ! usynt_out=$(leanb USyntaxTest 2>&1); then
    echo "$usynt_out"
    echo 'FAIL: USyntaxTest.lean: an UnElab parser guard failed.'
    fail=1
  fi
fi

# --- UCheck.lean, UHygiene.lean, UDiag.lean (UnElab M2) -------------------------
# UCheck: UnElab's typing checkU and T1 (checkU p cx k e = check p cx (elabT k e); checkProgU U = checkProg
# (elabProg U)), and rule 4's `ret f(args)` lint.  UHygiene: the elaboration's temporaries are fresh (strictly
# increasing «%k» along every path; no user name is reserved).  UDiag: diagnostics (file:line:col: in f: msg,
# gutter, ^~~~), a checker error placed by Scope.branches and the span table.
echo "building UCheck.lean ..."
if ! ucheck_out=$(leanb UCheck 2>&1); then
  echo "$ucheck_out"
  echo 'FAIL: UCheck.lean: a typing theorem or guard failed.'
  fail=1
fi
case "$ucheck_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a UCheck.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
for thm in "UCheck.check_lets" "UCheck.checkArg_fold" "UCheck.checkArgs_fold" "UCheck.checkU_elab" "UCheck.checkDecl_with" "UCheck.checkDeclU_elab" "UCheck.checkProgU_elab" "UCheck.checkProgU_ok"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${ucheck_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: UCheck.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building UHygiene.lean ..."
if ! uhyg_out=$(leanb UHygiene 2>&1); then
  echo "$uhyg_out"
  echo 'FAIL: UHygiene.lean: a hygiene theorem failed.'
  fail=1
fi
case "$uhyg_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a UHygiene.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
for thm in "UHygiene.reserved_tmp" "UHygiene.fresh_mono" "UHygiene.elabArg_fresh" "UHygiene.destr_fresh" "UHygiene.elabT_fresh" "UHygiene.elabProg_fresh"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${uhyg_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: UHygiene.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building UDiag.lean ..."
if ! udiag_out=$(leanb UDiag 2>&1); then
  echo "$udiag_out"
  echo 'FAIL: UDiag.lean: does not compile.'
  fail=1
fi
case "$udiag_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a UDiag.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac

# --- Doc.lean -------------------------------------------------------------------
# Doc.lean: the helpers for checked CoreLang documents, with their own guards.
# Only Doc.lean itself is built here.
echo "building Doc.lean ..."
if ! doc_out=$(leanb Doc 2>&1); then
  echo "$doc_out"
  echo 'FAIL: Doc.lean: a documentation helper guard failed.'
  fail=1
else
  echo "building DocU.lean ..."
  if ! docu_out=$(leanb DocU 2>&1); then
    echo "$docu_out"
    echo 'FAIL: DocU.lean (cldoc support for syntax=u) does not compile.'
    fail=1
  fi
  echo "docs: not part of this distribution"
fi

# Deliberately no count here: this grep asserts *0 failing*, and item 28 is
# what pins the size of the suite -- against the herd7 row counts and every
# number quoted in the documents.  A literal here would be a number written
# down in the one file whose whole job is to catch numbers written down.
if ! echo "$out" | grep -qE '[0-9]+ tests, 0 failing'; then
  echo "FAIL: litmus suite does not pass under the promise machine"
  fail=1
fi

if echo "$out" | grep -q 'state set differs'; then
  echo "FAIL: a test reaches a different set of states than WeakMem.lean"
  fail=1
fi

if echo "$out" | grep -q 'DELETE THIS RULE'; then
  echo "FAIL: an ablation broke nothing -- that rule is unjustified"
  fail=1
fi

if echo "$out" | grep -q 'is WRONG'; then
  echo "FAIL: toggling a permission changed the reachable states -- the"
  echo "      equivalence/generality argument for it in Promises.lean §2 is wrong"
  fail=1
fi

if echo "$out" | grep -q 'promise candidates are incomplete'; then
  echo "FAIL: a test has a .reg store, so promise candidates are incomplete"
  fail=1
fi

if ! echo "$out" | grep -q 'stuck=false'; then
  echo "FAIL: the read-own-write demo got stuck, so the triple may be vacuous"
  fail=1
fi

# The privacy theorems are all of the form "Remote cannot reach this".  An
# environment that does nothing satisfies every one of them, so both halves of
# the differential are required: unreachable stays untouched, AND the same
# address under the same oracle *is* touched once a pointer to it is published.
if ! echo "$out" | grep -q 'published=false: .*wrote-to-secret=false'; then
  echo "FAIL: Remote reached an address with no pointer to it"
  fail=1
fi

if ! echo "$out" | grep -q 'published=true: .*wrote-to-secret=true'; then
  echo "FAIL: Remote did not reach a published address, so renv is inert and"
  echo "      the privacy theorems in Promises.lean §7 are vacuous"
  fail=1
fi

# Same discipline for §8.  `published_read_is_initialised` says the reader
# cannot see a stale value, and a model in which the reader can never read
# anything at all proves it too.  The unfenced row is the control: it must
# actually exhibit the bad read.  It is also the executable form of the claim
# that the fence is load-bearing, which the proof can only make negatively.
if ! echo "$out" | grep -q 'fenced=false: .*saw-undef=true'; then
  echo "FAIL: the unfenced publication did not expose uninitialised memory, so"
  echo "      the fenced theorem in Promises.lean §8 has nothing to rule out"
  fail=1
fi

if ! echo "$out" | grep -q 'fenced=true: .*saw-undef=false'; then
  echo "FAIL: Remote read uninitialised memory through a properly published"
  echo "      pointer -- the address dependency is not carrying the ordering"
  fail=1
fi

# §9 is a rely condition, which makes vacuity even more dangerous than usual:
# a guard that accidentally disabled the whole environment would satisfy
# `owned_load_reads_own_write` trivially and look like a success.  The unowned
# row must show Remote genuinely clobbering the location under the same oracle.
if ! echo "$out" | grep -q 'owned=false: read=.*num 0'; then
  echo "FAIL: the environment did not overwrite an unowned location, so the"
  echo "      ownership theorem in Promises.lean §9 rules nothing out"
  fail=1
fi

if ! echo "$out" | grep -q 'owned=true: read=.*num 7'; then
  echo "FAIL: the environment wrote to a disowned allocation -- the rdisowned"
  echo "      guard in rstoreStep is not being applied"
  fail=1
fi

# §9.1 composes §8 and §9 over one program.  The failure mode to guard against
# is different from either: the *second* read could be pinned by coherence
# alone, in which case ownership is doing no work and the theorem is a
# restatement of §8.  Dropping only `assumeExclusive` must break it.
if ! echo "$out" | grep -q 'owned=false: second-read=.*num 0'; then
  echo "FAIL: the transferred object survived an environment that was free to"
  echo "      write it, so §9.1 is not about ownership at all"
  fail=1
fi

if ! echo "$out" | grep -q 'owned=true: second-read=.*num 7'; then
  echo "FAIL: the receiver's second read did not return the published value --"
  echo "      publication and ownership no longer compose (Promises.lean §9.1)"
  fail=1
fi

# §10 changed `mload` so that an empty candidate list is no longer a fault.
# That is D1, and it is exactly the kind of change that is easy to over- or
# under-apply: make every load stuck and the loop proof is vacuous; make no
# load stuck and the model no longer distinguishes allocated from not.
if ! echo "$out" | grep -q 'in-bounds=true: read=.*undef, stuck=false'; then
  echo "FAIL: reading an allocated-but-unwritten cell did not yield undef, or"
  echo "      got stuck -- D1 is not implemented (Promises.lean §10)"
  fail=1
fi

if ! echo "$out" | grep -q 'in-bounds=false: read=.*stuck=true'; then
  echo "FAIL: a load outside every allocation was not stuck, so the allocated"
  echo "      check is not being consulted and undef has swallowed a real error"
  fail=1
fi

# The store side of the same check.  Two ways to get this wrong, and the rows
# below pin both: drop the check and nothing is ever flagged; make the store
# suppress the write as well as flag it and `writes` goes to 0, which would be
# a second shape for the store rule that nothing in the model wants.
if ! echo "$out" | grep -q 'in-bounds=true:  writes=1, stuck=false'; then
  echo "FAIL: an in-bounds store was refused or flagged (Promises.lean §10)"
  fail=1
fi

if ! echo "$out" | grep -q 'in-bounds=false: writes=1, stuck=true'; then
  echo "FAIL: an out-of-bounds store was not flagged, or was suppressed rather"
  echo "      than recorded -- mstore's allocated check has changed shape"
  fail=1
fi

# This is the composition case, and the only one that is not obvious.  The load
# consults `allocated` only when nothing is readable, so reading back a cell a
# bad store created takes the unchecked branch.  It stays stuck only because
# `stuck` is sticky.  If this row ever reports clean, the bounds check can be
# defeated by a two-instruction program.
if ! echo "$out" | grep -q 'store-then-load out of bounds: .*stuck=true'; then
  echo "FAIL: storing out of bounds and reading the cell back reported clean."
  echo "      Either stuck stopped being sticky, or mstore stopped checking."
  fail=1
fi

# The copy loop's privacy claim has the same vacuity risk as §7's, with more
# moving parts: a loop that never ran, or an environment that never fired
# inside the body, would both report an untouched buffer.  The published row
# is the control -- same oracle, same adversary, same copy.
if ! echo "$out" | grep -q 'fresh=false: .*writes-to-dst=3'; then
  echo "FAIL: Remote did not clobber a published copy destination, so renv is"
  echo "      inert inside the loop body and §10's theorem rules nothing out"
  fail=1
fi

if ! echo "$out" | grep -q 'fresh=true: .*writes-to-dst=2'; then
  echo "FAIL: something wrote to a freshly allocated buffer that nothing could"
  echo "      reach -- freshness is not being enforced (Promises.lean §10)"
  fail=1
fi

# copy_is_exact's clean row.  If the buffer stops being a word-for-word
# duplicate of the source, the strong theorem is still true but no longer says
# anything anyone wants -- a copy that wrote nothing satisfies it too.  This is
# the non-vacuity guard for the *values*, where fresh=true above guards the
# count.
if ! echo "$out" | grep -q 'clobber=false: *dst=\[5, 6\], src\[0\] history=\[5\]'; then
  echo "FAIL: an uninterfered copy did not duplicate its source, so copy_is_exact"
  echo "      is vacuous on the one run where its antecedent holds"
  fail=1
fi

# The clobber row, and both halves of it matter.  The buffer must still be
# [5, 6] -- that is copy_copies_something holding under interference, and it is
# also the proof that the two rows differ only in the environment.  The source
# history must have two entries -- that is Describes failing, which is the
# reason copy_is_exact needs an antecedent at all.  If Remote's write stops
# landing, the row silently becomes a duplicate of the first.
if ! echo "$out" | grep -q 'clobber=true: *dst=\[5, 6\], src\[0\] history=\[5, 0\]'; then
  echo "FAIL: clobbering the source mid-copy did not produce a stale buffer and"
  echo "      a two-valued source cell, so the frozen-source hypothesis in"
  echo "      copy_is_exact is not being exercised (Promises.lean §10)"
  fail=1
fi

# §11 is atomicity, and it is a *restriction*: the CAS must refuse a read a
# plain load is allowed to take.  Both rows matter.  If the plain row stops
# acquiring, the load rule has been tightened and the control no longer shows
# anything; if the atomic row starts acquiring, rmwAdjacent is not being
# consulted and mcas is just a load followed by a store.
if ! echo "$out" | grep -q 'atomic=false: read=.*num 0, acquired=true'; then
  echo "FAIL: load-check-store did not take a held lock, so the atomicity"
  echo "      control is vacuous (Promises.lean §11)"
  fail=1
fi

if ! echo "$out" | grep -q 'atomic=true: read=.*num 1, acquired=false'; then
  echo "FAIL: a CAS read a stale value or acquired a held lock -- rmwAdjacent"
  echo "      is not restricting the read (Promises.lean §11)"
  fail=1
fi

# §11.1's exclusion theorem is satisfied by a remote CAS that never succeeds,
# so the free-lock row is the control and it is the one that matters most.
if ! echo "$out" | grep -q 'local-acquires=false: local=false, remote1=true, remote2=false'; then
  echo "FAIL: Remote either could not take a free lock, or took it twice --"
  echo "      lock_is_exclusive is vacuous (Promises.lean §11.1)"
  fail=1
fi

if ! echo "$out" | grep -q 'local-acquires=true: local=true, remote1=false, remote2=false'; then
  echo "FAIL: Remote acquired a lock the local thread was holding, so exclusion"
  echo "      is not being enforced (Promises.lean §11.1)"
  fail=1
fi

# §11.2 turns §9's assumption into a theorem, so the vacuity risk is §9's in a
# new form: an environment that cannot write for some *other* reason would
# satisfy `lock_protects_data` without the lock doing anything.  The control is
# a one-instruction change -- local reads the lock instead of winning it -- and
# it must be enough to let Remote in.
if ! echo "$out" | grep -q 'local-locks=false: acquired=true, read=.*num 0'; then
  echo "FAIL: Remote did not clobber the data when the local thread had not"
  echo "      taken the lock, so lock_protects_data rules nothing out"
  echo "      (Promises.lean §11.2)"
  fail=1
fi

if ! echo "$out" | grep -q 'local-locks=true: acquired=true, read=.*num 7'; then
  echo "FAIL: a disciplined environment wrote data protected by a lock the"
  echo "      local thread was holding -- the protection derived in"
  echo "      Promises.lean §11.2 is not being enforced"
  fail=1
fi

# §11.3 has no exclusion to appeal to, so the vacuity risk is the opposite of
# §11.2's: a reader that could never see the new data would validate cleanly
# for the wrong reason.  Both rows therefore matter -- the unfenced reader must
# actually tear, and the fenced one must actually be stopped.
if ! echo "$out" | grep -q 'reader-fence=false: .*torn-accepted=true'; then
  echo "FAIL: an unfenced seqlock reader did not accept a torn snapshot, so"
  echo "      the reader-side dmb ishld in Promises.lean §11.3 is not what is"
  echo "      doing the work"
  fail=1
fi

# The writer-side half.  This one was a recorded gap until `rloadStep` stopped
# folding the raw read timestamp into Remote's `vRd`: array order was supplying
# the ordering the fence is supposed to buy.  If it ever passes again with the
# fence dropped, that shortcut has come back.
if ! echo "$out" | grep -q 'writer-fence=false, reader-fence=true: .*torn-accepted=true'; then
  echo "FAIL: dropping the writer's dmb ishst did not produce a torn snapshot."
  echo "      Remote is getting its ordering from somewhere other than the"
  echo "      data word's message view -- most likely a read timestamp has"
  echo "      crept back into rloadStep's vRd (Promises.lean §11.3)"
  fail=1
fi

if ! echo "$out" | grep -q 'writer-fence=true, reader-fence=true: .*torn-accepted=false'; then
  echo "FAIL: a fenced seqlock reader accepted a torn snapshot -- validation"
  echo "      is not detecting the open transaction (Promises.lean §11.3)"
  fail=1
fi

# The promised-writer rows, and all three assertions are needed because the
# finding is that the first two are *identical*.  If the torn row ever stops
# tearing, the promise is not reaching the reader; if the fenced row stops
# being torn, the demo no longer shows that the fence is invisible to a
# reader; and if the fenced row is ever a behaviour, rule 3 is not being
# applied and the front end is reporting a run that the machine of §2 would
# have thrown away.
if ! echo "$out" | grep -q 'writer-fence=false, data-promised: .*torn=true, outstanding=\[\], behaviour=true'; then
  echo "FAIL: the unfenced writer's promised data store did not produce a torn"
  echo "      snapshot in a discharged run, so §11.3's store->store"
  echo "      counterexample is not being exhibited at all"
  fail=1
fi

if ! echo "$out" | grep -q 'writer-fence=true, data-promised: .*torn=true'; then
  echo "FAIL: with the writer's dmb ishst the reader stopped tearing.  That"
  echo "      makes the demo say the fence is visible to a reader, which is"
  echo "      the opposite of the finding: the promised message is still in"
  echo "      memory and still readable (Promises.lean §11.3)"
  fail=1
fi

if ! echo "$out" | grep -q 'writer-fence=true, data-promised: .*behaviour=false'; then
  echo "FAIL: a run that left a promise outstanding was reported as a"
  echo "      behaviour.  Rule 3 of §2.3 is not being applied in the front"
  echo "      end, and every promising demo is reporting memory states rather"
  echo "      than behaviours (Machine.exhibits, Promises.lean §5)"
  fail=1
fi

# §11.4, and it needs both rows or it proves nothing.  The first is the
# counterexample the primitive exists to rule out: two single-word CASes, each
# atomic, reading a pair that was never in memory.  Without it the second row
# could be passing because the scenario is too weak to tear in the first place.
if ! echo "$out" | grep -q 'atomic=false: .*torn-read=true'; then
  echo "FAIL: two independent single-word CASes did not tear, so the pair"
  echo "      control proves nothing -- the scenario no longer offers a stale"
  echo "      read at the first word (Promises.lean §11.4)"
  fail=1
fi

# The claim.  Note this asserts over *every* snapshot casPairOutcomes admits,
# not the one an oracle picked, so it cannot pass by luck.
if ! echo "$out" | grep -q 'atomic=true : .*torn-available=false'; then
  echo "FAIL: the pair compare-and-swap admits a torn snapshot.  pairStraddles"
  echo "      is not filtering, and the model is now weaker than"
  echo "      cats/aarch64-pair.cat's C-read-tear probe (Promises.lean §11.4)"
  fail=1
fi

# §14, and like §11.4 it needs both rows.  The protocol's knowledge clause is
# supposed to be exactly what the writer's store-store fence buys, so a run
# without the fence must *fail* it.  A protocol that held in both cases would
# be recording something other than the ordering, and would still satisfy the
# positive assertion below.
if ! echo "$out" | grep -q 'fenced=false: .*knows-holds=false'; then
  echo "FAIL: the publication protocol's knowledge clause held without the"
  echo "      writer's dmb ishst, so it is not measuring the fence and the"
  echo "      positive row proves nothing (Promises.lean §14)"
  fail=1
fi

if ! echo "$out" | grep -q 'fenced=true: .*knows-holds=true'; then
  echo "FAIL: the publication protocol's knowledge clause failed even with the"
  echo "      writer's dmb ishst -- Governs is not establishable, so every §14"
  echo "      theorem is vacuous (Promises.lean §14)"
  fail=1
fi

# §14 under interference, and again both rows.  `governs_of_env_disowned` says
# ownership is what keeps the protocol alive across a Remote step; the negative
# row is what stops that from being a claim about an environment that was never
# going to do anything.  The oracle is pointed at the root and told to write a
# pointer rather than null -- null satisfies `wf`, so a run that took it would
# pass the positive assertion while testing nothing.
if ! echo "$out" | grep -q 'owned=false: .*governs=false'; then
  echo "FAIL: the environment failed to break an unowned protocol location, so"
  echo "      the owned row below is not measuring ownership -- either the"
  echo "      oracle is no longer reaching the damaging step or rstoreStep is"
  echo "      dropping writes it should make (Promises.lean §14)"
  fail=1
fi

if ! echo "$out" | grep -q 'owned=true: .*governs=true'; then
  echo "FAIL: a protocol at a disowned location did not survive an environment"
  echo "      step, contradicting governs_of_env_disowned -- the theorem and"
  echo "      the executable model have come apart (Promises.lean §14)"
  fail=1
fi

# §14's composition.  Two rows again, and this pair is stricter than the others
# because it asserts the *hypothesis* as well as the conclusion: they have to
# fail together, or the control does not identify which hypothesis is doing the
# work.  `settled` is the Bool image of GovernsFrom (immProto v) d t0.
if ! echo "$out" | grep -q 'immutable=true: settled=true, deref=WeakMem.Val.num 7'; then
  echo "FAIL: the composed protocols did not pin the dereferenced value with"
  echo "      the descriptor left alone -- either pub_deref_pins' hypotheses"
  echo "      are unsatisfiable or the model stopped agreeing with it"
  echo "      (Promises.lean §14)"
  fail=1
fi

if ! echo "$out" | grep -q 'immutable=false: settled=false, deref=WeakMem.Val.num 99'; then
  echo "FAIL: overwriting the descriptor after publication did not break both"
  echo "      the settled hypothesis and the pin -- if only one of them moved,"
  echo "      the control no longer shows that this hypothesis is the one"
  echo "      responsible for the pin (Promises.lean §14)"
  fail=1
fi

# §15.  The monotonicity lemmas are only interesting if the two architectures
# actually compute different bounds, and the refinement is only necessary if a
# fence moves the state.  Both are asserted with their numbers, not just their
# booleans, so that a change which makes them agree shows up as a diff rather
# than as a silently weaker check.
if ! echo "$out" | grep -q 'readBound arm=1, tso=3, strict=true'; then
  echo "FAIL: arm and tso no longer disagree on the read bound at a state that"
  echo "      has already read -- if this is intended, §15's monotonicity"
  echo "      lemmas have become identities and prove nothing"
  echo "      (Promises.lean §15)"
  fail=1
fi

if ! echo "$out" | grep -q 'fence vPreBase before=1, after=3, moved=true'; then
  echo "FAIL: a dmb sy no longer moves vPreBase, so identity on states would"
  echo "      do and ThreadLe_of_fence_right is absorbing nothing -- either"
  echo "      stepFence changed or the witness state stopped being a witness"
  echo "      (Promises.lean §15)"
  fail=1
fi

# §4.1 is what licenses reading every `arm` result as a claim about x86.  Two
# ways it can rot: an outcome escapes (the containment is false), or the two
# rule sets stop differing anywhere (the containment is true but empty).  The
# report prints both counts on one line, so assert on both.
#
# No literal count here, for the same reason as the suite assertion above: item
# 28 is what pins the size, and it cross-checks this very line against the
# `N tests, 0 failing` line and against `litmus/`.  A number written down here
# would be a number written down in the one file whose job is to catch them.
if ! echo "$out" | grep -qE '[0-9]+ shapes, 0 escaping,'; then
  echo "FAIL: some outcome is reachable under tso but not under arm, so an"
  echo "      arm proof is no longer a claim about x86 (Promises.lean §4.1)"
  fail=1
fi

if echo "$out" | grep -q 'this check is vacuous'; then
  echo "FAIL: arm and tso agree on every shape tested, so tso ⊆ arm holds for"
  echo "      no interesting reason (Promises.lean §4.1)"
  fail=1
fi

# §12, the 2x2.  Row 1 is the claim, row 2 is the control for the writer's
# fence, and rows 3 and 4 are the two halves of "the reader's barrier is not
# the mechanism".  All four are needed: rows 1 and 2 alone would be satisfied
# by a model in which the reader's fence was doing the work.
if ! echo "$out" | grep -q 'writer-fence=true, reader-fence=false: depth=4, .*saw-undef=false'; then
  echo "FAIL: a fenceless reader did not walk the published chain to its"
  echo "      payload, so the address dependency has stopped carrying the"
  echo "      view along the chase (Promises.lean §12)"
  fail=1
fi

if ! echo "$out" | grep -q 'writer-fence=false, reader-fence=false: depth=2, .*saw-undef=true'; then
  echo "FAIL: the traversal succeeded without the writer's dmb ishst, so the"
  echo "      §12 control is vacuous and the fence is not load-bearing"
  fail=1
fi

if ! echo "$out" | grep -q 'writer-fence=false, reader-fence=true: depth=2, .*saw-undef=true'; then
  echo "FAIL: a reader-side dmb ishld rescued an unfenced writer.  Remote is"
  echo "      absorbing ordering the writer never published -- check that"
  echo "      rloadStep's vRd still takes only the message view (§12, §11.3)"
  fail=1
fi

if ! echo "$out" | grep -q 'writer-fence=true, reader-fence=true: depth=4, .*saw-undef=false'; then
  echo "FAIL: adding a reader barrier changed the fenced traversal, so the"
  echo "      dependency was not already supplying the ordering and the"
  echo "      'cheaper than dmb' claim is wrong (Promises.lean §12)"
  fail=1
fi

# §13, the growable array.  Five assertions, and they are five different
# failures.  The first says the data survives reallocation at all; the next two
# are the capacity/length split, which is the only thing this section adds to
# the model's expressiveness and which nothing else in the report exhibits; the
# last two are the non-vacuity control -- if a no-grow push stops getting
# stuck, then `vpushes_never_stick` is a statement about a lenient model rather
# than about vpush's growth test.
if ! echo "$out" | grep -q 'vget 2: len=3, cap=4, read=3, stuck=false'; then
  echo "FAIL: a value did not survive the vector's reallocations, so the"
  echo "      growable array loses data and §13's client is broken"
  fail=1
fi

if ! echo "$out" | grep -q 'vget 3: len=3, cap=4, read=undef, stuck=false'; then
  echo "FAIL: reading inside the capacity but past the length was not a clean"
  echo "      undef, so the capacity/length split is not expressible and"
  echo "      stage 2's implicit-undef allocation has regressed (§13, §6.6)"
  fail=1
fi

if ! echo "$out" | grep -q 'vget 4: len=3, cap=4, read=undef, stuck=true'; then
  echo "FAIL: reading past the capacity did not get stuck, so the load's"
  echo "      bounds check is inert and LoadPost.clean guarantees nothing"
  echo "      (Promises.lean §13)"
  fail=1
fi

if ! echo "$out" | grep -q 'no-grow, 2 pushes into cap 2: .*stuck=false'; then
  echo "FAIL: pushes within capacity got stuck even without growing, so the"
  echo "      §13 control differs from vpush in more than the growth test"
  fail=1
fi

if ! echo "$out" | grep -q 'no-grow, 3 pushes into cap 2: .*stuck=true'; then
  echo "FAIL: overrunning a buffer did not get stuck, so the store's bounds"
  echo "      check does not bite and vpushes_never_stick is vacuous (§13)"
  fail=1
fi

# §16.  Read the compiler, not the report.  The first assertion is that the
# theorem exists and was checked; the second is that it does not rest on
# `sorryAx`, which is the only way a Lean proof can be vacuous without the
# build failing.  Both read `build_out` rather than `$out`.
if ! echo "$build_out" | grep -q "tso_outcomes_subset_arm' depends on axioms"; then
  echo "FAIL: §16's axiom report is missing, so either the simulation theorem"
  echo "      was renamed or the '#print axioms' line at the end of §16 was"
  echo "      dropped -- the containment proof is no longer being checked"
  fail=1
fi

if echo "$build_out" | grep -q 'sorryAx'; then
  echo "FAIL: a declaration in Promises.lean depends on sorryAx -- something"
  echo "      in the TSO-subset-of-ARM simulation (§16) is admitted rather"
  echo "      than proved, and the theorem states nothing"
  fail=1
fi

# §17, the synchronised cell (`Sync`).  The first two assertions are a pair and must
# be read together: the same tuple from both means the derived construction
# buys a non-participating observer nothing.
if ! echo "$out" | grep -q 'casPair+cas  : observer read (1,1,7)'; then
  echo "FAIL: casPair-then-cas no longer exposes its intermediate, so either"
  echo "      three-word atomicity has become free -- which would make the"
  echo "      ladder's third row wrong -- or the observer stopped observing"
  echo "      (Promises.lean §17)"
  fail=1
fi

if ! echo "$out" | grep -q 'lock, unaware: observer read (1,1,7)'; then
  echo "FAIL: the lock-based update no longer exposes the same intermediate"
  echo "      as the naive one to an observer that ignores the lock.  §17's"
  echo "      headline is that these two rows agree; if they do not, either"
  echo "      the lock now excludes non-participants (it cannot) or the two"
  echo "      scenarios have drifted apart (Promises.lean §17)"
  fail=1
fi

if ! echo "$out" | grep -q 'lock, aware  : observer blocked'; then
  echo "FAIL: an observer running the lock protocol was not excluded, so the"
  echo "      lock is inert and the derived Sync cell protects nothing -- the"
  echo "      non-vacuity control for the two rows above (Promises.lean §17)"
  fail=1
fi

if ! echo "$out" | grep -q 'reader-locks=false: acquired=true, read=(7,0,0)'; then
  echo "FAIL: an unlocked three-word read no longer tears, so the reader-side"
  echo "      control is vacuous and 'holding the lock is what makes it a"
  echo "      snapshot' is untested (Promises.lean §17)"
  fail=1
fi

if ! echo "$out" | grep -q 'reader-locks=true: acquired=true, read=(7,7,7)'; then
  echo "FAIL: a reader holding the lock did not get a consistent snapshot,"
  echo "      which is the whole claim of the derived Sync cell (§17) and is"
  echo "      the executable shadow of sync_write_is_atomic"
  fail=1
fi

# 24. Pair single-copy atomicity holds against an observer that is not a pair.
#     These two must be asserted *together*: `CASPOrderedRead` passed for the
#     wrong reason before `pairTop` existed, and only the word-swapped mirror
#     detected it.  Dropping either assertion restores the blind spot.
if ! echo "$out" | grep -q 'ok    | \[arm\] CASPOrderedRead$'; then
  echo "FAIL: an ordered observer can see a pair RMW torn (second word then"
  echo "      first).  Either pairTop is gone from the read view or the test"
  echo "      is (WeakMem.lean pair suite)"
  fail=1
fi

if ! echo "$out" | grep -q 'ok    | \[arm\] CASPOrderedReadSwapped$'; then
  echo "FAIL: an ordered observer can see a pair RMW torn (first word then"
  echo "      second).  This is the direction the model got wrong before"
  echo "      pairTop, and the one its mirror cannot detect -- if this fails"
  echo "      while the test above passes, the model is asymmetric in word"
  echo "      order again (WeakMem.lean pair suite)"
  fail=1
fi

# 25. §17's two sides are theorems.  Same reasoning as item 22, and the same
#     mechanism: read `build_out`, not `$out`.  The global `sorryAx` assertion
#     above already covers the second half for every `#print axioms` line in
#     the file, so what is added here is the *presence* check -- deleting
#     either theorem, or renaming it, must not pass silently.
if ! echo "$build_out" | grep -q "sync_read_is_a_snapshot' depends on axioms"; then
  echo "FAIL: §17's reader-side axiom report is missing, so either"
  echo "      sync_read_is_a_snapshot was renamed or its '#print axioms'"
  echo "      line was dropped.  The reader's snapshot would then be exhibited"
  echo "      by the two rows above and not proved anywhere"
  fail=1
fi
if ! echo "$build_out" | grep -q "sync_write_is_atomic' depends on axioms"; then
  echo "FAIL: §17's writer-side axiom report is missing, so either"
  echo "      sync_write_is_atomic was renamed or its '#print axioms'"
  echo "      line was dropped.  That theorem is what establishes SyncFrozen"
  echo "      and SyncReleased, which are the reader's hypotheses: without it"
  echo "      sync_snapshot_after_write composes with nothing"
  fail=1
fi


# 27. §11.3's fenced promising writer is a theorem.  Item 26 already asserts
#     the demo row; this asserts that the general claim behind it still
#     exists.  The two are not redundant: the row is one oracle and two
#     addresses, and it would keep printing `behaviour=false` even if the
#     theorem were deleted.
if ! echo "$build_out" | grep -q "fenced_writer_cannot_discharge' depends on axioms"; then
  echo "FAIL: §11.3's writer-side axiom report is missing, so either"
  echo "      fenced_writer_cannot_discharge was renamed or its '#print"
  echo "      axioms' line was dropped.  The claim that a fenced promising"
  echo "      writer has no run would then rest on a single printed row"
  fail=1
fi

# 31. Certification.  §4.2 emits its own FAIL lines -- one per claim, so the
#     message names which of the four broke -- and this is the grep that turns
#     them into an exit status.  The section must also still be there: a report
#     that silently stopped running it would pass every grep below.
if ! echo "$out" | grep -q 'stuck configurations: on '; then
  echo "FAIL: §4.2's certification summary is missing, so the progress"
  echo "      counterexample and its repair are unmeasured"
  fail=1
fi

if echo "$out" | grep -q 'certification rejects nothing'; then
  echo "FAIL: certification prunes no step anywhere, so \"it changes nothing\""
  echo "      is true for the boring reason and §2.4 is decoration"
  fail=1
fi

if echo "$out" | grep -q 'no stuck configuration anywhere'; then
  echo "FAIL: no shape reaches a stuck configuration without certification,"
  echo "      so the progress counterexample §2.4 exists to remove is not"
  echo "      something the suite can see"
  fail=1
fi

if echo "$out" | grep -q 'stuck under certification'; then
  echo "FAIL: a stuck configuration survives certification.  Thread-local"
  echo "      certification is not enough here, which refutes the monotonicity"
  echo "      argument and the certification bridge theorem"
  fail=1
fi



# ---------------------------------------------------------------------------
# 28-29.  The documents, checked against the artifact rather than against
#         somebody's memory of it.  Markdown cannot compute, so the numbers
#         are computed here and the documents are annotated with invisible
#         markers saying which number is which.
# ---------------------------------------------------------------------------

# Computed, never quoted.
n_suite=$(printf '%s\n' "$out" | sed -n 's/^\([0-9][0-9]*\) tests, [0-9][0-9]* failing$/\1/p')
n_arm=$(printf '%s\n' "$out" | awk '/^ok    \| \[arm\]/{c++} END{print c+0}')
n_tso=$(printf '%s\n' "$out" | awk '/^ok    \| \[tso\]/{c++} END{print c+0}')
n_herd_arm=$(ls litmus/aarch64/*.litmus 2>/dev/null | wc -l | tr -d ' ')
n_herd_x86=$(ls litmus/x86_64/*.litmus 2>/dev/null | wc -l | tr -d ' ')
n_herd_pair=$(ls litmus/aarch64-pair/*.litmus 2>/dev/null | wc -l | tr -d ' ')
n_herd_wide=$(ls litmus/aarch64-wide/*.litmus 2>/dev/null | wc -l | tr -d ' ')
# The suite's total reachable final states, summed rather than printed as a
# line.  Computed here because it is quoted: it was written down as 199 when the
# suite was 46 tests, and stayed 199 after it became 52 -- item 28 could not see
# it because nothing computed the number to compare against.
n_states=$(printf '%s\n' "$out" |
  awk '{for (i = 1; i < NF; i++) if ($i == "states:") s += $(i + 1)} END {print s + 0}')
# §4.2's summary line: "prunes on N shapes: P/T offered steps rejected".
n_certprune=$(printf '%s\n' "$out" |
  sed -n 's/^ *prunes on \([0-9][0-9]*\) shapes: .*/\1/p')
# §4.1's own summary line: "N shapes, 0 escaping, K where arm is strictly weaker".
n_shapes=$(printf '%s\n' "$out" |
  sed -n 's/^ *\([0-9][0-9]*\) shapes, [0-9][0-9]* escaping, .*/\1/p')
n_slack=$(printf '%s\n' "$out" |
  sed -n 's/^ *[0-9][0-9]* shapes, [0-9][0-9]* escaping, \([0-9][0-9]*\) where.*/\1/p')
# The header's numbered list, delimited by where the header ends rather than by
# a line number.  This read `1,200p' until item 31 pushed the list past line
# 200, at which point it silently reported 30 -- a number about this artifact
# that had gone stale inside the machinery for catching numbers about this
# artifact that have gone stale.  The `/^# Usage:/' bound cannot drift.
item_nums=$(sed -n '1,/^# Usage:/p' check-promises.sh |
  sed -n 's/^#  *\([0-9][0-9]*\)\..*/\1/p' | sort -n)
n_items=$(printf '%s\n' "$item_nums" | tail -1)

if [ -z "$n_suite" ]; then
  echo "FAIL: the report no longer prints an 'N tests, M failing' summary, so"
  echo "      the suite size cannot be computed and every document quoting it"
  echo "      is unchecked"
  fail=1
  n_suite=-1
fi

if [ -z "$n_shapes" ] || [ -z "$n_slack" ]; then
  echo "FAIL: the report no longer prints §4.1's 'N shapes, M escaping, K where"
  echo "      arm is strictly weaker' summary, so the slack count cannot be"
  echo "      computed and the documents quoting it are unchecked"
  fail=1
  n_shapes=-1
  n_slack=-1
fi

if [ -z "$n_certprune" ]; then
  echo "FAIL: the report no longer prints §4.2's 'prunes on N shapes' summary,"
  echo "      so the documents quoting it are unchecked"
  fail=1
  n_certprune=-1
fi

# The three sources of the suite size must agree.  This is the check that
# makes the numbers below worth quoting at all: the Lean suite, the report's
# own summary line, and the emitted litmus/ tree are produced by different
# code, and a test added to one and not the others is exactly the drift
# `check-herd.sh` is too late to catch.
if [ "$n_suite" -ne "$((n_arm + n_tso))" ]; then
  echo "FAIL: the report says $n_suite tests but prints $n_arm arm and $n_tso"
  echo "      tso rows.  One of the two is not counting what it says it is"
  fail=1
fi
if [ "$n_arm" -ne "$((n_herd_arm + n_herd_pair + n_herd_wide))" ] ||
   [ "$n_tso" -ne "$n_herd_x86" ]; then
  echo "FAIL: the Lean suite ($n_arm arm, $n_tso tso) and litmus/"
  echo "      ($n_herd_arm aarch64 + $n_herd_pair pair + $n_herd_wide wide,"
  echo "      $n_herd_x86 x86_64) disagree."
  echo "      litmus/ is generated -- run ./check-herd.sh to regenerate it"
  fail=1
fi
# §4.1 claims to run the *whole* suite under both rule sets.  If it ever runs a
# subset, the containment evidence narrows without any document saying so.
if [ "$n_shapes" -ne "$n_suite" ]; then
  echo "FAIL: §4.1 ran $n_shapes shapes but the suite has $n_suite tests, so the"
  echo "      tso ⊆ arm evidence covers less than the documents claim"
  fail=1
fi

# The numbered list must be 1..n with nothing skipped or repeated, or
# `n_items` is not the number of items.
want_nums=$(i=1; while [ "$i" -le "$n_items" ]; do echo "$i"; i=$((i + 1)); done)
if [ "$item_nums" != "$want_nums" ]; then
  echo "FAIL: the numbered item list in this file's header is not 1..$n_items."
  echo "      A skipped or duplicated number makes the count wrong, and every"
  echo "      document quoting it wrong with it"
  fail=1
fi

# 28. Every number a document quotes about the artifact is marked, and every
#     mark is checked.  The marker is an HTML comment, so it renders as
#     nothing; `52<!--@suite-->` reads as "52" and means "this 52 is the
#     suite size".  A name with no site left carrying it is also a failure --
#     otherwise deleting the last mark would silently disable the check.
marker_bad=$(awk -v suite="$n_suite" -v items="$n_items" -v slack="$n_slack" \
      -v harm="$n_herd_arm" -v hx86="$n_herd_x86" -v hpair="$n_herd_pair" \
      -v hwide="$n_herd_wide" \
      -v nstates="$n_states" \
      -v certprune="$n_certprune" \
      -v gen="$(ls litmus/gen/*.litmus 2>/dev/null | wc -l | tr -d ' ')" \
      -v genx86="$(ls litmus/gen-x86/*.litmus 2>/dev/null | wc -l | tr -d ' ')" \
      -v lse2="$(ls litmus/aarch64-lse2/*.litmus 2>/dev/null | wc -l | tr -d ' ')" '
  BEGIN {
    # Check the four status-table counts.
    want["suite"] = suite; want["slack"] = slack
    want["herd-x86"] = hx86; want["herd-pair"] = hpair
    want["certprune"] = certprune
  }
  {
    line = $0
    while (match(line, /[0-9]+<!--@[a-z0-9-]+-->/)) {
      tok = substr(line, RSTART, RLENGTH); line = substr(line, RSTART + RLENGTH)
      num = tok; sub(/<!--@.*/, "", num)
      name = tok; sub(/^[0-9]+<!--@/, "", name); sub(/-->$/, "", name)
      if (!(name in want))
        printf "%s:%d: marker @%s names nothing this gate computes\n",
               FILENAME, FNR, name
      else {
        seen[name]++
        if (num + 0 != want[name] + 0)
          printf "%s:%d: quotes %s for @%s; the artifact says %s\n",
                 FILENAME, FNR, num, name, want[name]
      }
    }
  }
  END { for (k in want) if (!(k in seen)) printf "nothing is marked @%s any more\n", k }
' Promises.lean WeakMem.lean cats/*.cat)
if [ -n "$marker_bad" ]; then
  echo "FAIL: a document quotes a number the artifact does not have:"
  printf '%s\n' "$marker_bad" | sed 's/^/      /'
  fail=1
fi

# 29. Every line quoted from the report is a line the report
#     prints.  Blocks opt in with a ```report fence.  `…` is a wildcard, so a
#     quote may abbreviate -- `read=…num 0` matches the report's
#     `read=WeakMem.Val.num 0` -- and runs of whitespace are ignored, so a
#     document may align columns the report does not.  Everything else has to
#     match, which is what catches a value or a flag that changed.
#
#     This is the item that found eleven stale lines the day it was written:
#     `Repr` had started printing `WeakMem.Val.num 0` where the quotes said
#     `Val.num 0`, and nothing anywhere was able to notice.
echo "item 29: skipped"

# ---------------------------------------------------------------------------
# 30.  The generated suite.  See the header for why this one is different in
#      kind from everything above it.
# ---------------------------------------------------------------------------

echo "running the generated suites (litmus/gen, litmus/gen-x86, litmus/aarch64-acq) ..."

# The parser first, on tests whose answers are known independently of it.
# litmus/<arch>/expected.txt is emitted from the `Litmus` values' own
# `archAllows`/`states` fields; reading the *assembly* back and executing the
# reconstruction has to land on the same verdict and the same state count.
# This is what stops a parser that silently drops a dependency from making the
# generated comparison below agree about a program it is not reading -- a
# mutation that does exactly that changes three of these lines.
#
# Both front ends are exercised, because §10 has two and they share no code
# below `splitFile`.  The x86 round trip is the only thing checking that
# `xchgq` and `lock cmpxchgq` read back correctly, since diy7 cannot generate
# an RMW test for either architecture.
for d in aarch64 x86_64; do
  if ! LEAN_PATH="$BUILD" "$LEAN" --run WeakMem.lean run "litmus/$d" \
         2>/dev/null | sort > "$BUILD"/wm-roundtrip-actual.txt; then
    echo "FAIL: the §10 parser could not read litmus/$d/ back"
    fail=1
  else
    sort "litmus/$d/expected.txt" > "$BUILD"/wm-roundtrip-expected.txt
    if ! diff -u "$BUILD"/wm-roundtrip-expected.txt "$BUILD"/wm-roundtrip-actual.txt \
           > "$BUILD"/wm-roundtrip.txt; then
      echo "FAIL: parsing litmus/$d/ back does not reproduce expected.txt,"
      echo "      so §10 is not reading what §9 wrote and item 30's agreement"
      echo "      would be about a different program:"
      sed -n '3,$p' "$BUILD"/wm-roundtrip.txt | sed 's/^/      /'
      fail=1
    fi
  fi
done

# litmus/aarch64-acq/ is hand-written, but its expected.txt is likewise herd7's
# answer.  It pins the rule that an acquire read of an *external* write orders
# later accesses after the read timestamp (ARM's obs ⊇ rfe with [A];po), while
# a read of the thread's own write does not (the two rfi controls).  Before the
# fix the model allowed four of the five WRC shapes herd7 forbids.
for d in gen gen-x86 aarch64-acq; do
  n_gen=$(ls litmus/"$d"/*.litmus 2>/dev/null | wc -l | tr -d ' ')
  n_gen_exp=$(wc -l < litmus/"$d"/expected.txt | tr -d ' ')
  if [ "$n_gen" -lt 2 ]; then
    echo "FAIL: litmus/$d/ has $n_gen tests.  The differential against shapes"
    echo "      nobody here wrote is the only check in this file that was not"
    echo "      authored by someone who knew the answer; emptying the directory"
    echo "      must not be a way to pass"
    fail=1
  elif [ "$n_gen" -ne "$n_gen_exp" ]; then
    echo "FAIL: litmus/$d/ has $n_gen tests but expected.txt has $n_gen_exp"
    echo "      lines.  Re-derive the oracle with ./check-herd.sh $d"
    fail=1
  elif ! LEAN_PATH="$BUILD" "$LEAN" --run WeakMem.lean run litmus/"$d" \
           2>/dev/null | sort > "$BUILD"/wm-gen-actual.txt; then
    echo "FAIL: the model could not run litmus/$d/.  A generated shape the"
    echo "      parser does not understand is a gap, not a skip -- run"
    echo "      \`lean --run WeakMem.lean run litmus/$d\` to see which file"
    fail=1
  else
    sort litmus/"$d"/expected.txt > "$BUILD"/wm-gen-expected.txt
    if ! diff -u "$BUILD"/wm-gen-expected.txt "$BUILD"/wm-gen-actual.txt \
           > "$BUILD"/wm-gen.txt; then
      echo "FAIL: the model and herd7 disagree on some of $n_gen tests in"
      echo "      litmus/$d/ (- herd7, + this model):"
      sed -n '3,$p' "$BUILD"/wm-gen.txt | sed 's/^/      /'
      fail=1
    fi
  fi
done

# --- (hygiene) -----------------------------------------------------------------
# Every `#print axioms` line that no check above reads, and every theorem
# that had no report: 1334 names in 44 modules, std axioms only.
# A name may be printed relative to its namespace, so an optional prefix is allowed.
for thm in \
    "info_irrel" \
    "width_witness_irrelevant"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${cl_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: CoreLang.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "pcLib_typed" \
    "seqLib_typed"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${cty_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: CoreTyping.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermB5.bufInit_inv"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tb5_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermB5.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "noOwnR_valOfR" \
    "skN_substT"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tblkz_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermBlkZ.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "AppUpM.ful" \
    "AppUpM.trans" \
    "DeadVM.mono" \
    "DeadVM.ne" \
    "allocBuf_appUp" \
    "allocBuf_presV" \
    "alloc_appUp" \
    "alloc_keep" \
    "alloc_presV" \
    "appUp_lock" \
    "certified_fulfil" \
    "certified_noDeadO" \
    "certified_noDeadV" \
    "certified_of_solo" \
    "certified_promQ" \
    "certified_pub_vWrLe" \
    "certified_relStLe" \
    "deadVM_lock" \
    "evalOp_appUp" \
    "evalOp_deadO" \
    "evalOp_deadV" \
    "evalOp_ful" \
    "fenceS_appUp" \
    "fenceS_deadV" \
    "fold_appUp" \
    "holder_abovePlaceholder" \
    "injM_appUp" \
    "injM_deadV" \
    "loadUnits_appUp" \
    "loadUnits_deadV" \
    "loadUnits_readDead" \
    "plant_pub_window" \
    "projM_appUp" \
    "projM_deadV" \
    "promise_deadV" \
    "readAt_dead" \
    "solo_append" \
    "solo_deadV" \
    "solo_fulfil" \
    "solo_winInv" \
    "stepFence_relSt" \
    "stepLoadPair_deadV" \
    "stepLoadPair_read" \
    "stepLoad_deadV" \
    "stepLoad_read" \
    "stepRmwPair_appUp" \
    "stepRmwPair_deadO" \
    "stepRmwPair_deadV" \
    "stepRmwPair_prom" \
    "stepRmwPair_read" \
    "stepRmwPair_shape" \
    "stepRmw_appUp" \
    "stepRmw_deadO" \
    "stepRmw_deadV" \
    "stepRmw_ful" \
    "stepRmw_read" \
    "stepStorePair_deadV" \
    "stepStorePair_shape" \
    "stepStore_appUp" \
    "stepStore_deadO" \
    "stepStore_deadV" \
    "stepStore_ful" \
    "step_pwfAll" \
    "storeUnits_appUp" \
    "storeUnits_deadV" \
    "storeUnits_ful" \
    "threadSteps_deadV" \
    "tstep_appUp" \
    "tstep_deadV" \
    "tstep_fulfil" \
    "tstep_publish_relSt" \
    "winInv_prom" \
    "winInv_thread"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tcert_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermCert.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "Bnd_atOff_oneAt" \
    "Bnd_cons" \
    "Bnd_embed" \
    "Bnd_oneAt" \
    "BoxNamed_cut" \
    "BufOKR_transferS" \
    "BufOK_transferS" \
    "CE_Cut" \
    "CellOKR_len" \
    "CellOK_transferS" \
    "Cut_cov" \
    "Cut_fp" \
    "Cut_rini" \
    "Cut_sto" \
    "GBoxNamed_empty" \
    "GEnv.le.refl" \
    "GEnv.le.trans" \
    "GFoot_refl" \
    "GStoClo_empty" \
    "InclS.of_incl" \
    "InclS.refl" \
    "InclS_cut_pub" \
    "InclS_pub_cut" \
    "IniR_monoL" \
    "LabIn_cst" \
    "LabIn_decodeArm" \
    "LabIn_drop" \
    "LabIn_encodeArm" \
    "LabIn_nil" \
    "LabIn_ofArm" \
    "LabIn_of_get" \
    "LabIn_one" \
    "LabIn_retag" \
    "LabIn_take" \
    "MemHeldOn_mono" \
    "MemHeld_join" \
    "MemHeld_joinOn" \
    "MemHeld_split" \
    "MemHeld_splitOn" \
    "ModeOK_pub_move" \
    "ModeOK_pub_moveL" \
    "ModeOK_pub_pfr" \
    "OwnAt_cut" \
    "PairOK_transferS" \
    "PredU_cut_shared" \
    "PromAtG_nword" \
    "SegOf_accs" \
    "StoClo_Cut" \
    "StoClo_PubE" \
    "TEnv.selIni_le_one" \
    "VR_transferL" \
    "VRes_cut_shared" \
    "ValOfR_transferS" \
    "ValOfS_transferS" \
    "ValOf_transferS" \
    "WordUnit_cut_shared" \
    "cutSto_eq_shared" \
    "cutSto_own" \
    "cutSto_shared" \
    "cutSto_sub" \
    "latest_cut_G" \
    "mem_PromAtG_pred" \
    "noOR_array" \
    "noOR_loc" \
    "noOR_ptr" \
    "noOR_ptrOpt" \
    "noOR_seg" \
    "post_box_fresh" \
    "post_box_old" \
    "post_sto_fresh" \
    "post_sto_old" \
    "wordOK_back"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tcut_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermCut.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "gfoot_rini_other"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tinterf_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermInterf.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermK5Lp.bufCap_gt"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tk5lp_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermK5Lp.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermLiveHeld.bufInit_wd_frame" \
    "TermLiveHeld.casCell_no_wordAt" \
    "TermLiveHeld.caspE_no_wordAt" \
    "TermLiveHeld.dwf_no_word" \
    "TermLiveHeld.fetchCell_no_wordAt" \
    "TermLiveHeld.fresh_no_word" \
    "TermLiveHeld.grows_no_word" \
    "TermLiveHeld.solid_no_word" \
    "TermLiveHeld.stl_no_wordAt" \
    "TermLiveHeld.stlw_no_wordAt" \
    "TermLiveHeld.storeLoc_wd_frame" \
    "TermLiveHeld.storePubLoc_wd_frame" \
    "TermLiveHeld.storePub_wd_frame" \
    "TermLiveHeld.storeUnits_new_loc" \
    "TermLiveHeld.tstep_new_label" \
    "TermLiveHeld.wd_frame_comp" \
    "TermLiveHeld.wd_frame_whole" \
    "TermLiveHeld.xchgAtF_wd_frame" \
    "TermLiveHeld.xchgAt_wd_frame" \
    "TermLiveHeld.xchgLoc_wd_frame" \
    "TermLiveHeld.xchgOwn_wd_frame" \
    "TermLiveHeld.word_cell" \
    "TermLiveHeld.store_word_loc" \
    "TermLiveHeld.fetch_word_facts" \
    "TermLiveHeld.cas_word_epoch" \
    "TermLiveHeld.wd_frame_wholeG" \
    "TermLiveHeld.wd_frame_compG" \
    "TermLiveHeld.solid_no_wordG" \
    "TermLiveHeld.dwf_no_wordG" \
    "TermLiveHeld.grows_no_wordG" \
    "TermLiveHeld.storeLoc_wd_frameG" \
    "TermLiveHeld.storePub_wd_frameG" \
    "TermLiveHeld.storePubLoc_wd_frameG" \
    "TermLiveHeld.xchgOwn_wd_frameG" \
    "TermLiveHeld.xchgLoc_wd_frameG" \
    "TermLiveHeld.xchgAt_wd_frameG" \
    "TermLiveHeld.xchgAtF_wd_frameG" \
    "TermLiveHeld.bufInit_wd_frameG" \
    "TermLiveHeld.storeOwn_wd_frameG" \
    "TermLiveHeld.casCell_no_wordAtG" \
    "TermLiveHeld.fetchCell_no_wordAtG" \
    "TermLiveHeld.stl_no_wordAtG" \
    "TermLiveHeld.stlw_no_wordAtG" \
    "TermLiveHeld.caspE_no_wordAtG" \
    "TermLiveHeld.fresh_no_wordG" \
    "TermLiveHeld.nonWdFootT_of" \
    "TermLiveHeld.wd_held_core" \
    "TermLiveHeld.tstep_casp_push"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tlh_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveHeld.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermMain.sysInv_promP" \
    "lblSto_of_initShape" \
    "machine_tokens_mainF_init" \
    "machine_tokens_main_init" \
    "reachable_typedF_init" \
    "reachable_typed_init" \
    "token_unique_finalF_init" \
    "token_unique_final_init" \
    "token_unique_netF_init" \
    "token_unique_net_init"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tmain_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMain.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermMain.CrShiftP_zero" \
    "TermMain.CrShift_sum" \
    "TermMain.CrShift_zero" \
    "TermMain.Res.sum_apply'" \
    "TermMain.Res.sum_map_zero'" \
    "TermMain.TOut_zero" \
    "TermMain.nsumPerm" \
    "TermMain.nsum_le_of_nodup" \
    "TermMain.pSumAt_add" \
    "TermMain.pSumAt_key" \
    "TermMain.promsOf_nodup" \
    "TermMain.sum_promsOf" \
    "TermMain.sum_updD_le" \
    "TermMain.updD_other" \
    "TermMain.updD_self" \
    "TermMain.updD_zero"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tmdefs_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMainDefs.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermMem.EnvValR.envVal" \
    "TermMem.EnvValR.store" \
    "TermMem.alloc_hid" \
    "TermMem.loadUnits_vWr" \
    "TermMem.storeUnits_hid" \
    "TermMem.storeUnits_newOK" \
    "TermMem.storeUnits_wr" \
    "TermSound.VRR_unsee" \
    "TermSound.VR_VRR_copy" \
    "TermSound.VR_VRR_copy_closed" \
    "TermSound.VR_VRR_copy_finv" \
    "TermSound.VR_VRR_copy_frame" \
    "TermSound.WitC_VRR"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tmem_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMem.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "xfz_prom" \
    "xfz_thread"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tnohold_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermNoHold.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermOnce.MintOwnL_init" \
    "TermOnce.MintOwnL_le" \
    "TermOnce.MintOwnL_step" \
    "TermOnce.MintStep_own"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tonce_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOnce.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "hent_ofG"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${r4_termovercrc_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOverCrC.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermOwnX2.ownXLe_start_le"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${townx2_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermOwnX2.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "Desig.desigAt" \
    "TwWords_length"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tpaid_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPaid.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermPiece.GdCov_nil" \
    "TermPiece.GdCov_own" \
    "TermPiece.PSet_cases" \
    "TermPiece.PSet_insert" \
    "TermPiece.PSet_mem" \
    "TermPiece.Piece_PDisj" \
    "TermPiece.Piece_accs" \
    "TermPiece.Piece_pos" \
    "TermPiece.VRR_pset" \
    "TermPiece.accs_prod_some" \
    "TermPiece.fulP_of_fulAll" \
    "TermPiece.mem_dedupC" \
    "TermPiece.nodup_dedupC" \
    "TermPiece.nodup_map_of_inj" \
    "TermPiece.pcAt_some" \
    "TermPiece.perm_lift" \
    "TermPiece.pin_le_gdOK" \
    "TermPiece.storeUnits_fulAllP" \
    "TermPiece.sumPerm" \
    "TermStep.stepStore_AboveFW" \
    "TermStep.stepStore_NPnewQ"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tpiece_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPiece.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "BufOKR_raise" \
    "DbRes_congrD" \
    "LowestIn_sup" \
    "PlantCr_frame" \
    "PlantCr_nword" \
    "TermPiece.LowOwn_uniq" \
    "TermPiece.lt_size_of_some" \
    "TermPiece.piece_match" \
    "TermPlant.AtOff_word_lit0" \
    "TermPlant.IniAt_unitR" \
    "TermPlant.LatestNP_congr" \
    "TermPlant.LowestIn_sup" \
    "TermPlant.PatchIt.app_cov" \
    "TermPlant.PatchIt.app_get" \
    "TermPlant.PlantCr_frame" \
    "TermPlant.PlantCr_nword" \
    "TermPlant.ThInvMCF.toK" \
    "TermPlant.ThInvMCFS.toK" \
    "TermPlant.ThInvMCFSK.toF" \
    "TermPlant.cellAcct" \
    "TermPlant.cellOK_wordOK'" \
    "TermPlant.cell_word_typed" \
    "TermPlant.dropA_le" \
    "TermPlant.dropA_neg" \
    "TermPlant.dropA_pos" \
    "TermPlant.dropP_le_dropA" \
    "TermPlant.exists_WLe_pickD" \
    "TermPlant.exists_list_pick" \
    "TermPlant.fulP_bufInitN" \
    "TermPlant.fulP_nop" \
    "TermPlant.fulP_ofH" \
    "TermPlant.fulP_stepK" \
    "TermPlant.fulP_tgt" \
    "TermPlant.fulP_wordStore" \
    "TermPlant.heldPieceF" \
    "TermPlant.heldPieceF0" \
    "TermPlant.inAcc_ex" \
    "TermPlant.inAcc_one" \
    "TermPlant.loadUnits_rd1" \
    "TermPlant.lowGapF" \
    "TermPlant.mc_ofFul" \
    "TermPlant.mul_add_uniq" \
    "TermPlant.nWords_ones" \
    "TermPlant.nhid" \
    "TermPlant.no_word2_of_ones" \
    "TermPlant.nodup_map_on" \
    "TermPlant.offs_ne" \
    "TermPlant.overU_of" \
    "TermPlant.own_cohF" \
    "TermPlant.own_htyc" \
    "TermPlant.pSum_dropA_le" \
    "TermPlant.patchAll" \
    "TermPlant.patchO" \
    "TermPlant.patchW" \
    "TermPlant.patchWs" \
    "TermPlant.patch_get" \
    "TermPlant.pickCohF" \
    "TermPlant.pickOldF" \
    "TermPlant.pieceAcctF0" \
    "TermPlant.pred_of_rd" \
    "TermPlant.pred_of_win" \
    "TermPlant.rcKeepP_bufInitN" \
    "TermPlant.rcKeepP_nop" \
    "TermPlant.rcKeepP_pred" \
    "TermPlant.rcKeepP_tgt" \
    "TermPlant.rcKeep_of_rini" \
    "TermPlant.rkAddr_eq" \
    "TermPlant.stepOutRS_ofT" \
    "TermPlant.storeUnits_fulAll" \
    "TermPlant.sum_app" \
    "TermPlant.sum_filt" \
    "TermPlant.sum_idx" \
    "TermPlant.sum_le_of" \
    "TermPlant.sum_sub_le" \
    "TermPlant.tstepMCF_bufInitF" \
    "TermPlant.tstepMCF_stepKR" \
    "TermPlant.tstepMCF_stepTK" \
    "TermPlant.tstepMCF_stlF" \
    "TermPlant.tstepMCF_stlwF" \
    "TermPlant.tstepMCF_storeLocF" \
    "TermPlant.tstepMCF_storeOwnF" \
    "TermPlant.tstepMCF_xchgAtFF" \
    "TermPlant.tstepMCF_xchgAtFr" \
    "TermPlant.tstepMCF_xchgLocF" \
    "TermPlant.tstepMCF_xchgOwnF" \
    "TermPlant.tstepMR_bufInitN" \
    "TermPlant.tstepMR_stlN" \
    "TermPlant.tstepMR_stlwN" \
    "TermPlant.tstepMR_storeLocN" \
    "TermPlant.tstepMR_storeOwnN" \
    "TermPlant.tstepMR_xchgAtFN" \
    "TermPlant.tstepMR_xchgAtN" \
    "TermPlant.tstepMR_xchgLocN" \
    "TermPlant.tstepMR_xchgOwnN" \
    "TermPlant.unitA" \
    "TermPlant.unitO" \
    "TermPlant.word_typed" \
    "ThInvMCF.toK" \
    "ThInvMCFQ.toK" \
    "ThInvMCFS.toK" \
    "ThInvMCFSK.toF" \
    "dropA_le" \
    "dropA_neg" \
    "dropA_pos" \
    "dropP_le_dropA" \
    "mc_ofFulESQ" \
    "mc_ofFulSQ" \
    "pSum_dropA_le" \
    "stepOut_ofFSQ" \
    "stepOut_ofNSQ" \
    "sum_set_zero" \
    "tstepMCF_stepTK"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tplant_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlant.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermPlantAtW.nfInv_pre" \
    "TermPlantAtW.noFul_ofNF"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${k1a_termplantatw_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantAtW.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "sw_bufInit_on"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tplantf_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantF.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermPlantR1.BufR_raise" \
    "TermPlantR1.HeldEntryL_len" \
    "TermPlantR1.HeldEntryL_raise" \
    "TermPlantR1.HeldEntryL_raiseW" \
    "TermPlantR1.VRR_swap" \
    "TermPlantR1.mu_unfold_valid" \
    "TermPlantR1.raise_payL" \
    "TermPlantR1.slot_swap" \
    "TermPlantR1.wsum" \
    "TermPlantR1.wsum_split" \
    "TermPlantR1.wvE_at"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tpr1_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantR1.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermPlantS.HeldEntry_raiseZ"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tplants_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPlantS.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "keyT_poolG"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${r4_termpoolbal_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPoolBal.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermMain.tstepMC_promEc"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tps_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPromStep.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermPtrStab.promInCut_init" \
    "TermPtrStab.promInCut_prom" \
    "TermPtrStab.promInCut_thread" \
    "TermPtrStab.promInCut_threadT"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${g265_ptrstab_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPtrStab.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermRunLoc.iniLoc_mono" \
    "TermRunLoc.runAgreeF3K_of_F3" \
    "TermRunLoc.runAgreeT3K_of_T3"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${trloc_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermRunLoc.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "msg_of_undef" \
    "off_lt_buf" \
    "oneAt_all_one" \
    "undef_not_wordOK_buf"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tseen_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSeenHid.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "CoreLang.Ty.ownHead" \
    "TermSound.CE_rini" \
    "TermSound.Ext.rini" \
    "TermSound.TEnv.insR_rini" \
    "TermSound.TEnv.ownHead_cl0" \
    "TermSound.TEnv.ownTop" \
    "TermSound.TEnv.ownTop_cl" \
    "TermSound.TEnv.ownTop_congr" \
    "TermSound.TEnv.ownTop_instT" \
    "TermSound.TEnv.ownTop_of_Clo" \
    "TermSound.TEnv.ownTop_shiftI" \
    "TermSound.TEnv.ownTop_shiftIN" \
    "TermSound.TEnv.ownTop_shiftTN" \
    "TermSound.TEnv.ownTop_shiftT_insR" \
    "TermSound.TEnv.ownTop_substTs" \
    "TermSound.TEnv.ownTop_tyEq" \
    "TermSound.TEnv.selIni" \
    "TermSound.TEnv.selIni_cl" \
    "TermSound.TEnv.selIni_eq" \
    "TermSound.TEnv.selIni_instT" \
    "TermSound.TEnv.selIni_le" \
    "TermSound.TEnv.selIni_le_at" \
    "TermSound.TEnv.selIni_le_ini" \
    "TermSound.TEnv.selIni_loc" \
    "TermSound.TEnv.selIni_shiftI" \
    "TermSound.TEnv.selIni_shiftT_insR" \
    "TermSound.TEnv.selIni_substTs" \
    "TermSound.TEnv.selIni_tyEq" \
    "TermSound.WitR_call" \
    "TermSound.modeIni_clM" \
    "TermSound.modeIni_inst" \
    "TermSound.modeIni_le" \
    "TermSound.modeIni_le_ini" \
    "TermSound.modeIni_meq" \
    "TermSound.modeIni_shift" \
    "TermSound.pre_rini" \
    "TermSound.rgnFree_clK" \
    "TermSound.subE_rini" \
    "VRR_call" \
    "WitAF.af" \
    "WitAF.mg" \
    "WitAF.ni" \
    "declCx_HeldOK" \
    "noIallV_cl" \
    "tstep_callR" \
    "tstep_callcR" \
    "tstep_retR" \
    "tstep_tailR" \
    "zrel_WitL"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tsnd_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSound.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermSpawnGlobM.extZT_self" \
    "TermSpawnGlobM.extZ_self"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${b2_termspawnglobm_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnGlobM.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermSpawnMid.spawnT_bf" \
    "TermSpawnMid.spawnT_lbase" \
    "TermSpawnMid.spawnT_mem" \
    "TermSpawnMid.spawnT_pairs"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${b2_termspawnmid_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMid.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermSpawnMid.Spawn.cap_eq"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${b2_termspawnmidm0_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnMidM0.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermSpawn.ownLive_grow"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${b2_termspawnstarto_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnStartO.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "AgreeG.push0" \
    "AgreeG.unsee" \
    "AgreeK.push0" \
    "AgreeK.unsee" \
    "AgreeV.push0" \
    "AgreeV.unsee" \
    "BlkDb_grow" \
    "BlkDb_mono" \
    "BlkStart_congr" \
    "BlkZ_grow" \
    "BlkZ_mono" \
    "BufOKR.bufOK" \
    "BufOKR.full" \
    "BufOKR_iff" \
    "CellOKR_iff" \
    "CellR_up" \
    "ClR_closed" \
    "ClR_of" \
    "CoreEq.push0" \
    "CoreEq.refl" \
    "CoreEq.unsee" \
    "DStart_congr" \
    "DbRes_noIni" \
    "DbRes_rgwd_noIni" \
    "DbRes_zero" \
    "DesigAt_congr" \
    "DesigAt_iniW" \
    "DesigAt_mem" \
    "EFoot_plantE" \
    "FirstW_grow" \
    "FirstW_initAt" \
    "FirstW_shrink" \
    "HeldEntry.toS" \
    "HeldEntryL.entry" \
    "HeldEntryL_cell" \
    "HeldEntryL_ownN" \
    "HeldEntryL_ownP" \
    "HeldEntryL_tr" \
    "IniAt_monoG" \
    "IniR_monoG" \
    "Insp_unsee" \
    "KeepP_upd" \
    "LabsIn_one" \
    "LabsIn_sub" \
    "LabsV.labsIn" \
    "LabsV_nil" \
    "LabsV_noloc" \
    "LabsV_one" \
    "LabsV_takeDrop" \
    "MemHeld.toS" \
    "MemHeldK.memHeld" \
    "MemHeldK_eqs" \
    "MemHeldK_mono" \
    "MemHeldK_of" \
    "MemHeldK_ofKeep" \
    "MemHeldK_ofSSet" \
    "MemHeldK_ofSSetE" \
    "MemHeldK_slotSet" \
    "MemHeldK_tr" \
    "MemHeldK_unfocus" \
    "MemHeldK_unfocusNA" \
    "MemHeldL.cover" \
    "MemHeldL.memHeld" \
    "MemHeldL_box" \
    "MemHeldL_eqs" \
    "MemHeldL_focus" \
    "MemHeldL_focusE" \
    "MemHeldL_seeE" \
    "MemHeldL_tr" \
    "MemHeldL_trP" \
    "MemHeldL_trS" \
    "MemHeldL_unfocus" \
    "MemHeldL_unfocusAny" \
    "MemHeldXL_store" \
    "MemHeldXL_tr" \
    "MemHeld_flipLS" \
    "MemHeld_flipS" \
    "MemHeld_iffS" \
    "MemHeld_pubS" \
    "MemInv_plantSet" \
    "MemInv_plantSetK" \
    "ModeOK_monoG" \
    "NpZ_zwS" \
    "Np_le" \
    "Np_of" \
    "PinOK_frame" \
    "PinOK_keep" \
    "PredU_slot_ge" \
    "PrefixHeld_Np" \
    "PrefixHeld_zero" \
    "SFrame_updS" \
    "SKeep.toT" \
    "SKeep_noPred" \
    "SKeep_ofKeepP" \
    "SKeep_of_eq" \
    "SKeep_of_other" \
    "SKeep_refl" \
    "SKeep_set" \
    "SKeep_trans" \
    "SKeep_updS" \
    "SSet.keep" \
    "SSet_refl" \
    "SlotStart_congr" \
    "TermSound.TEnv.rc_congr" \
    "TermSound.TEnv.rc_le_ini" \
    "TermSound.TEnv.rc_max" \
    "TermSound.TEnv.rc_mono" \
    "TermSound.guardT_sub" \
    "TermSound.guardT_tyEq" \
    "TermSound.sub_opaqueOK" \
    "TermStep.AboveFW_atSame" \
    "TermStep.AboveFW_push" \
    "TermStep.AboveFW_pushM" \
    "TermStep.AtOff_trans" \
    "TermStep.AtSame_app" \
    "TermStep.AtSame_erase" \
    "TermStep.AtSame_growsL" \
    "TermStep.AtSame_push" \
    "TermStep.AtSame_refl" \
    "TermStep.AtSame_symm" \
    "TermStep.AtSame_trans" \
    "TermStep.BoxNewV_of_box" \
    "TermStep.BoxNewV_refl" \
    "TermStep.BoxTopP_growsAt" \
    "TermStep.BoxWords.imp" \
    "TermStep.BufOK_congr_lo" \
    "TermStep.CellOKR_transfer_pub" \
    "TermStep.CellOKR_uninit" \
    "TermStep.CellOK_cover" \
    "TermStep.CellOK_seg" \
    "TermStep.CohRd_of_eq" \
    "TermStep.CrKeep_alloc" \
    "TermStep.CrKeep_seeE" \
    "TermStep.CrKeep_sto" \
    "TermStep.CrKeep_stoN" \
    "TermStep.CrKeep_storeN" \
    "TermStep.CrMov_pack" \
    "TermStep.CrMov_packLe" \
    "TermStep.CrPack_le" \
    "TermStep.DbRes_congr" \
    "TermStep.DbRes_mem" \
    "TermStep.DbRes_move" \
    "TermStep.DbRes_nInit" \
    "TermStep.DbRes_nfu" \
    "TermStep.DbRes_noword" \
    "TermStep.DbRes_nvisU" \
    "TermStep.DbRes_ownz" \
    "TermStep.DbRes_rg_noWord" \
    "TermStep.DbRes_uninit" \
    "TermStep.DbRes_vis" \
    "TermStep.DbRes_wd_nInit" \
    "TermStep.EFoot.riniW" \
    "TermStep.EFoot.rinieq" \
    "TermStep.EFoot_fresh" \
    "TermStep.EFoot_ini" \
    "TermStep.EFoot_plant" \
    "TermStep.EFoot_pub" \
    "TermStep.EFoot_refl" \
    "TermStep.EFoot_seeBox" \
    "TermStep.Ext_unsee" \
    "TermStep.FRes_congr" \
    "TermStep.FirstW_atSame" \
    "TermStep.FirstW_push" \
    "TermStep.FirstW_uniq" \
    "TermStep.FlipOK_of" \
    "TermStep.Foot_ext" \
    "TermStep.FpAt_congr" \
    "TermStep.FpAt_nil" \
    "TermStep.FpAt_priv" \
    "TermStep.FpAt_sub" \
    "TermStep.FpAt_vis" \
    "TermStep.FreshArr_eq" \
    "TermStep.FreshIn_sto" \
    "TermStep.FulW.trans" \
    "TermStep.HeldEntry_ownN" \
    "TermStep.HeldEntry_ownP" \
    "TermStep.HiddenP_le" \
    "TermStep.HoldW.congrE" \
    "TermStep.IniAt_monoAt" \
    "TermStep.IniAt_of_IniW" \
    "TermStep.IniAt_of_seg" \
    "TermStep.IniSegN.mono" \
    "TermStep.IniSegN_of_InitR" \
    "TermStep.IniW.ofEq" \
    "TermStep.IniW_congr" \
    "TermStep.IniW_congrU" \
    "TermStep.IniW_none" \
    "TermStep.IniW_word" \
    "TermStep.IniWr.ofEq" \
    "TermStep.IniWr_congr" \
    "TermStep.IniWr_of" \
    "TermStep.InitAt_prefix" \
    "TermStep.InitRr.initR" \
    "TermStep.InitRr_of_IniSegN" \
    "TermStep.LatestNP_appNo" \
    "TermStep.LatestNP_atSame" \
    "TermStep.LatestNP_erase_otherF" \
    "TermStep.LatestNP_ex" \
    "TermStep.LatestNP_growsAtF" \
    "TermStep.LatestNP_subErase" \
    "TermStep.LatestP_NP" \
    "TermStep.LatestP_NPN" \
    "TermStep.LatestP_NPmsg" \
    "TermStep.LatestP_NPmsgN" \
    "TermStep.LatestP_growsAt" \
    "TermStep.LatestSF_none" \
    "TermStep.LatestSF_of_LatestS" \
    "TermStep.LatestS_coh_congr" \
    "TermStep.LatestS_coh_eq" \
    "TermStep.LoadCoh_load" \
    "TermStep.LoadCoh_of_eq" \
    "TermStep.LoadCoh_rd" \
    "TermStep.MemHeld_flip" \
    "TermStep.MemHeld_flipL" \
    "TermStep.MemHeld_plant" \
    "TermStep.MemHeld_pub" \
    "TermStep.MemHeld_seeE" \
    "TermStep.MemInv_boxF" \
    "TermStep.MemInv_plant" \
    "TermStep.MemInv_plantF" \
    "TermStep.MemInv_plantFH" \
    "TermStep.MemInv_plantFK" \
    "TermStep.MemInv_plantFN" \
    "TermStep.MemInv_plantFNr" \
    "TermStep.MemInv_plantU" \
    "TermStep.MemInv_seeBox" \
    "TermStep.MemInv_storeAtI" \
    "TermStep.MintStep_own_sto" \
    "TermStep.NVP_env" \
    "TermStep.NVP_eqs" \
    "TermStep.NVP_mono" \
    "TermStep.NVP_of_nvis" \
    "TermStep.NVP_priv" \
    "TermStep.NVP_store" \
    "TermStep.OldCr_zero" \
    "TermStep.OverU_mono" \
    "TermStep.Over_mono" \
    "TermStep.OwnCellF_alloc" \
    "TermStep.OwnCellF_pub" \
    "TermStep.OwnCellF_push_prom" \
    "TermStep.OwnCellF_store" \
    "TermStep.OwnCellF_storeOther" \
    "TermStep.OwnFrontierRMW_priv" \
    "TermStep.OwnHidP.imp" \
    "TermStep.OwnNVPF_of" \
    "TermStep.OwnNVP_cell" \
    "TermStep.OwnNVP_of_F" \
    "TermStep.OwnOKPF_cellP" \
    "TermStep.OwnOKPF_load" \
    "TermStep.OwnOKPF_tail" \
    "TermStep.OwnOKP_store" \
    "TermStep.OwnOKP_storeAt" \
    "TermStep.OwnOKSF_coh" \
    "TermStep.OwnOKSF_live" \
    "TermStep.OwnOKSF_of_OwnOKS" \
    "TermStep.OwnOKSF_pair" \
    "TermStep.OwnOKSF_read1" \
    "TermStep.OwnOKSF_word" \
    "TermStep.OwnOKS_priv" \
    "TermStep.OwnPubV.alloc" \
    "TermStep.OwnPubV.allocBuf" \
    "TermStep.OwnPubV.eqv" \
    "TermStep.OwnPubV.mono" \
    "TermStep.OwnPubV.store" \
    "TermStep.PredU_bump" \
    "TermStep.PredU_congr" \
    "TermStep.PredU_initRr" \
    "TermStep.PredU_nonArr" \
    "TermStep.PredU_own" \
    "TermStep.PredU_vis" \
    "TermStep.PredWords_eq_read" \
    "TermStep.PromAt_atSame" \
    "TermStep.PromAt_congr" \
    "TermStep.PromAt_lat" \
    "TermStep.PromAt_noProm" \
    "TermStep.PromAt_nwordP" \
    "TermStep.PromAt_pred" \
    "TermStep.PromAt_privL" \
    "TermStep.PromAt_sub" \
    "TermStep.PromCrP_drop" \
    "TermStep.PromCrP_of" \
    "TermStep.PromCr_dbLe" \
    "TermStep.PromCr_erase" \
    "TermStep.PromCr_keep" \
    "TermStep.PubG_tr" \
    "TermStep.PubWin_of_NoHold" \
    "TermStep.ReadTs_of_LatestNP" \
    "TermStep.ReadTs_uniq" \
    "TermStep.ReadsV_unit" \
    "TermStep.ResEqv_congr" \
    "TermStep.ResEqv_nvis" \
    "TermStep.ResEqv_refl" \
    "TermStep.ResEqv_trans" \
    "TermStep.RiniW_of_eq" \
    "TermStep.RiniW_of_ne" \
    "TermStep.Steps.inv" \
    "TermStep.ThInvMC_plant" \
    "TermStep.ThInvMC_promise_plant" \
    "TermStep.ThInvMF.toMT" \
    "TermStep.ThInvMFA.toF" \
    "TermStep.ThInvMFS.toA" \
    "TermStep.ThInvMFS.toF" \
    "TermStep.ThInvMFS_congr" \
    "TermStep.ThInvM_promise" \
    "TermStep.VRR_buf_R" \
    "TermStep.VRR_cell_R" \
    "TermStep.VRR_det" \
    "TermStep.VRR_ofVR_locW" \
    "TermStep.VRR_ofVR_ptrOptW" \
    "TermStep.VRR_ofVR_ptrW" \
    "TermStep.VRR_ofVR_reflocW" \
    "TermStep.VRR_transfer" \
    "TermStep.VRR_word_nundef" \
    "TermStep.VR_transfer" \
    "TermStep.VRes_congr" \
    "TermStep.VRes_nfu" \
    "TermStep.VRes_nvisU" \
    "TermStep.VRes_uninit" \
    "TermStep.VRes_vis" \
    "TermStep.WordUnit_of_WordAt" \
    "TermStep.accs_cl_unfold" \
    "TermStep.allocBuf_newT" \
    "TermStep.allocBuf_okP" \
    "TermStep.allocBuf_undef" \
    "TermStep.allocBuf_undefT" \
    "TermStep.allocBuf_vWr_le" \
    "TermStep.allocE_sto_cases" \
    "TermStep.alloc_coh_le_vWr" \
    "TermStep.alloc_fulW" \
    "TermStep.alloc_newT" \
    "TermStep.alloc_nonempty" \
    "TermStep.alloc_okP" \
    "TermStep.alloc_size_fr" \
    "TermStep.alloc_undef" \
    "TermStep.apply_fetch_nundef" \
    "TermStep.atOff_word_nz" \
    "TermStep.buf_runtime" \
    "TermStep.buf_runtime'" \
    "TermStep.bumpIni_le_max" \
    "TermStep.casWordC_core" \
    "TermStep.case_armBR" \
    "TermStep.case_armBS" \
    "TermStep.case_armNBS" \
    "TermStep.cellP_tail" \
    "TermStep.cellP_tailLoad" \
    "TermStep.close_ptr" \
    "TermStep.dropP_le" \
    "TermStep.envV_tail" \
    "TermStep.evalOp_fld_ownW" \
    "TermStep.evalOp_idx_ownW" \
    "TermStep.exists_least_nat" \
    "TermStep.fenceS_vWr_le" \
    "TermStep.fence_region" \
    "TermStep.fetchC_core" \
    "TermStep.flip_at" \
    "TermStep.foldr_max_mem" \
    "TermStep.heldBufInit" \
    "TermStep.heldMixAt" \
    "TermStep.heldStoreAt" \
    "TermStep.held_nundef" \
    "TermStep.held_of_prefix" \
    "TermStep.held_uninit" \
    "TermStep.hiddenP_wordOK" \
    "TermStep.iniAt_rc_of_iniWr" \
    "TermStep.keep_region" \
    "TermStep.lay_closed" \
    "TermStep.le_foldr_max" \
    "TermStep.le_of_unhidden" \
    "TermStep.lift" \
    "TermStep.liftS" \
    "TermStep.loadUnits_cohMsg" \
    "TermStep.loadUnits_nonemptyT" \
    "TermStep.loadUnits_readsV" \
    "TermStep.loadUnits_topP" \
    "TermStep.loadUnits_topPA" \
    "TermStep.locLoadI" \
    "TermStep.mc_liftF" \
    "TermStep.mc_liftPL" \
    "TermStep.mc_ofKF" \
    "TermStep.mc_ofPL" \
    "TermStep.mem_PromAt_pred" \
    "TermStep.modeIni_own_rc" \
    "TermStep.newBuf_z_none" \
    "TermStep.not_VisU_none" \
    "TermStep.nvis_dwf" \
    "TermStep.nvis_priv" \
    "TermStep.offs_eq" \
    "TermStep.offs_neW" \
    "TermStep.ownLoadAtF" \
    "TermStep.ownLoadF" \
    "TermStep.ownPtr_view" \
    "TermStep.ownW_ne_own" \
    "TermStep.ownW_offs" \
    "TermStep.own_cellP" \
    "TermStep.own_msgWordsN" \
    "TermStep.own_msgWordsP" \
    "TermStep.own_tailW" \
    "TermStep.pSum_dropP_le" \
    "TermStep.pairStoreHeld" \
    "TermStep.pin_le_at" \
    "TermStep.plantLoadAtV" \
    "TermStep.plant_holdF" \
    "TermStep.projM_ownS" \
    "TermStep.projM_ownT" \
    "TermStep.promise_acct" \
    "TermStep.pubLoadAtV" \
    "TermStep.pure_state" \
    "TermStep.rgnFree_Fd" \
    "TermStep.riniW_bufInit" \
    "TermStep.rini_ite_max" \
    "TermStep.rmwPairAcc" \
    "TermStep.rmwPlainAcc" \
    "TermStep.rmw_ownLatest" \
    "TermStep.segLoadV" \
    "TermStep.skel_unfold_mu" \
    "TermStep.skel_word" \
    "TermStep.stepLoadPair_topS" \
    "TermStep.stepLoad_topS" \
    "TermStep.stepPresW_of" \
    "TermStep.stepStore_AtSame" \
    "TermStep.stepStore_NPkeepF" \
    "TermStep.stepStore_NPsameF" \
    "TermStep.stepStore_NPsameP" \
    "TermStep.stepStore_fulW" \
    "TermStep.step_inv" \
    "TermStep.storeUnits_NPkeep" \
    "TermStep.storeUnits_NPmix" \
    "TermStep.storeUnits_cohLe" \
    "TermStep.storeUnits_cohOff" \
    "TermStep.storeUnits_cohW" \
    "TermStep.storeUnits_cohWr" \
    "TermStep.storeUnits_fulW" \
    "TermStep.storeUnits_hidP" \
    "TermStep.storeUnits_packLe" \
    "TermStep.storeUnits_twoCoh" \
    "TermStep.storeUnits_vWr_mono" \
    "TermStep.storeUnits_written" \
    "TermStep.store_promAbove_unit" \
    "TermStep.substS_subst1" \
    "TermStep.sum_map_le" \
    "TermStep.sum_sublist_split" \
    "TermStep.tstepMCF_step" \
    "TermStep.tstepMCF_stepK" \
    "TermStep.tstepMCF_stepP" \
    "TermStep.tstepMC_bufInit" \
    "TermStep.tstepMC_casWord" \
    "TermStep.tstepMC_casWordLoc" \
    "TermStep.tstepMC_fetch" \
    "TermStep.tstepMC_fetchLoc" \
    "TermStep.tstepMC_inlB" \
    "TermStep.tstepMC_inrB" \
    "TermStep.tstepMC_prom" \
    "TermStep.tstepMC_promE" \
    "TermStep.tstepMC_publish" \
    "TermStep.tstepMC_step" \
    "TermStep.tstepMC_stepA" \
    "TermStep.tstepMC_stl" \
    "TermStep.tstepMC_stlw" \
    "TermStep.tstepMC_storeLoc" \
    "TermStep.tstepMC_storeOwn" \
    "TermStep.tstepMC_storePub" \
    "TermStep.tstepMC_storePubLoc" \
    "TermStep.tstepMC_xchgAt" \
    "TermStep.tstepMC_xchgAtF" \
    "TermStep.tstepMC_xchgLoc" \
    "TermStep.tstepMC_xchgOwn" \
    "TermStep.tstepMF_step" \
    "TermStep.tstepMR_bufInit" \
    "TermStep.tstepMR_caseB" \
    "TermStep.tstepMR_inlB" \
    "TermStep.tstepMR_inlBB" \
    "TermStep.tstepMR_inrB" \
    "TermStep.tstepMR_inrBB" \
    "TermStep.tstepMR_new" \
    "TermStep.tstepMR_publish" \
    "TermStep.tstepMR_stl" \
    "TermStep.tstepMR_stlw" \
    "TermStep.tstepMR_storeLoc" \
    "TermStep.tstepMR_storeOwn" \
    "TermStep.tstepMR_storePub" \
    "TermStep.tstepMR_storePubLoc" \
    "TermStep.tstepMR_xchgAt" \
    "TermStep.tstepMR_xchgAtF" \
    "TermStep.tstepMR_xchgLoc" \
    "TermStep.tstepMR_xchgOwn" \
    "TermStep.tstepM_caseBS" \
    "TermStep.tstepM_caseS" \
    "TermStep.tstepM_caseTS" \
    "TermStep.tstepM_fetch" \
    "TermStep.tstepM_fetchLoc" \
    "TermStep.tstepM_inlBBS" \
    "TermStep.tstepM_inlBS" \
    "TermStep.tstepM_inlS" \
    "TermStep.tstepM_inlTS" \
    "TermStep.tstepM_inrBBS" \
    "TermStep.tstepM_inrBS" \
    "TermStep.tstepM_inrS" \
    "TermStep.tstepM_inrTS" \
    "TermStep.tstepM_newA" \
    "TermStep.tstepM_newBufA" \
    "TermStep.tstepM_openPub" \
    "TermStep.tstepM_region" \
    "TermStep.tstepM_stepA" \
    "TermStep.tstepSA" \
    "TermStep.tstep_footprint" \
    "TermStep.tstep_footprintMC" \
    "TermStep.unit_Lay" \
    "TermStep.unit_VR" \
    "TermStep.view_le_readBound" \
    "TermStep.wr_le_rg" \
    "TermStep.zero_unfold1" \
    "ThInvMCFS.toF" \
    "TouchS_store" \
    "Ty.tier_iall" \
    "Ty.tier_iex" \
    "Ty.tier_mu" \
    "Ty.tier_tex" \
    "VR_monoG" \
    "VR_monoH" \
    "VR_monoJ" \
    "VR_monoK" \
    "VR_word1_nundef" \
    "ValOf_monoG" \
    "ValOf_monoH" \
    "ValOf_monoJ" \
    "ValOf_monoK" \
    "Valid_isBoxed" \
    "VisD_congr" \
    "ZwZ_mono" \
    "accs_iex_one" \
    "accs_tex_one" \
    "decodeArm_head0" \
    "decodeArm_labs" \
    "decodeArm_labsV" \
    "heldBufInitL" \
    "heldMixAtL" \
    "heldOneL" \
    "heldPairL" \
    "heldStoreAtL" \
    "heldWordA" \
    "heldWordL" \
    "held_uninitA" \
    "le_Np" \
    "modeIni_leG" \
    "modeIni_leK" \
    "modeIni_leV" \
    "nWords_one_eq" \
    "nWords_zero_nil" \
    "noJunk" \
    "noJunkA" \
    "noJunk_valOf" \
    "not_DesigAt_of" \
    "not_VisD_none" \
    "not_VisD_priv" \
    "ofArm_labs" \
    "ofArm_labsF" \
    "ofArm_labsV" \
    "ownTop_noOwn" \
    "own_segL" \
    "pairStoreHeldL" \
    "plantE_ini_in" \
    "plantE_ini_ne" \
    "plantE_pfr_in" \
    "plantE_pfr_ne" \
    "rmwPairAccL" \
    "rmwPlainAccL" \
    "rmwWordAccL" \
    "seg_arr_width" \
    "selIni_leG" \
    "selIni_leK" \
    "selIni_leV" \
    "single_nundef" \
    "slotCnt_arr" \
    "slotR_imp" \
    "slotR_raise" \
    "tstepMCF_step" \
    "wordStoreHeldL"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tstep_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStep.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "IniAt_of_IniWr" \
    "apply_num_read" \
    "bufInit_own" \
    "cas_e_nu" \
    "cas_pred" \
    "cell_mode" \
    "fetch_pred" \
    "foreign_frontier" \
    "foreign_pred" \
    "mode_frontier" \
    "notOwn" \
    "own_pred" \
    "peekVal_cl" \
    "pred_of_adj" \
    "pw_le_storeMview" \
    "stl_own" \
    "stlw_own" \
    "store_cell" \
    "store_view" \
    "units_view" \
    "xchgAtF_own" \
    "xchgAt_own" \
    "xchg_cell" \
    "xchg_view"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tspr_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStepPred.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "AllPromLt_init" \
    "AllPromLt_promise" \
    "Cut_withFp" \
    "FpOwnFree_init" \
    "FpOwnFree_promise" \
    "FrontierLe_gfoot" \
    "FrontierLe_init" \
    "FrontierLe_mono" \
    "FrontierLe_withFp" \
    "NewIn.left" \
    "NewIn.mono" \
    "NewIn.of_eq" \
    "NewIn.trans" \
    "OnceIn.left" \
    "OnceIn.of_eq" \
    "OnceIn.of_newInF" \
    "PromsDisj_init" \
    "PromsDisj_promise" \
    "PubE_withFp" \
    "SysInvW.bnamed_cut" \
    "SysInvW.bnamed_withFp" \
    "SysInvW.book_promise" \
    "SysInvW.book_thread" \
    "SysInvW.fpokOf" \
    "SysInvW.freshMem" \
    "SysInvW.frle_thread" \
    "SysInvW.newOwn_wordOK" \
    "SysInvW.newOwn_wordOK_init" \
    "SysInvW.newOwn_wordOK_init_sc" \
    "SysInvW.newOwn_wordOK_sc" \
    "SysInvW.publish_noOwnUse" \
    "SysInvW.publish_ownZero" \
    "SysInvW.rle_cut" \
    "SysInvW.rle_thread" \
    "SysInvW.rle_withFp" \
    "VMono.refl'" \
    "VMono.trans" \
    "VWrLe_init" \
    "VWrLe_promise" \
    "VWrLe_thread" \
    "allProms_promise" \
    "allocBuf_vmono" \
    "alloc_vmono" \
    "casp_ua" \
    "cellOK_cover" \
    "cellOK_wordOK" \
    "enter_vmono" \
    "evalOp_bufInit_new" \
    "evalOp_fetch_new" \
    "evalOp_newOp" \
    "evalOp_once" \
    "evalOp_stl_new" \
    "evalOp_stlw_new" \
    "evalOp_store_new" \
    "evalOp_stp_new" \
    "evalOp_vmono" \
    "evalOp_xchgAtF_new" \
    "evalOp_xchgAt_new" \
    "evalOp_xchg_new" \
    "fenceS_vmono" \
    "gfoot_ini_box" \
    "gfoot_ini_own" \
    "gfoot_ini_shared" \
    "ini_withFp" \
    "injM_vmono" \
    "isRef_buf" \
    "isRef_cell" \
    "isRef_cellOr" \
    "isRef_epair" \
    "isRef_word" \
    "isRef_word2" \
    "isRef_xchg" \
    "loadUnits_nalloc" \
    "loadUnits_vmono" \
    "lockFence_vWr" \
    "mem_allProms" \
    "mem_allProms_upd" \
    "newIn_alloc" \
    "newIn_allocBuf" \
    "newIn_allocBuf'" \
    "newIn_projInj" \
    "newIn_storeUnits" \
    "newMsg_wordOK_ownAll" \
    "newMsg_wordOK_ownInit" \
    "newMsg_wordOK_ownPlanted" \
    "newPos_b5" \
    "newPos_sw" \
    "newPos_ua" \
    "offs_inj" \
    "offs_one" \
    "offs_zero" \
    "oneAt_ful" \
    "or_iffA" \
    "or_iffB" \
    "pair_ua" \
    "peek_sto" \
    "projM_nalloc" \
    "projM_vmono" \
    "promise_other" \
    "rmwPair_newAt" \
    "rmwPair_newLoc" \
    "rmwPair_once" \
    "rmwPair_vmono" \
    "rmw_newAt" \
    "rmw_newLoc" \
    "rmw_once" \
    "rmw_vmono" \
    "role_lt" \
    "role_of_newRole" \
    "role_two0" \
    "role_two1" \
    "stepFence_vWr" \
    "stepRmwPair_vmono" \
    "stepRmw_vmono" \
    "stepper_newPos" \
    "storeUnits_once" \
    "storeUnits_onceIn" \
    "storeUnits_vmono" \
    "stp_ua" \
    "sw_noWord2" \
    "tgt_of" \
    "threadSteps_upd" \
    "tstep_newNotProm" \
    "tstep_newOp" \
    "tstep_newPos" \
    "tstep_newPosE" \
    "tstep_once" \
    "tstep_vWr" \
    "tstep_vmono" \
    "twoAt_twoAt" \
    "twoAt_word2" \
    "units_new" \
    "vr_sto" \
    "wordOK_pub"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tstp_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStepper.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "BoxTopP_of_G" \
    "GStoMg.elem" \
    "GStoMg_empty" \
    "SysInvW.hown" \
    "SysInvW.ownUniq" \
    "SysInvW.own_thread"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tsys_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSys.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermTear.CErini" \
    "TermTear.selIni_CE"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${ttear_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermTear.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "instantiate_admits" \
    "mg_cl"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${ttv_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermTv.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "AtOff_word_lit" \
    "DbRes_own_zero" \
    "Fd_Clo" \
    "FrBound_foot" \
    "FrBound_inspM" \
    "FrBound_refl" \
    "IniAt_nonbuf" \
    "InvAtXR_prom" \
    "InvAtX_of" \
    "InvAtX_promOf" \
    "PromCr_own_zero" \
    "SW_nundef" \
    "StoClo_EFoot" \
    "VR_one_nundef" \
    "VRes_own_zero" \
    "WrUp.trans" \
    "accs_iex_cases" \
    "accs_tex_cases" \
    "allocBuf_wrUp" \
    "alloc_wrUp" \
    "bufF_slot" \
    "bufInit_nu" \
    "bufInit_ua" \
    "buf_slot" \
    "cas_nu" \
    "cell_nu" \
    "cell_ua" \
    "certified_holderWord" \
    "certified_noPairPromX" \
    "certified_prefixHeld" \
    "certified_promNotUndefX" \
    "certified_promNumX" \
    "certified_promTypedX" \
    "certified_promWordNX" \
    "certified_promWordX" \
    "decodeArm_head" \
    "enter_wrUp" \
    "evalOp_fulC" \
    "evalOp_wrUp" \
    "fetch_ful_core" \
    "fetch_ful_num" \
    "fetch_ful_numL" \
    "fetch_ful_numP" \
    "flipOK_cert" \
    "lane_slotN" \
    "lane_slotW" \
    "loadUnits_wrUp" \
    "locPub_encFwd" \
    "locPub_encRev" \
    "locPub_mem_val" \
    "locPub_ofArmRev" \
    "locPub_push0_rels" \
    "nWords_eq_one" \
    "nu_nil" \
    "nu_num" \
    "nu_single" \
    "nu_two" \
    "oneAt_append" \
    "oneAt_not_two" \
    "oneAt_single" \
    "ownZeroAt_use_ne" \
    "own_num" \
    "publish_noOwnUse" \
    "publish_ownZero" \
    "rmwPair_wrUp" \
    "rmw_wrUp" \
    "solo_ownZero" \
    "solo_typedX" \
    "solo_typedXR" \
    "stl_ua" \
    "stlw_ua" \
    "storeUnits_fulC" \
    "storeUnits_wrUp" \
    "store_nu" \
    "store_ua" \
    "sum_map_key_zero" \
    "swAt_of_ua" \
    "tstep_fulC" \
    "tstep_wrUp" \
    "unitsOp_nu" \
    "unitsOp_sw" \
    "unitsOp_ua" \
    "useVal_cl" \
    "use_own_ne" \
    "wordOK_one" \
    "wordOK_pubRef" \
    "wordOK_slot1" \
    "wordOK_word" \
    "xchgAtF_nu" \
    "xchgAtF_ua" \
    "xchgAt_nu" \
    "xchgAt_ua" \
    "xchg_nu" \
    "xchg_ua"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${ttyped_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermTyped.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "TermViewInv.eo_asLanes" \
    "TermViewInv.eo_band" \
    "TermViewInv.eo_bit1" \
    "TermViewInv.eo_bits" \
    "TermViewInv.eo_borrow" \
    "TermViewInv.eo_call" \
    "TermViewInv.eo_callc" \
    "TermViewInv.eo_claim" \
    "TermViewInv.eo_cvt" \
    "TermViewInv.eo_endBorrow" \
    "TermViewInv.eo_fcmp" \
    "TermViewInv.eo_fld" \
    "TermViewInv.eo_fnptr" \
    "TermViewInv.eo_fold" \
    "TermViewInv.eo_fop" \
    "TermViewInv.eo_fop1" \
    "TermViewInv.eo_freeze" \
    "TermViewInv.eo_idx" \
    "TermViewInv.eo_lane" \
    "TermViewInv.eo_mkEPair" \
    "TermViewInv.eo_mkTicket" \
    "TermViewInv.eo_mkWord2" \
    "TermViewInv.eo_nameI" \
    "TermViewInv.eo_null" \
    "TermViewInv.eo_pack" \
    "TermViewInv.eo_packT" \
    "TermViewInv.eo_rem" \
    "TermViewInv.eo_setLane" \
    "TermViewInv.eo_sub" \
    "TermViewInv.eo_toInt" \
    "TermViewInv.eo_validate" \
    "TermViewInv.eo_vmatch" \
    "TermViewInv.eo_zero"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tve1_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermViewInvE1.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "eo_fence" \
    "eo_fetch" \
    "eo_inl" \
    "eo_inr" \
    "eo_intoRgn" \
    "eo_ldp" \
    "eo_load" \
    "eo_stp"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tve2_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermViewInvE2.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "eo_ldl" \
    "eo_ldlw" \
    "eo_loadAt" \
    "eo_loadAtF" \
    "eo_stlw" \
    "eo_xchgAtF"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tve3_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermViewInvE3.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
for thm in \
    "lock_excludes_one_attempt"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tut_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: Tutorial.lean (hygiene): '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermC1*.lean (G2, region c1) ---------------------------
# Temporary parallel copies of checkW/drf/ModeOK/noOR/PubCpl/PlantEdge/PubWinTN under new names;
# nothing switches.  TermC1Guards' #guard lines are the c1 guards and the 51-site census.
# Deleted (with these modules) when the new definitions replace the old ones.
echo "building TermC1Defs.lean ..."
if ! c1_termc1defs_out=$(leanb TermC1Defs 2>&1); then
  echo "$c1_termc1defs_out"
  echo 'FAIL: TermC1Defs.lean does not compile.'
  fail=1
fi
case "$c1_termc1defs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermC1Defs.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.ProgScopeOKW1.scope" \
    "TermC1.ProgScopeOKW1.wrap"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1defs_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Defs.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building TermC1Inv.lean ..."
if ! c1_termc1inv_out=$(leanb TermC1Inv 2>&1); then
  echo "$c1_termc1inv_out"
  echo 'FAIL: TermC1Inv.lean does not compile.'
  fail=1
fi
case "$c1_termc1inv_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermC1Inv.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.PubWinTN1.pub" \
    "TermC1.noOR1_of_noOR" \
    "TermC1.PlantEdge1_of_PlantEdge" \
    "TermC1.ModeOK1_pub" \
    "TermC1.ModeOK1_own"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1inv_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Inv.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building TermC1Lem.lean ..."
if ! c1_termc1lem_out=$(leanb TermC1Lem 2>&1); then
  echo "$c1_termc1lem_out"
  echo 'FAIL: TermC1Lem.lean does not compile.'
  fail=1
fi
case "$c1_termc1lem_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermC1Lem.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.noMonoSaw_not_tornLic" \
    "TermC1.rgnOpOK1_load" \
    "TermC1.rgnOpOK1_store" \
    "TermC1.rgnOpOK1_xchg" \
    "TermC1.rgnOpOK1_fetch" \
    "TermC1.noRes_of_not_affine" \
    "TermC1.noRes_of_affine_false" \
    "TermC1.noRes_of_rgnPay" \
    "TermC1.adapt_noOwn"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1lem_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Lem.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building TermC1Guards.lean ..."
if ! c1_termc1guards_out=$(leanb TermC1Guards 2>&1); then
  echo "$c1_termc1guards_out"
  echo 'FAIL: TermC1Guards.lean does not compile.'
  fail=1
fi
case "$c1_termc1guards_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermC1Guards.lean theorem has a sorry"
    fail=1 ;;
esac


# --- TermMicro.lean (stream G: the micro-step machine) ------------------------------
# One memory event per machine step; TermRun is unchanged.  A new module that no final
# imports, so it changes no premise.  Its #print axioms block is the list below.
echo "building TermMicro.lean ..."
if ! micro_out=$(leanb TermMicro 2>&1); then
  echo "$micro_out"
  echo 'FAIL: TermMicro.lean does not compile.'
  fail=1
fi
case "$micro_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermMicro.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermMicro.evalOp_eq" \
    "TermMicro.tstep_plan" \
    "TermMicro.tstep_eq_run" \
    "TermMicro.certified_certifiedM" \
    "TermMicro.step_sim" \
    "TermMicro.steps_sim" \
    "TermMicro.sysInvM_embed" \
    "TermMicro.sysInvM_run"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${micro_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMicro.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPairLayout.lean (pair-layout invariant on reachable configurations) ------
# A new module (imports only TermSpawnDefs) that no final imports, so it changes no
# premise.  Its #print axioms block is the list below (11 exports).
echo "building TermPairLayout.lean ..."
if ! pair_out=$(leanb TermPairLayout 2>&1); then
  echo "$pair_out"
  echo 'FAIL: TermPairLayout.lean does not compile.'
  fail=1
fi
case "$pair_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermPairLayout.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
for thm in \
    "TermPairLayout.pairInv_runG" \
    "TermPairLayout.pairStep_runG" \
    "TermPairLayout.pairInv_reach_init" \
    "TermPairLayout.pairInv_reach_initOK" \
    "TermPairLayout.pairInv_reach_spawn" \
    "TermPairLayout.pair_layout" \
    "TermPairLayout.pairStep_step" \
    "TermPairLayout.pairInv_runS" \
    "TermPairLayout.pairStep_runS" \
    "TermPairLayout.pairInv_of_initOK" \
    "TermPairLayout.pairInv_spawnS"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${pair_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPairLayout.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermMemTyped.lean ----------------------------------------------------------
# TermMemTyped.
echo "building TermMemTyped.lean ..."
if ! kc_termmemtyped_out=$(leanb TermMemTyped 2>&1); then
  echo "$kc_termmemtyped_out"
  echo 'FAIL: TermMemTyped.lean does not compile.'
  fail=1
fi
case "$kc_termmemtyped_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermMemTyped.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermMemTyped: every #print axioms theorem, std axioms only.
for thm in \
    "TermMemTyped.memTyped_of_frameTie" \
    "TermMemTyped.reachable_memTyped" \
    "TermMemTyped.reachable_memTyped_init" \
    "TermMemTyped.segOf_ref" \
    "TermMemTyped.single_word" \
    "TermMemTyped.ptrOpt_of_wordOK" \
    "TermMemTyped.ptr_of_wordOK" \
    "TermMemTyped.ptrTypedAt_of" \
    "TermMemTyped.reachable_ptrTyped" \
    "TermMemTyped.reachable_ptrTyped_init"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${kc_termmemtyped_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermMemTyped.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermScopeStart.lean --------------------------------------------------------
# TermScopeStart.
echo "building TermScopeStart.lean ..."
if ! kc_termscopestart_out=$(leanb TermScopeStart 2>&1); then
  echo "$kc_termscopestart_out"
  echo 'FAIL: TermScopeStart.lean does not compile.'
  fail=1
fi
case "$kc_termscopestart_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermScopeStart.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermScopeStart: every #print axioms theorem, std axioms only.
for thm in \
    "TermScopeStart.runScope_entry" \
    "TermScopeStart.runScope_spawnS"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${kc_termscopestart_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermScopeStart.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermScopeLib.lean ----------------------------------------------------------
# TermScopeLib.
echo "building TermScopeLib.lean ..."
if ! kc_termscopelib_out=$(leanb TermScopeLib 2>&1); then
  echo "$kc_termscopelib_out"
  echo 'FAIL: TermScopeLib.lean does not compile.'
  fail=1
fi
case "$kc_termscopelib_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermScopeLib.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermScopeLib: every #print axioms theorem, std axioms only.
for thm in \
    "TermScopeLib.ok_of_accepts" \
    "TermScopeLib.queue_int_checked" \
    "TermScopeLib.queue_pay_checked" \
    "TermScopeLib.queue_ptr_checked" \
    "TermScopeLib.queue_int_scopeW" \
    "TermScopeLib.queue_pay_scopeW" \
    "TermScopeLib.queue_ptr_scopeW" \
    "TermScopeLib.queue_int_runScope" \
    "TermScopeLib.queue_pay_runScope" \
    "TermScopeLib.queue_ptr_runScope" \
    "TermScopeLib.fhm_lib_false_scope" \
    "TermScopeLib.fhm_lib_true_scope" \
    "TermScopeLib.fhm_inst_9_scope" \
    "TermScopeLib.fhm_inst_20_scope" \
    "TermScopeLib.fhm_own_false_scope" \
    "TermScopeLib.fhm_own_true_scope" \
    "TermScopeLib.fhm_lib_false_runScope" \
    "TermScopeLib.fhm_lib_true_runScope" \
    "TermScopeLib.fhm_inst_9_runScope" \
    "TermScopeLib.fhm_inst_20_runScope" \
    "TermScopeLib.fhm_own_false_runScope" \
    "TermScopeLib.fhm_own_true_runScope"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${kc_termscopelib_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermScopeLib.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermZeroS.lean -------------------------------------------------------------
# TermZeroS.
echo "building TermZeroS.lean ..."
if ! kc_termzeros_out=$(leanb TermZeroS 2>&1); then
  echo "$kc_termzeros_out"
  echo 'FAIL: TermZeroS.lean does not compile.'
  fail=1
fi
case "$kc_termzeros_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermZeroS.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermZeroS: every #print axioms theorem, std axioms only.
for thm in \
    "TermZeroS.zeroPair_spec" \
    "TermZeroS.zeroableIn_eq"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${kc_termzeros_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermZeroS.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermScopeFHM.lean ----------------------------------------------------------
# TermScopeFHM.
echo "building TermScopeFHM.lean ..."
if ! kc_termscopefhm_out=$(leanb TermScopeFHM 2>&1); then
  echo "$kc_termscopefhm_out"
  echo 'FAIL: TermScopeFHM.lean does not compile.'
  fail=1
fi
case "$kc_termscopefhm_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermScopeFHM.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermScopeFHM: every #print axioms theorem, std axioms only.
for thm in \
    "TermScopeFHM.fhm_lib_false_scopeW" \
    "TermScopeFHM.fhm_lib_true_scopeW" \
    "TermScopeFHM.fhm_inst_9_scopeW" \
    "TermScopeFHM.fhm_inst_20_scopeW" \
    "TermScopeFHM.fhm_own_false_scopeW" \
    "TermScopeFHM.fhm_own_true_scopeW" \
    "TermScopeFHM.fhm_lib_false_checked" \
    "TermScopeFHM.fhm_lib_true_checked" \
    "TermScopeFHM.fhm_inst_9_checked" \
    "TermScopeFHM.fhm_inst_20_checked" \
    "TermScopeFHM.fhm_own_false_checked" \
    "TermScopeFHM.fhm_own_true_checked"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${kc_termscopefhm_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermScopeFHM.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- G3a (region c1): publish-family helpers in TermStep, TermC1Rgn.lean ---
# TermStep's publish helpers (tstepM_publish's proof now uses them; its statement is unchanged).
for thm in \
    "TermStep.tb_use" \
    "TermStep.pubTyFacts" \
    "TermStep.pubTyFactsBuf" \
    "TermStep.ownPtr_inv" \
    "TermStep.ownBuf_inv" \
    "TermStep.Lay_ptr_remode" \
    "TermStep.pubEnvAt_seen" \
    "TermStep.pubCell_post"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tstep_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# TermC1Rgn: PubWinTN1e (certification window at every region, dead binders included); region and
# intoRgn publish their cell (thread layer).  Nothing switches; deleted or
# merged when the new definitions replace the old ones.
echo "building TermC1Rgn.lean ..."
if ! c1_termc1rgn_out=$(leanb TermC1Rgn 2>&1); then
  echo "$c1_termc1rgn_out"
  echo 'FAIL: TermC1Rgn.lean does not compile.'
  fail=1
fi
case "$c1_termc1rgn_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermC1Rgn.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.PubWinTN1e.pub" \
    "TermC1.PubWinTN1e.toN1" \
    "TermC1.PubWinTN1e.rgn" \
    "TermC1.PubWinTN1e.into" \
    "TermC1.ThInvMFR1.toF" \
    "TermC1.ModeOK1_rgn_seen" \
    "TermC1.RgnPubT1.of" \
    "TermC1.IntoPubT1.of" \
    "TermC1.pwLab" \
    "TermC1.pubStep1" \
    "TermC1.tstepM_region1" \
    "TermC1.ThInvMFI1.toF" \
    "TermC1.tstepM_intoRgn1"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1rgn_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Rgn.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done


# --- G3b (region c1): MR publish helpers in TermStep, TermC1RgnR.lean ---
# TermStep: tstepMR_publish's proof now uses pubCellR_post; region_stepR follows from
# region_stepRT (statements unchanged).
for thm in \
    "TermStep.pubCellR_post" \
    "TermStep.region_stepRT"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tstep_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# TermC1RgnR: region and intoRgn publish their cell (resource and credit layers).  Nothing
# switches; deleted or merged when the new definitions replace the old ones.
echo "building TermC1RgnR.lean ..."
if ! c1_termc1rgnr_out=$(leanb TermC1RgnR 2>&1); then
  echo "$c1_termc1rgnr_out"
  echo 'FAIL: TermC1RgnR.lean does not compile.'
  fail=1
fi
case "$c1_termc1rgnr_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermC1RgnR.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.RgnLe1.of_le1" \
    "TermC1.pubStepR1" \
    "TermC1.tstepMR_region1" \
    "TermC1.tstepMR_intoRgn1" \
    "TermC1.tstepMC_region1_of" \
    "TermC1.tstepMC_intoRgn1_of"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1rgnr_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1RgnR.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done


# --- G4 (region c1): mode-generic cell load/store in TermStep, TermC1Ld.lean ---
# TermStep: the pub load/store lemmas are re-proved on mode-generic cell lemmas (statements unchanged).
for thm in \
    "TermStep.pubFr" \
    "TermStep.ptr_view" \
    "TermStep.loadCell_core" \
    "TermStep.loadCell_step" \
    "TermStep.tstepM_loadCell" \
    "TermStep.tstepMR_loadCell" \
    "TermStep.modeIni_ne_own" \
    "TermStep.tstepM_storeCell" \
    "TermStep.tstepMR_storeCell" \
    "TermStep.tstepM_loadCellLoc" \
    "TermStep.tstepMR_loadCellLoc" \
    "TermStep.tstepM_storeCellLoc" \
    "TermStep.tstepMR_storeCellLoc"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${tstep_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# TermC1Ld: load/store at region cells, held to the pub clause (hypothesis hmo).
# Nothing switches; deleted or merged when the new definitions replace the old ones.
echo "building TermC1Ld.lean ..."
if ! c1_termc1ld_out=$(leanb TermC1Ld 2>&1); then
  echo "$c1_termc1ld_out"
  echo 'FAIL: TermC1Ld.lean does not compile.'
  fail=1
fi
case "$c1_termc1ld_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermC1Ld.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.arrFree_adapt" \
    "TermC1.adapt_cl" \
    "TermC1.rgnV" \
    "TermC1.rgn_adaptT" \
    "TermC1.rgn_adapt" \
    "TermC1.rgnLoc_adaptL" \
    "TermC1.accs_rgnSub" \
    "TermC1.rgnLoc_adaptS" \
    "TermC1.rgnLoad_facts" \
    "TermC1.rgnSub" \
    "TermC1.rgnStore_facts" \
    "TermC1.tstepM_loadRgn1" \
    "TermC1.tstepMR_loadRgn1" \
    "TermC1.tstepMC_loadRgn1" \
    "TermC1.tstepM_storeRgn1" \
    "TermC1.tstepMR_storeRgn1" \
    "TermC1.tstepMC_storeRgn1" \
    "TermC1.tstepM_loadRgnLoc1" \
    "TermC1.tstepMR_loadRgnLoc1" \
    "TermC1.tstepMC_loadRgnLoc1" \
    "TermC1.tstepM_storeRgnLoc1" \
    "TermC1.tstepMR_storeRgnLoc1" \
    "TermC1.tstepMC_storeRgnLoc1"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1ld_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Ld.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done


# --- G5 (region c1, D-4): TermC1Ptr.lean, ModeOK1 facts for region pointer payloads ---
# Nothing switches; deleted or merged when the new definitions replace the old ones.
echo "building TermC1Ptr.lean ..."
if ! c1_termc1ptr_out=$(leanb TermC1Ptr 2>&1); then
  echo "$c1_termc1ptr_out"
  echo 'FAIL: TermC1Ptr.lean does not compile.'
  fail=1
fi
case "$c1_termc1ptr_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermC1Ptr.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.noOR1_ptr" \
    "TermC1.noOR1_ptrOpt" \
    "TermC1.noOR1_loc" \
    "TermC1.ModeOK1_eq_pub" \
    "TermC1.ModeOK1_pfr" \
    "TermC1.ModeOK1_move" \
    "TermC1.ModeOK1_moveL" \
    "TermC1.ModeOK1_toPub"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1ptr_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Ptr.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done


# --- G7 (region c1): TermPubSto helpers, TermC1Win.lean (seen half of the region window) ---
# TermPubSto: pubSto_of_typed is re-proved on ownSto_of_use / ownBufSto_of_use (statement unchanged).
# g286_termpubsto_out is set by the TermPubSto build above.
for thm in \
    "TermPubSto.ownSto_of_use" \
    "TermPubSto.ownBufSto_of_use"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${g286_termpubsto_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPubSto.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# TermC1Win: a typed region / intoRgn names an own store cell; NoHold at a seen one.  Nothing switches.
echo "building TermC1Win.lean ..."
if ! c1_termc1win_out=$(leanb TermC1Win 2>&1); then
  echo "$c1_termc1win_out"
  echo 'FAIL: TermC1Win.lean does not compile.'
  fail=1
fi
case "$c1_termc1win_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermC1Win.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.rgnSto_of_typed" \
    "TermC1.intoSto_of_typed" \
    "TermC1.rgn_noHold_seen" \
    "TermC1.into_noHold_seen"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1win_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Win.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# TermC1Drf: drf1 survives closing (all witnesses drf1) and folding; drf implies drf1 (S4).  Nothing switches.
echo "building TermC1Drf.lean ..."
if ! c1_termc1drf_out=$(leanb TermC1Drf 2>&1); then
  echo "$c1_termc1drf_out"
  echo 'FAIL: TermC1Drf.lean does not compile.'
  fail=1
fi
case "$c1_termc1drf_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermC1Drf.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.drfM_clM" \
    "TermC1.drf1_clK_up" \
    "TermC1.drf1_clK" \
    "TermC1.drf1_cl" \
    "TermC1.drf1_cl0K" \
    "TermC1.drf1_cl0" \
    "TermC1.drf1_cl_shift" \
    "TermC1.drf1_unfold" \
    "TermC1.drf1_Fd" \
    "TermC1.drf1_of_drf"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1drf_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Drf.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# TermC1Cnt: counted words with region references counted (mPub1/sNo1/pubWords1/cntIdx1); agreement off region references.  Nothing switches.
echo "building TermC1Cnt.lean ..."
if ! c1_termc1cnt_out=$(leanb TermC1Cnt 2>&1); then
  echo "$c1_termc1cnt_out"
  echo 'FAIL: TermC1Cnt.lean does not compile.'
  fail=1
fi
case "$c1_termc1cnt_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermC1Cnt.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.mPub1_of_mPub" \
    "TermC1.sNo1_of_sNo" \
    "TermC1.sNo1_eq" \
    "TermC1.pub1_eq" \
    "TermC1.pubWords1_of_sNo1" \
    "TermC1.sNo1_rgn" \
    "TermC1.filterMap_tagIdx" \
    "TermC1.cntIdx1_of_sNo1" \
    "TermC1.cntIdx1_eq" \
    "TermC1.pubWords1_adapt"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1cnt_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Cnt.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# TermC1Pay: a region payload closes to a coupledOK, copyable, drf1 type at kind-respecting witnesses.  Nothing switches.
echo "building TermC1Pay.lean ..."
if ! c1_termc1pay_out=$(leanb TermC1Pay 2>&1); then
  echo "$c1_termc1pay_out"
  echo 'FAIL: TermC1Pay.lean does not compile.'
  fail=1
fi
case "$c1_termc1pay_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermC1Pay.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.admits_wit" \
    "TermC1.rgnPay_cl0" \
    "TermC1.wit_of_ask" \
    "TermC1.rgnPay_cl0_admits"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1pay_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Pay.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# TermC1Wit: WitR1/WitOK1 (every witness drf1) and their preservation; closes the region-payload premise; PackTOK1 (the packT scope check).  Nothing switches.
echo "building TermC1Wit.lean ..."
if ! c1_termc1wit_out=$(leanb TermC1Wit 2>&1); then
  echo "$c1_termc1wit_out"
  echo 'FAIL: TermC1Wit.lean does not compile.'
  fail=1
fi
case "$c1_termc1wit_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermC1Wit.lean theorem has a sorry"
    fail=1 ;;
esac
for thm in \
    "TermC1.ask_true_iff" \
    "TermC1.WitR1_iff" \
    "TermC1.WitR1_nil" \
    "TermC1.WitR1_wit" \
    "TermC1.mentions_lt" \
    "TermC1.WitR1_occ" \
    "TermC1.drf1_cl_frame" \
    "TermC1.rgnPay_cl0_frame" \
    "TermC1.subE_wit_call" \
    "TermC1.WitR1_call" \
    "TermC1.WitR1_pushT" \
    "TermC1.noIallV_of_drf1" \
    "TermC1.WitOK1_pack" \
    "TermC1.opOK1_tys" \
    "TermC1.allOK1_tail" \
    "TermC1.PackTOK1.drf1" \
    "TermC1.packTOK1_of_opOK1"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${c1_termc1wit_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermC1Wit.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermSpawnSuccs.lean ------------------------------------------------------------
# (E3) explorer Spawn successors (not wired into successorsAll) and their soundness.
echo "building TermSpawnSuccs.lean ..."
if ! e3_spawnsuccs_out=$(leanb TermSpawnSuccs 2>&1); then
  echo "$e3_spawnsuccs_out"
  echo 'FAIL: TermSpawnSuccs.lean does not compile.'
  fail=1
fi
case "$e3_spawnsuccs_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermSpawnSuccs.lean theorem has a sorry"
    fail=1 ;;
esac
# TermSpawnSuccs: every #print axioms theorem, std axioms only.
for thm in \
    "TermSpawnSuccs.spawnSuccs_sound"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${e3_spawnsuccs_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermSpawnSuccs.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermStartW.lean ----------------------------------------------------------------
# (E3, R2 = A') the wrapper start: InitShape/EntryOK/RunScope at startW.
echo "building TermStartW.lean ..."
if ! e3_startw_out=$(leanb TermStartW 2>&1); then
  echo "$e3_startw_out"
  echo 'FAIL: TermStartW.lean does not compile.'
  fail=1
fi
case "$e3_startw_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a TermStartW.lean theorem has a sorry"
    fail=1 ;;
esac
# TermStartW: every #print axioms theorem, std axioms only.
for thm in \
    "TermStartW.startW_get" \
    "TermStartW.allOK_exitTail" \
    "TermStartW.allOK_wrapTerm" \
    "TermStartW.wcx_tvOK" \
    "TermStartW.runScope_startW" \
    "TermStartW.heldOK_entry" \
    "TermStartW.entryOK_wrap" \
    "TermStartW.initShape_startW"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${e3_startw_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermStartW.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermPermitV.lean ---------------------------------------------------------------
# (D4, T4(A) B1 = (i)) permits stay below the memory size along StepsE runs (PermV; cited by parkVs' docstring).
echo "building TermPermitV.lean ..."
if ! d4_permitv_out=$(leanb TermPermitV 2>&1); then
  echo "$d4_permitv_out"
  echo 'FAIL: TermPermitV.lean does not compile.'
  fail=1
fi
case "$d4_permitv_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermPermitV.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermPermitV: every #print axioms theorem, std axioms only.
for thm in \
    "TermPermit.permV_startW" \
    "TermPermit.permit_cap" \
    "TermPermit.permit_le_size"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')  # names may contain ? ! etc.
  if ! echo "${d4_permitv_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermPermitV.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- UTstep, USem, UElabSim, UHyg, ULive (UnElab M2s: semantics, T2, T3) ----------
# UTstep: tstep on sentinel continuations (tstep_head_subst).  USem: UnElab's machine ustep, run through the core
# tstep on sentinels (call/callc/tail/ret by hand), configuration moves through the core functions.  UElabSim:
# elabT k e = (layer k e).core, tstep_elab, T2 (StepsU -> StepsE on images; StepsE from an image -> some U run;
# image<->image needs [K2]).  UHyg: the hygiene invariant UInv, kept by every U move, true at startU.  ULive: T3,
# liveness_iff for the TermLiveMach/TermLiveGrow headlines on image starts, explorer_iff (per edge, crash,
# ClassHyp; not exploreG's loop).  No machineU_sound (false, [K1]).
echo "building UTstep.lean ..."
if ! utstep_out=$(leanb UTstep 2>&1); then
  echo "$utstep_out"
  echo 'FAIL: UTstep.lean: a sentinel tstep lemma failed.'
  fail=1
fi
case "$utstep_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a UTstep.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
for thm in "UnElab.tstep_let" "UnElab.tstep_head_subst" "UnElab.tstep_let_cont" "UnElab.tstep_head_env"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${utstep_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: UTstep.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building USem.lean ..."
if ! usem_out=$(leanb USem 2>&1); then
  echo "$usem_out"
  echo 'FAIL: USem.lean: does not compile.'
  fail=1
fi
case "$usem_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a USem.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
for thm in "UnElab.ustep" "UnElab.uThreadSteps" "UnElab.uExtCfg" "UnElab.uSpawnCfg"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${usem_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: USem.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building UElabSim.lean ..."
if ! uelabsim_out=$(leanb UElabSim 2>&1); then
  echo "$uelabsim_out"
  echo 'FAIL: UElabSim.lean: a simulation (T2) theorem failed.'
  fail=1
fi
case "$uelabsim_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a UElabSim.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
for thm in "UnElab.focus_elab" "UnElab.elab_layer" "UnElab.tstep_elab" "UnElab.ustep_nil_iff" "UnElab.uCertified_iff" "UnElab.UStep.toCore" "UnElab.UStep.ofCore" "UnElab.T2_fwd" "UnElab.T2_bwd" "UnElab.uNoSpawnP_iff" "UnElab.uAtSite_iff" "UnElab.uExtSite_iff" "UnElab.uSiteNoProm_iff"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${uelabsim_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: UElabSim.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building UHyg.lean ..."
if ! uhygc_out=$(leanb UHyg 2>&1); then
  echo "$uhygc_out"
  echo 'FAIL: UHyg.lean: a hygiene-invariant theorem failed.'
  fail=1
fi
case "$uhygc_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a UHyg.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
for thm in "UnElab.hygE_of_noRes" "UnElab.layer_letOp_hyg" "UnElab.layer_head_hyg" "UnElab.ustep_inv" "UnElab.StepsU.inv" "UnElab.toCoreCfg_startU" "UnElab.uInv_start" "UnElab.uInv_reach"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${uhygc_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: UHyg.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
echo "building ULive.lean ..."
if ! ulive_out=$(leanb ULive 2>&1); then
  echo "$ulive_out"
  echo 'FAIL: ULive.lean: a liveness-transfer (T3) theorem failed.'
  fail=1
fi
case "$ulive_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a ULive.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
for thm in "UnElab.liveness_iff_robust" "UnElab.liveness_iff_tokenFree" "UnElab.liveness_iff_forced" "UnElab.liveness_iff_livelock" "UnElab.liveness_iff_robustX" "UnElab.liveness_iff_forcedX" "UnElab.liveness_iff_livelockX" "UnElab.liveness_iff_robustXC" "UnElab.liveness_iff_forcedXC" "UnElab.liveness_iff_livelockXC" "UnElab.robust_transfer" "UnElab.tokenFree_transfer" "UnElab.forced_transfer" "UnElab.livelock_transfer" "UnElab.robustX_transfer" "UnElab.forcedX_transfer" "UnElab.livelockX_transfer" "UnElab.robustXC_transfer" "UnElab.forcedXC_transfer" "UnElab.livelockXC_transfer" "UnElab.machineU_S_iff" "UnElab.machineXU_S_iff" "UnElab.machineXCU_S_iff" "UnElab.imgU_closed" "UnElab.imgU_startW" "UnElab.successorsL_img" "UnElab.crashCfg_elab" "UnElab.classHyp_iff" "UnElab.explorer_iff"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${ulive_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: ULive.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- EM0Prelude.lean ----------------------------------------------------------------
# (E3) the EM0 prelude (source = AST #guard).
echo "building EM0Prelude.lean ..."
if ! e3_prelude_out=$(leanb EM0Prelude 2>&1); then
  echo "$e3_prelude_out"
  echo 'FAIL: EM0Prelude.lean does not compile.'
  fail=1
fi
case "$e3_prelude_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a EM0Prelude.lean theorem has a sorry"
    fail=1 ;;
esac

# --- EM0.lean -----------------------------------------------------------------------
# (E3) the EM0 program: syntax round trip, checker and explorer #guards.
echo "building EM0.lean ..."
if ! e3_em0_out=$(leanb EM0 2>&1); then
  echo "$e3_em0_out"
  echo 'FAIL: EM0.lean does not compile.'
  fail=1
fi
case "$e3_em0_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a EM0.lean theorem has a sorry"
    fail=1 ;;
esac

# --- LostWakeDemo.lean ---------------------------------------------------------
# The faithful permit makes a lost wake-up visible. EM0 as written: the spawn-machine search (capacity 2, no
# promises) is complete with no stuck configuration and no fair livelock. EM0 with the worker's `unpark` deleted
# (`em0Lost`): the search is complete and stuck, and at every node with no thread move some thread is parked at `park`
# holding no permit (the reason). The #guards state this; the printed report is the reason.
echo "building LostWakeDemo.lean ..."
if ! d4_lostwake_out=$(leanb LostWakeDemo 2>&1); then
  echo "$d4_lostwake_out"
  echo 'FAIL: LostWakeDemo.lean does not compile.  A failing #guard is an error,'
  echo '      so EM0 or its unpark-less variant no longer behaves as the note says.'
  fail=1
fi
case "$d4_lostwake_out" in
  *"declaration uses"*|*sorryAx*)
    echo "FAIL: a LostWakeDemo.lean theorem has a sorry"
    fail=1 ;;
esac
case "$d4_lostwake_out" in
  *"em0Lost: STUCK at node "*"parked at \`park\` with no permit"*) ;;
  *)
    echo "FAIL: LostWakeDemo.lean: the lost-wake-up report (stuck node, parked thread, no permit) is missing"
    fail=1 ;;
esac

# --- UElabTest.lean (UnElab M2) ------------------------------------------------------
# The elaboration against the libraries and EM0: every library program is an UnElab program meaning itself (and
# the UnElab parser reads its printed .w back); EM0 in UnElab elaborates to EM0Prelude/EM0's .w up to value-binder
# names; checkProg, ProgScopeOKW and checkProgU accept it; rule 6 (nested index binders); rule 4's lint;
# diagnostics goldens.
echo "building UElabTest.lean ..."
if ! uelabt_out=$(leanr UElabTest.lean 2>&1); then
  echo "$uelabt_out"
  echo 'FAIL: UElabTest.lean: an elaboration guard failed.'
  fail=1
fi

# --- TermScopeEM0.lean --------------------------------------------------------------
# (E3) EM0 program-side obligations (kernel, zero_decide) and the *_hello finals.
echo "building TermScopeEM0.lean ..."
if ! e3_scopeem0_out=$(leanb TermScopeEM0 2>&1); then
  echo "$e3_scopeem0_out"
  echo 'FAIL: TermScopeEM0.lean does not compile.'
  fail=1
fi
case "$e3_scopeem0_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermScopeEM0.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermScopeEM0: every #print axioms theorem, std axioms only.
for thm in \
    "TermScopeEM0.em0_checked" \
    "TermScopeEM0.em0_scopeW" \
    "TermScopeEM0.em0_wrap_check" \
    "TermScopeEM0.em0_wrap_checkW" \
    "TermScopeEM0.em0_initShape" \
    "TermScopeEM0.em0_initOK" \
    "TermScopeEM0.em0_oblX" \
    "TermScopeEM0.machine_tokens_main_hello" \
    "TermScopeEM0.token_unique_net_hello" \
    "TermScopeEM0.token_unique_final_hello" \
    "TermScopeEM0.reachable_typed_hello"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${e3_scopeem0_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermScopeEM0.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermStartD.lean / DmaRing.lean ---------------------------------------------------
# Device start + DMA ring: the board finals and the ring final.
echo "building TermStartD.lean ..."
if ! startd_out=$(leanb TermStartD 2>&1); then
  echo "$startd_out"
  echo 'FAIL: TermStartD.lean does not compile.'
  fail=1
fi
case "$startd_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermStartD.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
echo "building DmaRing.lean ..."
if ! dmaring_out=$(leanb DmaRing 2>&1); then
  echo "$dmaring_out"
  echo 'FAIL: DmaRing.lean does not compile.'
  fail=1
fi
case "$dmaring_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a DmaRing.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# DmaRing: every #print axioms theorem, std axioms only.
for thm in \
    "TermStartD.initShape_startD" \
    "TermStartD.runScope_startD" \
    "TermStartD.token_unique_net_board" \
    "DmaRing.ring_argOK"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${dmaring_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: DmaRing.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done
# TermStartD has no #print axioms lines, so its registered finals are checked from
# a file generated here (no olean is written).
devstart_ax_tmp=$(mktemp -d)
cat > "$devstart_ax_tmp/DevStartAxioms.lean" <<'EOF'
import TermStartD
import DmaRing
#print axioms TermStartD.token_unique_net_board
#print axioms TermStartD.token_unique_final_board
#print axioms TermStartD.machine_tokens_main_board
#print axioms TermStartD.reachable_typed_board
#print axioms DmaRing.dma_ring_tokens_unique_net
EOF
if ! devstart_ax_out=$(LEAN_PATH="$BUILD" "$LEAN" $(dyn) "$devstart_ax_tmp/DevStartAxioms.lean" 2>&1); then
  echo "$devstart_ax_out"
  echo 'FAIL: the device-start axioms check file does not compile.'
  fail=1
fi
rm -rf "$devstart_ax_tmp"
for thm in \
    "TermStartD.token_unique_net_board" \
    "TermStartD.token_unique_final_board" \
    "TermStartD.machine_tokens_main_board" \
    "TermStartD.reachable_typed_board" \
    "DmaRing.dma_ring_tokens_unique_net"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${devstart_ax_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: device-start finals: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermProgressDefs.lean ------------------------------------------------------
# Progress vocabulary: StuckWhy, SpawnBy, ExtBy, MovesBy.
echo "building TermProgressDefs.lean ..."
if ! i36_defs_out=$(leanb TermProgressDefs 2>&1); then
  echo "$i36_defs_out"
  echo 'FAIL: TermProgressDefs.lean does not compile.'
  fail=1
fi
case "$i36_defs_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermProgressDefs.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermProgressDefs: every #print axioms theorem, std axioms only.
for thm in \
    "TermProgress.movesBy_step"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${i36_defs_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermProgressDefs.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermProgress.lean ----------------------------------------------------------
# (item 36) per-thread progress on EM0 runs (progress_main), its sharpness (stuck_sharp), configuration level (progress_main_cfg); guarded headlines (tools/premises).
echo "building TermProgress.lean ..."
if ! i36_prog_out=$(leanb TermProgress 2>&1); then
  echo "$i36_prog_out"
  echo 'FAIL: TermProgress.lean does not compile.'
  fail=1
fi
case "$i36_prog_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermProgress.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermProgress: every #print axioms theorem, std axioms only.
for thm in \
    "TermProgress.lt_of_get" \
    "TermProgress.cert_movesBy" \
    "TermProgress.threadStep_promFree" \
    "TermProgress.spawnT_cases" \
    "TermProgress.thr_typed" \
    "TermProgress.site_eval" \
    "TermProgress.publish_progress" \
    "TermProgress.pf_progress" \
    "TermProgress.progress_main" \
    "TermProgress.stuck_sharp" \
    "TermProgress.progress_main_cfg"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${i36_prog_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermProgress.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveProv.lean ----------------------------------------------------------
# (item 37) protocols a program names; provenance along EM0 runs (S2).
echo "building TermLiveProv.lean ..."
if ! l37_prov_out=$(leanb TermLiveProv 2>&1); then
  echo "$l37_prov_out"
  echo 'FAIL: TermLiveProv.lean does not compile.'
  fail=1
fi
case "$l37_prov_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermLiveProv.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermLiveProv: every #print axioms theorem, std axioms only.
for thm in \
    "TermLiveL3.protosTy_substTs" \
    "TermLiveL3.evalOp_tyIn" \
    "TermLiveL3.tstep_thProvM" \
    "TermLiveL3.progTypedM_stepsE" \
    "TermLiveL3.progTyped_stepsE"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${l37_prov_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveProv.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveMachE.lean ---------------------------------------------------------
# (item 37) machineE: the liveness machine with extern and spawn moves (S0).
echo "building TermLiveMachE.lean ..."
if ! l37_mache_out=$(leanb TermLiveMachE 2>&1); then
  echo "$l37_mache_out"
  echo 'FAIL: TermLiveMachE.lean does not compile.'
  fail=1
fi
case "$l37_mache_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermLiveMachE.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermLiveMachE: every #print axioms theorem, std axioms only.
for thm in \
    "TermLiveL3.mstepE_step" \
    "TermLiveL3.machineE_run_stepsE"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${l37_mache_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveMachE.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveL3.lean ------------------------------------------------------------
# (item 37) setting, start provenance (wrapper, scenarios), hold view (S3, S7).
# (item 37) inversion at a touched word; TouchesW/InducedW; the robust-branch theorems (S4, S5).
echo "building TermLiveL3.lean ..."
if ! l37_l3_out=$(leanb TermLiveL3 2>&1); then
  echo "$l37_l3_out"
  echo 'FAIL: TermLiveL3.lean does not compile.'
  fail=1
fi
case "$l37_l3_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermLiveL3.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermLiveL3: every #print axioms theorem, std axioms only.
for thm in \
    "TermLiveL3.startOKX_of_scenario" \
    "TermLiveL3.setting_of_scenario" \
    "TermLiveL3.setting_of_initOK" \
    "TermLiveL3.progTyped_startW" \
    "TermLiveL3.setting_of_startW" \
    "TermLiveL3.scenarioStart_iff" \
    "TermLiveL3.progTypedM_spawnS" \
    "TermLiveL3.settingM_of_setting" \
    "TermLiveL3.settingM_of_scenarioK" \
    "TermLiveL3.touched_inv" \
    "TermLiveL3.touched_inv_mem" \
    "TermLiveL3.touched_mentionedM" \
    "TermLiveL3.touched_mentioned" \
    "TermLiveL3.not_heldV_of_robustPwf" \
    "TermLiveL3.robust_touchedFreeM" \
    "TermLiveL3.no_induced_of_touchedFree" \
    "TermLiveL3.no_induced_livelock_robust2_thmM" \
    "TermLiveL3.robust_touchedFree_thm" \
    "TermLiveL3.no_induced_livelock_robust2_thm" \
    "TermLiveL3.no_induced_livelock_robust2_scenario" \
    "TermLiveL3.inducedW_induced"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${l37_l3_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveL3.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveCert*.lean ---------------------------------------------------------
# (item 38 v1) certificate-checked liveness completeness on machineE (promise-free runs, POR off):
# TermLiveCert (the checker `check` and its definitions), TermLiveCertMoves/Key (movesPF = machineE thread moves;
# cfgKey/canon), TermLiveCertRun (no_livelock_of_check (FairS), no_livelock_of_check_fair, reach_of_check,
# outcome_of_check, terminates_of_check), TermLiveCertScen (cfgCoh_scenario: a ScenarioStartK start is coherent),
# TermLiveCertGen (the UNTRUSTED generator certOf; its #guards are compiled evaluation, no theorem uses them).
# TermLiveCertJoin (item 38 wiring): the kernel side of sce's certificate files -- check_intro (check from its
# node ranges), all_range_join, the noSpawnB/noStuckB range intros, and the *At statements at a ScenarioStartK
# start of the same key (scenario forms of the frozen theorems above).
for l38_m in TermLiveCert TermLiveCertMoves TermLiveCertKey TermLiveCertRun TermLiveCertScen TermLiveCertGen TermLiveCertJoin; do
  echo "building $l38_m.lean ..."
  if ! l38_out=$(leanb "$l38_m" 2>&1); then
    echo "$l38_out"
    echo "FAIL: $l38_m.lean does not compile."
    fail=1
  fi
  case "$l38_out" in
    *"declaration uses"*|*sorryAx*|*ofReduceBool*)
      echo "FAIL: a $l38_m.lean theorem has a sorry or a native_decide"
      fail=1 ;;
  esac
  case "$l38_m" in
    TermLiveCertRun) l38_thms="TermLiveCert.no_livelock_of_check TermLiveCert.no_livelock_of_check_fair TermLiveCert.reach_of_check TermLiveCert.outcome_of_check TermLiveCert.terminates_of_check" ;;
    TermLiveCertScen) l38_thms="TermLiveCert.cfgCoh_scenario" ;;
    TermLiveCertJoin) l38_thms="TermLiveCert.all_range_join TermLiveCert.check_intro TermLiveCert.check_congr TermLiveCert.noSpawnB_intro TermLiveCert.noStuckB_intro TermLiveCert.noLivelockAt_of_check TermLiveCert.noLivelockFairAt_of_check TermLiveCert.outcomesAt_of_check TermLiveCert.terminatesAt_of_check" ;;
    *) l38_thms="" ;;
  esac
  for thm in $l38_thms; do
    thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
    if ! echo "${l38_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
      echo "FAIL: $l38_m.lean: '#print axioms $thm' missing or non-standard axioms"
      fail=1
    fi
  done
done

# --- TermLiveC.lean -------------------------------------------------------------
# The held branch: HeldBy, the witness extension across machineE moves, held_latest_const,
# forced_wait_held_thm (PromFreeFrom: a run restriction, not a fairness condition).
echo "building TermLiveC.lean ..."
if ! l15c_out=$(leanb TermLiveC 2>&1); then
  echo "$l15c_out"
  echo 'FAIL: TermLiveC.lean does not compile.'
  fail=1
fi
case "$l15c_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermLiveC.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermLiveC: every #print axioms theorem, std axioms only.
for thm in \
    "TermLiveC.debt_zero_of_allNoProm" \
    "TermLiveC.sysInvO_mstepE_ext" \
    "TermLiveC.held_latest_const" \
    "TermLiveC.mstep_wit" \
    "TermLiveC.wit_keep" \
    "TermLiveC.thread_new_env" \
    "TermLiveC.suffix_induct" \
    "TermLiveC.forced_wait_held_thm"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${l15c_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveC.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveC2.lean ------------------------------------------------------------
# (item 15 C) the held branch for protocol pairs: HeldBy2 (both latest values of the pair form a held
# state), the pair C2 (pair_new_holder: only the holder appends at b or b.next), held2_latest_const,
# forced_wait_held2_thm (PromFreeFrom: a run restriction, not a fairness condition).
echo "building TermLiveC2.lean ..."
if ! l15c2_out=$(leanb TermLiveC2 2>&1); then
  echo "$l15c2_out"
  echo 'FAIL: TermLiveC2.lean does not compile.'
  fail=1
fi
case "$l15c2_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermLiveC2.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermLiveC2: every #print axioms theorem, std axioms only.
for thm in \
    "TermLiveC.near_next" \
    "TermLiveC.near_offs" \
    "TermLiveC.pair_overlap" \
    "TermLiveC.word_pair_excl" \
    "TermLiveC.wd2_held" \
    "TermLiveC.tstep_casp_shape" \
    "TermLiveC.pair_new_holder" \
    "TermLiveC.thread_latest_keep2" \
    "TermLiveC.heldAt2_step" \
    "TermLiveC.held2_latest_const" \
    "TermLiveC.forced_wait_held2_thm"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${l15c2_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveC2.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- TermLiveG3.lean ------------------------------------------------------------
# (item 15 C) the held branch, critical-section form: a thread crashed anywhere on a straight-line path to
# its token release store (TokPath, scope 1) or to `call f (pair mv tk)` of an unlockD-shaped f (TokPathCall,
# scope 2) is the holder, so every thread that keeps touching the word is stuck.  Seqlock, mutex and lockD/incrD
# instances.  Reachability open; cas->ret window not covered; no ticket-lock instance.
echo "building TermLiveG3.lean ..."
if ! l15g3_out=$(leanb TermLiveG3 2>&1); then
  echo "$l15g3_out"
  echo 'FAIL: TermLiveG3.lean does not compile.'
  fail=1
fi
case "$l15g3_out" in
  *"declaration uses"*|*sorryAx*|*ofReduceBool*)
    echo "FAIL: a TermLiveG3.lean theorem has a sorry or a native_decide"
    fail=1 ;;
esac
# TermLiveG3: the 5 main theorems, std axioms only.
for thm in \
    "TermLiveC.forced_wait_in_critical_section" \
    "TermLiveC.forced_wait_in_critical_section_call" \
    "TermLiveC.seqlock_forced_wait_in_critical_section" \
    "TermLiveC.mutex_forced_wait_in_critical_section" \
    "TermLiveC.mutex_incr_forced_wait_in_critical_section"; do
  thm_re=$(printf '%s' "$thm" | sed 's/[][\\.*^$?+(){}|]/\\&/g')
  if ! echo "${l15g3_out}" | grep -qE "'([^' ]*\.)?$thm_re' (depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]|does not depend on any axioms)"; then
    echo "FAIL: TermLiveG3.lean: '#print axioms $thm' missing or non-standard axioms"
    fail=1
  fi
done

# --- SceText, SceCli, SceLive, SceProof, SceRun, SceTest, tools/sce (UnElab M3a, M3b, M3d) -----------
# sce, the UnElab front end.  SceRun.run is the whole command as a pure function (imports with
# -I and .i over .u, cycles, duplicates, UDiag's diagnostics, the whole-program check, emission re-parsed and
# re-checked); SceTest runs it on an in-memory file system: every exit code and message, EM0 through
# sce to exactly the elaborated program, the .w mode, determinism.  tools/test-sce.sh runs tools/sce (Sce.lean
# under lean with libwm.so; arguments in SCE_ARGC/SCE_ARG_i) end to end.  Sce.lean is not a leanb target.
# SceLive (M3b): the live stage, mode A: each scenario's bounded search (TermLive.exploreG, analyse), its report
# (status, verdict, results, final states, each livelock kind with its threads placed in the source), and the
# --live / --live-strict / --final checks (exit 5); SceTest checks its counts and verdicts against Doc.threads.
# SceProof (M3d): the liveness instance behind `live def` (TermLiveL3's theorems under the decidable robust
# premise robustOK); sce prints it for every live def and --live-proof writes and builds it (tools/test-sce.sh
# builds one).  This step runs after TermLiveL3, which SceProof imports.
# SceCertK, SceCert (item 38): liveness certificates -- mode A (TermLiveCert.check by compiled evaluation, the
# report lines and refusals) and the texts of the root.cert/ files --live-proof writes; SceCertK holds the ToExpr
# instances and the #sce_start/#sce_cert commands those files run.  Nothing in them is trusted: the files are
# re-checked by the kernel (TermLiveCertJoin).  tools/test-sce.sh builds one certificate end to end.
echo "building SceText.lean, SceCli.lean, SceFront.lean, SceLive.lean, SceProof.lean, SceCertK.lean, SceCert.lean, SceRun.lean ..."
for m in SceText SceCli SceFront SceLive SceProof SceCertK SceCert SceRun; do
  if ! sce_out=$(leanb $m 2>&1); then
    echo "$sce_out"
    echo "FAIL: $m.lean: does not compile (or a guard failed)."
    fail=1
  elif echo "$sce_out" | grep -q "declaration uses 'sorry'"; then
    echo "FAIL: $m.lean has a sorry"
    fail=1
  fi
  if [ "$m" = SceRun ] && ! echo "$sce_out" | grep -qE "'SceRun\.scopeFail_none' depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]"; then
    echo "FAIL: SceRun.lean: '#print axioms SceRun.scopeFail_none' missing or non-standard axioms"
    fail=1
  fi
  if [ "$m" = SceFront ]; then
    for thm in rtCheck_iff Front.ok_roundTrip Front.checked_prog; do
      if ! echo "$sce_out" | grep -qE "'SceFront\.$thm' depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]"; then
        echo "FAIL: SceFront.lean: '#print axioms SceFront.$thm' missing or non-standard axioms"
        fail=1
      fi
    done
  fi
  if [ "$m" = SceProof ]; then
    for thm in progRobustPwf_of_robustOK firstBad_none mainInst scenInst; do
      if ! echo "$sce_out" | grep -qE "'SceProof\.$thm' depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]"; then
        echo "FAIL: SceProof.lean: '#print axioms SceProof.$thm' missing or non-standard axioms"
        fail=1
      fi
    done
  fi
done
echo "building SceTest.lean ..."
if ! scet_out=$(leanr SceTest.lean 2>&1); then
  echo "$scet_out"
  echo 'FAIL: SceTest.lean: an sce guard failed.'
  fail=1
fi
echo "running tools/test-sce.sh ..."
if ! tsce_out=$(WM_BUILD="$BUILD" WM_LEAN="$LEAN" tools/test-sce.sh 2>&1); then
  echo "$tsce_out"
  echo 'FAIL: tools/test-sce.sh'
  fail=1
else
  echo "$tsce_out" | tail -1
fi
echo "cldoc cert: not part of this distribution"

# Premise-meaning guard: the transitive definition closure of every
# user-facing final's statement (premises and conclusion: InitOK, ObligationsF,
# InitShape, StartOK, KidOK, ...) is pretty-printed and hashed against
# tools/premises/premises.md5.  A proof-side change that alters what a final
# MEANS (e.g. a new conjunct in a definition InitOK unfolds to) fails the gate
# unless WM_APPROVE_PREMISES names the approval entry, which re-freezes the
# baseline and logs it in tools/premises/approvals.log.
echo "checking the meaning of the finals' premises ..."
if ! prem_out=$(WM_BUILD="$BUILD" WM_LEAN="$LEAN" tools/premises/guard.sh 2>&1); then
  echo "FAIL: premise-meaning guard:"
  echo "$prem_out" | sed 's/^/      /'
  fail=1
else
  echo "$prem_out" | tail -1
fi

if [ "$fail" -ne 0 ]; then
  exit 1
fi

echo "OK"
