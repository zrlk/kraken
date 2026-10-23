/-
Observable events, outcomes, address ranges and labelled runs for the `scc`
correctness statement.

Nothing here depends on Kraken or WeakCore: both the target interface
(`Scc/Sem/Ext.lean`) and the source interface (`Scc/Sem/SrcExt.lean`) emit
the same events, and `Scc/Sem/Correct.lean` compares their traces.

- `Ev`: one event. A byte written to standard output (one event per byte, so
  that a partial `write` is a trace prefix), the process exit with its code
  modulo 256, a `write` the kernel refused, or the distinguished abort
  outcome with its kind (`AbortKind`).
- `Outcome`: how a configuration has terminated, if it has.
- `Range`: a half-open range of addresses `[lo, lo + size)`, as natural
  numbers below `2^64`.
- `LRun step`: runs of a labelled step relation, concatenating the labels.
-/

namespace Scc.Sem

/-! ## Events and outcomes -/

/-- Why the target aborted. Each kind has its own abort stub in the text
(labelled `Layout.abortLbl k`), so the model can tell them apart; on the host all exit
with status 101. -/
inductive AbortKind where
  /-- A plain `Int` `+` whose result does not fit in 64 bits. -/
  | overflow
  /-- The heap arena is exhausted. -/
  | heap
  /-- A thread's stack would exceed its cap. -/
  | stack
  /-- No thread slot is left for a spawn, or the kernel refused a
  `clone`. -/
  | threads
  /-- The kernel refused a `write`. -/
  | writeErr
  deriving DecidableEq, Repr

/-- An index for each kind. -/
def AbortKind.idx : AbortKind → Nat
  | .overflow => 0 | .heap => 1 | .stack => 2 | .threads => 3 | .writeErr => 4

theorem AbortKind.idx_inj {k k' : AbortKind} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> simp_all [AbortKind.idx]

theorem AbortKind.idx_lt (k : AbortKind) : k.idx < 5 := by
  cases k <;> simp [AbortKind.idx]

/-- **A stack-range transfer site** (`Scc/DESIGN.md` §2.6): a `nop` of the
runtime, at a fixed label (`XferKind.label`), at which the thread's first two
argument registers hold the base and the size of a stack-pool range. The
extended machine takes the transfer there in place of the `nop`
(`ExtMachine.Step.xfer`).

* `take`: the range moves from the pool into the thread's private memory
  (in the runtime's `scc_rt_stack_take`, after the range is chosen).
* `release`: the range moves from the thread's private memory back to the
  pool (at the entry of the runtime's `scc_rt_stack_release`). -/
inductive XferKind where
  | take
  | release
  deriving DecidableEq, Repr

/-- The label of the transfer site of each kind: names shared by the runtime
and the statement (fixed here, not chosen by a certificate). -/
def XferKind.label : XferKind → String
  | .take => "scc_rt_take_site"
  | .release => "scc_rt_release_site"

/-- An event.

* `out b`: the byte `b` was written to file descriptor 1. A `write` that
  transfers `n` bytes emits `n` events, in order.
* `exit code`: the process exited (`exit_group`) with status `code`; the
  source's exit value `v` appears as `v % 256`.
* `writeErr`: a `write` returned 0 or an error other than `EINTR`/`EAGAIN`
  (an event of the environment, recorded so that an abort of kind
  `writeErr` can be justified by it).
* `cloneErr`: a `clone` returned an error (`EAGAIN`, `ENOMEM`): Linux may
  refuse a thread below any limit the program can see (an event of the
  environment, recorded so that an abort of kind `threads` can be
  justified by it).
* `abort k`: the distinguished abort outcome of kind `k`. On the host it is
  exit status 101 after a message on file descriptor 2; the model keeps it
  apart from a program's own `exit 101`. Bytes written to file descriptor 2
  are not events. -/
inductive Ev where
  | out (b : Fin 256)
  | exit (code : Fin 256)
  | writeErr
  | cloneErr
  | abort (k : AbortKind)
  deriving DecidableEq, Repr

/-- The events a source run must reproduce: output bytes and the exit. -/
def Ev.isObs : Ev → Bool
  | .out _ | .exit _ => true
  | .writeErr | .cloneErr | .abort _ => false

/-- The events of a trace that a source run must reproduce: everything but
`writeErr`, `cloneErr` and `abort`, which have no source counterpart. -/
def obs (tr : List Ev) : List Ev := tr.filter Ev.isObs

@[simp] theorem obs_nil : obs [] = [] := rfl

/-- How a configuration has terminated.

* `exit code`, `abort k`: as the events of the same name.
* `halted`: every thread has run off its text with no outstanding promise and
  no exit call was made. This is the only termination of the existing Kraken
  machine (`Config.final`); the extended machine's `fault` makes it a fault
  for an `scc` program, whose threads always end by a system call. -/
inductive Outcome where
  | exit (code : Fin 256)
  | abort (k : AbortKind)
  | halted
  deriving DecidableEq, Repr

/-! ## Address ranges -/

/-- The addresses `[lo, lo + size)`. -/
structure Range where
  lo : Nat
  size : Nat
  deriving DecidableEq, Repr

namespace Range

/-- `a` is in the range. -/
def contains (r : Range) (a : Nat) : Prop := r.lo ≤ a ∧ a < r.lo + r.size

instance (r : Range) (a : Nat) : Decidable (r.contains a) := by
  unfold contains; infer_instance

/-- The range lies in the 64-bit address space and does not contain address
0 (which represents `null`). -/
def InSpace (r : Range) : Prop := 0 < r.lo ∧ r.lo + r.size ≤ 2 ^ 64

/-- The two ranges share no address. -/
def Disjoint (r s : Range) : Prop := r.lo + r.size ≤ s.lo ∨ s.lo + s.size ≤ r.lo

/-- Every address of `r` is in `s`. -/
def Sub (r s : Range) : Prop := s.lo ≤ r.lo ∧ r.lo + r.size ≤ s.lo + s.size

/-- The range starts at a multiple of `k`. -/
def Aligned (r : Range) (k : Nat) : Prop := r.lo % k = 0

theorem Disjoint.not_both {r s : Range} (h : r.Disjoint s) {a : Nat} (hr : r.contains a)
    (hs : s.contains a) : False := by
  unfold Disjoint at h; unfold contains at hr hs; omega

end Range

/-! ## Labelled runs -/

/-- Runs of a labelled step relation; the run's label is the concatenation of
its steps' labels. -/
inductive LRun {C : Type} (step : C → List Ev → C → Prop) : C → List Ev → C → Prop
  | refl (c : C) : LRun step c [] c
  | step {c c' c'' : C} {es tr : List Ev} : step c es c' → LRun step c' tr c'' →
      LRun step c (es ++ tr) c''

namespace LRun

variable {C : Type} {step : C → List Ev → C → Prop}

/-- A run of a relation with no steps from `c` is the empty run. -/
theorem eq_refl_of_stuck {c c' : C} {tr : List Ev} (h : LRun step c tr c')
    (hs : ∀ es c'', ¬ step c es c'') : tr = [] ∧ c' = c := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step h1 _ => exact absurd h1 (hs _ _)

/-- Runs compose. -/
theorem trans {c c' c'' : C} {tr tr' : List Ev} (h : LRun step c tr c') (h' : LRun step c' tr' c'') :
    LRun step c (tr ++ tr') c'' := by
  induction h with
  | refl => exact h'
  | step hs _ ih => rw [List.append_assoc]; exact .step hs (ih h')

/-- Monotonicity in the step relation. -/
theorem mono {step' : C → List Ev → C → Prop} (hm : ∀ c es c', step c es c' → step' c es c')
    {c c' : C} {tr : List Ev} (h : LRun step c tr c') : LRun step' c tr c' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (hm _ _ _ hs) ih

end LRun

end Scc.Sem
