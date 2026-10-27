/-
Evidence for the known holes of the `scc` correctness statement.

Each item is a compilation (or a relation `R`) that the statement of
`Scc/Sem/Correct.lean` should reject: a `hole_` theorem shows it is still
accepted, a `not_` theorem that the statement now rejects it. They
use toy instances in the style of `oneShot`: a scripted source (`script`,
configurations are program points, every step by thread 0, a chosen event
list and core configuration per point) and toy targets with at most one
Kraken thread, which never takes an instruction step, and whose system calls
are free fields. The holes are in the clauses,
not in the instances: the instances give the fields only the meaning their
docstrings state.

* `not_correct_early_abort` (P1, fixed): the source prints a
  byte and then exceeds the heap budget; a target that aborts at once,
  printing nothing, is rejected, since the justifying source configuration
  must have exactly the target's observable trace.
* `not_correct_silent_exit` (P2, fixed): a target whose only thread exits
  with no event, leaving no live thread and no exit outcome, is rejected by
  `Progress`.
* `not_components_skipped_store` (P3, fixed): for a source that stores `1`
  and then `0` to a cell that a variable the thread still reads points to
  (`skipSrcL`, the cell live), no witness makes `Components` hold of a
  target memory with only the store of `1` (only a first message may map to
  the initial write); `components_both_stores`, `components_live_stores`:
  the faithful target passes. `components_skipped_store_dead` (accepted by
  design): with no reference to the cell left, its label is dead, its
  memory runtime-owned, and the skipped store is admitted.
* `not_components_live_write` (memory scoped to live labels): a target
  write into a live label's range with no source message (`storeL`,
  `healMem`) is rejected: after the label's target epoch by `mem_onto`,
  since without colour bits (`colourMask = 0`) no write is colour-only; at
  or before it by `pre_alloc`, since the write is no thread's outstanding
  promise. Writes to recycled memory before an allocation are exempt only
  as outstanding promises. `not_components_live_write_tsFrom_last`: the
  same holds for a witness with `tsFrom` at the last timestamp (the
  never-mirror choice), which exempts outstanding promises only.
* `not_components_fulfilled_no_preimage` (`pre_alloc`): the same write is
  rejected when its writer has another promise outstanding but not this one:
  a fulfilled promise must gain a preimage.
* `not_components_empty_env` (P4, fixed): a variable the thread still reads
  must be placed (`env_total`), so on a target whose registers all hold 7 no
  witness gives `Components` while the variable holds 5;
  `components_env_placed`: placed in a register holding 5, it passes.
* `not_components_imm_table` (live immediate constants, `Layout.imms`,
  `env_imm`): a word at an immediate must be the constant the layout's
  immediate table names for its variable at its frame's control point, so
  a table naming another constant (`not_components_imm_wrong`) or another
  variable (`not_components_imm_wrong_var`) is rejected, as is any
  immediate with the empty table (P4 above); `components_env_imm`: the
  constant the table names passes, whatever the registers hold.
* `not_components_cas_fail` (`exprFv` as WeakCore's `freeB`): the outer
  variable a `cas` failure branch reads must be placed; formerly `exprFv`
  removed `cas`'s result name from both branches.
* `not_components_loc_interior`, `not_components_loc_wrong_label`
  (`WordPlace.loc`, `LocRep`): a locative `b[1]` kept as the pair (base,
  offset word) must have the label's base in the base half, so the interior
  address `b + 8` or another object's base is rejected, whatever the offset
  word; `components_loc_base_off`: `(b, 8)` passes.
* `not_correct_load_none` (P7, fixed): a target whose loader refuses is
  rejected, `start` being unconditional.
* `not_correct_sym_in_code`, `not_correct_sym_dup` (`Layout.WF` on
  `symbols`): a layout with a data symbol on the text image, or two symbols
  of one name, is not well formed, so nothing is `Correct` with it;
  `symbols_wf`: symbols in the data, heap, pool and pinned regions pass.
* `not_inLayout_rodata_msg` (`InLayout`, messages): a store to the read-only
  image `rodata` is outside the layout; `inLayout_rodata_init`: a `.rodata`
  initial word, as the loaders lay it out, is inside it (formerly every
  initial word had to be shared, so no text with a `.rodata` was `Correct`).
* `not_correct_wrong_exit`, `not_correct_wrong_store` (P10): a target that
  exits with another code, or stores another value and prints it, is
  rejected by the simulation clause (its trace is no source trace's prefix).
* `not_correct_event_after_exit` (P9, gate on `main`'s exit): for every
  program and every source hook whose event list only grows, a target with
  an event after its exit (`[exit 0, exit 0]`) is rejected; without the gate
  a hook emitting after `main`'s return gives the source that trace.
* `correct_justified_abort` (P1 with `Layout.abortLbl`, accepted): the
  clauses still admit a justified abort. A target that prints the byte and
  then aborts with kind `heap`, at the resolved site of `abortLbl .heap`, is
  `Correct` for a source that prints it and then crosses the heap budget.

Each `not_` lemma was first an accepted hole against the earlier statement;
dropping the clause it relies on turns it back into one.
-/
import Scc.Sem.Correct

namespace Scc.Sem.Holes

open Kraken.Promising

/-! ## Toy instances -/

/-- **A scripted source**: configuration `n` is the program point after `n`
steps, all taken by thread 0; step `n` emits `evs[n]`; `core n` is the core
configuration at point `n`. -/
abbrev script (core : Nat → TermRun.Cfg) (evs : List (List Ev)) : SrcSem where
  Cfg := Nat
  core := core
  init := (· = 0)
  step i n es n' := i = 0 ∧ n' = n + 1 ∧ evs[n]? = some es

theorem script_step {core : Nat → TermRun.Cfg} {evs : List (List Ev)} {n : Nat} {es : List Ev}
    (h : evs[n]? = some es) : (script core evs).step 0 n es (n + 1) :=
  ⟨rfl, rfl, h⟩

/-- A run of a scripted source from point `m` either stays there or starts
with the events of step `m`. -/
theorem script_run {core : Nat → TermRun.Cfg} {evs : List (List Ev)} {m n : Nat} {tr : List Ev}
    (h : (script core evs).Run m tr n) : m = n ∨ ∃ es, evs[m]? = some es ∧ es <+: tr := by
  induction h with
  | refl => exact .inl rfl
  | step hs _ _ =>
    obtain ⟨_, -, -, he⟩ := hs
    exact .inr ⟨_, he, List.prefix_append _ _⟩

/-- The trace of a run of a scripted source from point `m` is a prefix of the
events of the steps from `m` on. -/
theorem script_trace {core : Nat → TermRun.Cfg} {evs : List (List Ev)} {m n : Nat} {tr : List Ev}
    (h : (script core evs).Run m tr n) : tr <+: (evs.drop m).flatten := by
  induction h with
  | refl => exact List.nil_prefix
  | step hs _ ih =>
    obtain ⟨_, _, rfl, he⟩ := hs
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp he
    rw [List.drop_eq_getElem_cons hlt, List.flatten_cons]
    exact (List.prefix_append_right_inj _).mpr ih

/-- The witness that maps source thread 0 to target thread `j`, with every
other map empty. -/
def wThr (M : ExtMachine) (j : Nat) : Witness M :=
  { Witness.empty M with thr := fun i => if i = 0 then some j else none }

/-- The components hold of `wThr`, the empty source configuration, and a
target configuration with no threads, no shared writes and no stack ranges,
under a layout with no static data. -/
theorem components_wThr (M : ExtMachine) (Λ : Layout) (j : Nat) (t : M.Cfg) (ht : t.1.threads = #[])
    (hm : t.1.mem.msgs = #[]) (hs : ∀ j, M.stackRange t j = none) (hst : ∀ l, Λ.static l = none) :
    Components M Λ (wThr M j) t emptyCfg := by
  refine ComponentsAll.scoped ?_ (fun _ => rfl) (fun _ => rfl)
  constructor <;> simp [wThr, Witness.empty, emptyCfg, ht, hm, hs, hst, Kraken.Promising.Memory.get?]

section Toy

variable (I : ISA) (A : Arch)

/-! ## P1: early aborts -/

/-- A source configuration with one allocated word: heap use 1. -/
def oneCell : TermRun.Cfg := { mem := #[⟨⟨0, 0⟩, .num 0, 0⟩], ths := #[] }

/-- The core configurations of `earlySrc`: empty before the allocation,
`oneCell` after it. -/
def earlyCore (n : Nat) : TermRun.Cfg := if n < 2 then emptyCfg else oneCell

/-- The source `print b; allocate a word`: step 0 prints `b`, step 1
allocates (and, with no heap budget, leaves it). -/
abbrev earlySrc (b : Fin 256) : SrcSem := script earlyCore [[.out b], []]

/-- The budget with no heap words, no threads and no frames. -/
def noBudget : Budget := ⟨0, 0, 0⟩

theorem heapUse_emptyCfg : heapUse emptyCfg = 0 := by decide

theorem heapUse_oneCell : heapUse oneCell = 1 := by decide

/-- **Rejected (P1): an early abort.** The source prints `b`
and then exceeds the heap budget. A target that aborts with kind `heap` at
once, without printing, is not `Correct`: the abort must be justified at a
source configuration reached with the target's observable trace `[]`, which
is the start, where the next step (the print) crosses no budget part. -/
theorem not_correct_early_abort (b : Fin 256) (st : I.State) :
    ¬ Correct (oneShot I A (.abort .heap) st) (earlySrc b) trivLayout noBudget () := by
  rintro ⟨h⟩
  obtain ⟨s, w, i, ⟨s0, hs0, hr⟩, -, -, -, hj⟩ := h.abort _ [] _ 0 [.abort .heap]
    (Config.init [st] [], true) .heap rfl (.refl _)
    (.sys ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by simp) (oneShot_abort_at I A (.abort .heap) st) (by simp)) (by simp)
  change s0 = 0 at hs0
  subst hs0
  rcases script_run hr with rfl | ⟨es, he, hp⟩
  · obtain ⟨es, s', ⟨-, rfl, -⟩, -, hnot⟩ := hj
    exact hnot (by show heapUse (earlyCore (0 + 1)) ≤ 0; simp [earlyCore, heapUse_emptyCfg])
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    simp [obs] at hp

/-! ## P2: silent exits -/

/-- A toy target with one notional thread (0) that exits by a system call
with no event: afterwards no thread is live and the process has no exit
outcome. -/
def silentExit : Target where
  M := {
    I := I, A := A, X := Bool
    runs := fun c tid => c.2 = false ∧ tid = 0
    atSys := fun _ _ => True
    spawn := fun _ _ _ _ => False
    sys := fun _ _ c es c' => c.2 = false ∧ es = [] ∧ c' = (c.1, true)
    xfer := fun _ _ _ _ => False
    live := fun c tid => c.2 = false ∧ tid = 0
    exited := fun _ => none
    fault := fun _ => False
    regVal := fun _ _ => 0
    privLoad := fun _ _ => none
    stackRange := fun _ _ => none
    pc := fun _ => 0 }
  Asm := Unit
  load _ _ := some (Config.init [] [], false)
  resolve _ _ _ := none

/-- The source `print b; exit 0`. -/
abbrev printSrc (b : Fin 256) : SrcSem := script (fun _ => emptyCfg) [[.out b], [.exit 0]]

/-- **Rejected (P2): a silent exit.** The target's only thread
exits with no event; then no thread is live and `exited` is `none`, which
`Progress` rejects (some thread must be live, or the process must have
terminated). So the target is not `Correct` for a source that prints `b` and
exits with 0 (for any source, in fact). -/
theorem not_correct_silent_exit (b : Fin 256) :
    ¬ Correct (silentExit I A) (printSrc b) trivLayout noBudget () := by
  rintro ⟨h⟩
  obtain ⟨⟨-, hp⟩, -⟩ := h.progress _ [] (Config.init [] [], true) rfl
    (LRun.step (es := []) (tr := []) ⟨0, .sys ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by simp) (by simp) (by simp)⟩ (.refl _))
  rcases hp with hp | ⟨⟨tid, hl, -⟩, -⟩
  · simp [silentExit] at hp
  · simp at hl

/-! ## P7: conditional start -/

/-- **Rejected (P7): a refusing loader.** A target whose loader
refuses every text is not `Correct`, whatever the source: `start` is
unconditional. (With `start` conditional on `RouteS`, a layout whose image
matched no source start made every clause vacuous.) -/
theorem not_correct_load_none (st : I.State) (S : SrcSem) (Λ : Layout) (B : Budget) :
    ¬ Correct { oneShot I A (.out 0) st with load := fun _ _ => none } S Λ B () := by
  rintro ⟨h⟩
  obtain ⟨t0, -, h0, -⟩ := h.start
  cases h0

/-! ## Data symbols in the layout -/

/-- `trivLayout` with a data symbol at 16, the first byte of its code. -/
def symInCode : Layout := { trivLayout with symbols := [("val", 16)] }

/-- **Rejected (`Layout.WF.symIn`, `symAbove`): a data symbol inside the
code.** A layout that places a data symbol on the text image is not
well formed, so no target is `Correct` with it, whatever the source and the
budget: a reference to the symbol would read or write the code. -/
theorem not_correct_sym_in_code (T : Target) (S : SrcSem) (B : Budget) (asm : T.Asm) :
    ¬ Correct T S symInCode B asm := by
  rintro ⟨h⟩
  have := h.layout.symAbove ("val", 16) (by simp [symInCode])
  simp [symInCode, trivLayout] at this

/-- **Rejected (`Layout.WF.symNodup`): two data symbols with one name.** -/
theorem not_correct_sym_dup (T : Target) (S : SrcSem) (B : Budget) (asm : T.Asm) :
    ¬ Correct T S { trivLayout with symbols := [("val", 48), ("val", 56)] } B asm := by
  rintro ⟨h⟩
  have := h.layout.symNodup
  simp at this

/-- **Accepted: data symbols in the data, heap, pool and pinned regions.** -/
theorem symbols_wf :
    ({ trivLayout with symbols := [("val", 48), ("heap", 64), ("pool", 80), ("tcbs", 96)] } : Layout).WF :=
  { trivLayout_wf with
    symIn := by simp [Layout.dataRegion, Range.contains, trivLayout]
    symAbove := by simp [trivLayout]
    symNodup := by simp }

/-! ## Initial words in the read-only image -/

/-- `trivLayout` with a read-only image at `[112, 128)`, clear of every
region. -/
def roLayout : Layout := { trivLayout with rodata := ⟨112, 16⟩ }

/-- **Accepted (`InLayout`'s initial words): a `.rodata` word.** A target
configuration whose initial memory is a word of the read-only image (as the
loaders lay `.rodata` out, `rodataWords`) and which has written nothing is
inside the layout. -/
theorem inLayout_rodata_init (M : ExtMachine) (t : M.Cfg) (ht : t.1.mem = ⟨[(⟨112, 8⟩, 0)], #[]⟩) :
    InLayout roLayout t := by
  rw [InLayout, ht]
  refine ⟨by simp, fun p hp => ?_⟩
  simp only [List.mem_singleton] at hp
  subst hp
  right; simp [roLayout, Range.contains]

/-- **Rejected (`InLayout`'s messages): a write to the read-only image.**
A target configuration with a message (a store) at a word of `rodata` is
outside the layout, whatever its initial memory: `rodata` is not shared. -/
theorem not_inLayout_rodata_msg (M : ExtMachine) (t : M.Cfg) (m : Msg) (hm : m ∈ t.1.mem.msgs.toList)
    (ha : m.loc.addr = 112) : ¬ InLayout roLayout t := by
  rintro ⟨h, -⟩
  have := h m hm
  rw [ha] at this
  simp [Layout.shared, roLayout, trivLayout, Range.contains] at this

/-- **Rejected (`InLayout`'s initial words): an initial word outside both
`shared` and `rodata`.** Admitting the read-only image does not admit any
initial word: one on the code (at 16) is outside the layout. -/
theorem not_inLayout_init_code (M : ExtMachine) (t : M.Cfg) (ht : t.1.mem = ⟨[(⟨16, 8⟩, 0)], #[]⟩) :
    ¬ InLayout roLayout t := by
  rw [InLayout, ht]
  rintro ⟨-, h⟩
  have := h _ (List.mem_singleton.mpr rfl)
  simp [Layout.shared, roLayout, trivLayout, Range.contains] at this

/-! ## P10: wrong observable results -/

/-- `oneShot` resolving no label, so that its event may be an exit (an exit
is never at a resolved abort site). -/
def oneShotX (e : Ev) (st : I.State) : Target := { oneShot I A e st with resolve := fun _ _ _ => none }

/-- **Rejected (P10): a wrong exit code.** The source exits with
3; a target that exits with 4 is not `Correct`: its trace `[exit 4]` is a
prefix of no source trace (`[]` or `[exit 3]`). -/
theorem not_correct_wrong_exit (st : I.State) :
    ¬ Correct (oneShotX I A (.exit 4) st) (script (fun _ => emptyCfg) [[.exit 3]]) trivLayout noBudget () := by
  rintro ⟨h⟩
  obtain ⟨tr', s, ⟨s0, hs0, hr⟩, -, hp⟩ := h.sim _ [.exit 4] _ rfl
    (LRun.step (es := [.exit 4]) (tr := []) ⟨0, .sys ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by simp) (by simp)
      (fun _ _ _ _ h => by simp [Target.marks, oneShotX] at h)⟩ (.refl _))
  change s0 = 0 at hs0
  subst hs0
  have := hp.trans (script_trace hr)
  simp [obs, List.filter_cons, Ev.isObs] at this

/-- A toy target with one thread in state `st`, always at a system call,
resolving no label: its first system call stores `v` to the word at 64 (a
shared message), its second prints `v`. -/
@[reducible] def storePrint (v : Fin 256) (st : I.State) : Target where
  M := {
    I := I, A := A, X := Nat
    runs := fun c tid => c.2 < 2 ∧ tid = 0
    atSys := fun _ _ => True
    spawn := fun _ _ _ _ => False
    sys := fun _ _ c es c' =>
      (c.2 = 0 ∧ es = [] ∧
        c' = ({ c.1 with mem := { c.1.mem with msgs := c.1.mem.msgs.push ⟨wordLoc 64, BitVec.ofNat _ v.val, 0⟩ } }, 1)) ∨
      (c.2 = 1 ∧ es = [.out v] ∧ c' = (c.1, 2))
    xfer := fun _ _ _ _ => False
    live := fun c tid => c.2 < 2 ∧ tid = 0
    exited := fun _ => none
    fault := fun _ => False
    regVal := fun _ _ => 0
    privLoad := fun _ _ => none
    stackRange := fun _ _ => none
    pc := fun _ => 0 }
  Asm := Unit
  load _ _ := some (Config.init [st] [], 0)
  resolve _ _ _ := none

/-- The core configurations of `storeSrc`: a freshly allocated cell `x`
(label 0) holding 0, then also the store of 1. -/
def storeCore : Nat → TermRun.Cfg
  | 0 => oneCell
  | _ => { mem := #[⟨⟨0, 0⟩, .num 0, 0⟩, ⟨⟨0, 0⟩, .num 1, 0⟩], ths := #[] }

/-- The source `x := 1; print x`: step 0 stores 1 (no event), step 1 prints
the value read back, 1. -/
abbrev storeSrc : SrcSem := script storeCore [[], [.out 1]]

/-- **Rejected (P10): a wrong stored value, made observable.**
The source stores 1 and prints it; a target that stores 2 and prints it is
not `Correct`: after its two steps its trace is `[out 2]`, a prefix of no
source trace (`[]` or `[out 1]`). (Before the print, the components of `R`
already reject such a store: `not_components_skipped_store`.) -/
theorem not_correct_wrong_store (st : I.State) :
    ¬ Correct (storePrint I A 2 st) storeSrc trivLayout noBudget () := by
  rintro ⟨h⟩
  obtain ⟨tr', s, ⟨s0, hs0, hr⟩, -, hp⟩ := h.sim _ [.out 2] _ rfl
    (LRun.step (es := []) (tr := [.out 2]) ⟨0, .sys ⟨by simp, rfl⟩ (.inl ⟨rfl, rfl, rfl⟩) (by simp) (by simp)
        (by simp)⟩
      (LRun.step (es := [.out 2]) (tr := []) ⟨0, .sys ⟨by simp, rfl⟩ (.inr ⟨rfl, rfl, rfl⟩) (by simp) (by simp) (by simp)⟩
        (.refl _)))
  change s0 = 0 at hs0
  subst hs0
  have := hp.trans (script_trace hr)
  simp [obs, List.filter_cons, Ev.isObs] at this

/-! ## P9: events after `main`'s exit -/

/-- A toy target with one thread in state `st`, always at a system call,
resolving no label: its first system call exits with 0, its second (an
event after the exit) exits with 0 again. -/
@[reducible] def exitTwice (st : I.State) : Target where
  M := {
    I := I, A := A, X := Nat
    runs := fun c tid => c.2 < 2 ∧ tid = 0
    atSys := fun _ _ => True
    spawn := fun _ _ _ _ => False
    sys := fun _ _ c es c' => (c.2 = 0 ∧ es = [.exit 0] ∧ c' = (c.1, 1)) ∨ (c.2 = 1 ∧ es = [.exit 0] ∧ c' = (c.1, 2))
    xfer := fun _ _ _ _ => False
    live := fun c tid => c.2 < 2 ∧ tid = 0
    exited := fun _ => none
    fault := fun _ => False
    regVal := fun _ _ => 0
    privLoad := fun _ _ => none
    stackRange := fun _ _ => none
    pc := fun _ => 0 }
  Asm := Unit
  load _ _ := some (Config.init [st] [], 0)
  resolve _ _ _ := none

/-- **Rejected (P9): an event after `main`'s exit.** For every
program `p` and every source hook whose event list only grows along the
steps and is empty at the start, a target with trace `[exit 0, exit 0]` is
not `Correct` for `SrcSem.source P p`: the trace of a source run is the
growth of `srcObs` (`source_run_trace`), which is cut at its first exit
(`cutAtExit_exit_last`), so no source trace has an event after an exit.

Without the gate on `main` having returned, `source_run_trace` fails for a
hook whose thread 1 can still emit `out 1` after `main` has returned: that
step takes `srcObs` from `[exit 0]` to `[out 1, exit 0]` and is labelled
with the growth past the old length, `[exit 0]`, so that source has the
trace `[exit 0, exit 0]`, and this target would no longer be refuted by its
trace. The gate is vacuous on programs (it restricts configurations, not
which programs compile); this target is the compilation it rules out. -/
theorem not_correct_event_after_exit (st : I.State) (P : SrcSem.SrcParams) (p : CoreTerm.Prog)
    (hinit : ∀ c, P.init c → SrcSem.srcObs P.hooks.trace c = [])
    (hgrow : ∀ i c c', SrcSem.StepBy p P.k P.arch i c c' ∨ SrcSem.SpawnBy P.cap i c c' ∨ P.hooks.ext i c c' →
      P.hooks.trace c <+: P.hooks.trace c') :
    ¬ Correct (exitTwice I A st) (SrcSem.source P p) trivLayout noBudget () := by
  rintro ⟨h⟩
  obtain ⟨tr', s, ⟨s0, hs0, hr⟩, -, hp⟩ := h.sim _ [.exit 0, .exit 0] _ rfl
    (LRun.step (es := [.exit 0]) (tr := [.exit 0]) ⟨0, .sys ⟨by simp, rfl⟩ (.inl ⟨rfl, rfl, rfl⟩) (by simp)
        (by simp) (fun _ _ _ _ h => by simp [Target.marks] at h)⟩
      (LRun.step (es := [.exit 0]) (tr := []) ⟨0, .sys ⟨by simp, rfl⟩ (.inr ⟨rfl, rfl, rfl⟩) (by simp) (by simp)
        (fun _ _ _ _ h => by simp [Target.marks] at h)⟩ (.refl _)))
  have ht := SrcSem.source_run_trace hgrow hr
  rw [hinit _ hs0, List.nil_append] at ht
  obtain ⟨d, rfl⟩ := hp
  have he : obs [.exit 0, .exit 0] ++ d = [] ++ .exit 0 :: (.exit 0 :: d) := by
    simp [obs, List.filter_cons, Ev.isObs]
  rw [he] at ht
  exact absurd (SrcSem.cutAtExit_exit_last ht) (by simp)

/-! ## A justified abort -/

/-- A finished source thread (`ret ()`), with no variables. -/
def doneTh : TermRun.TTh := { term := .ret .unit, env := [] }

/-- One source thread, `doneTh`, and no memory. -/
def doneCfg : TermRun.Cfg := { mem := #[], ths := #[doneTh] }

/-- `doneCfg` with one allocated word: heap use 1. -/
def doneCell : TermRun.Cfg := { mem := #[⟨⟨0, 0⟩, .num 0, 0⟩], ths := #[doneTh] }

theorem heapUse_doneCfg : heapUse doneCfg = 0 := by decide

theorem heapUse_doneCell : heapUse doneCell = 1 := by decide

/-- The core configurations of `abortSrc`: `doneCfg` before the allocation,
`doneCell` after it. -/
def abortCore : Nat → TermRun.Cfg
  | 0 | 1 => doneCfg
  | _ => doneCell

/-- The source `print b; allocate a word`, by its one thread: step 0 prints
`b`, step 1 allocates (and, with no heap budget, crosses it). -/
abbrev abortSrc (b : Fin 256) : SrcSem := script abortCore [[.out b], []]

/-- The components hold of `wThr` (source thread 0 to target thread 0),
`doneCfg`, and a target configuration with one thread, no memory and no
stack ranges, under `trivLayout`. -/
theorem components_doneCfg (M : ExtMachine) (st : M.I.State) (x : M.X)
    (hs : ∀ j, M.stackRange (Config.init [st] [], x) j = none) :
    Components M trivLayout (wThr M 0) (Config.init [st] [], x) doneCfg := by
  refine ComponentsAll.scoped ?_ (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i hi
    simp [doneCfg] at hi
    subst hi
    simp [wThr, Config.init]
  · intro i i' j h h'
    simp only [wThr] at h h'
    split at h <;> split at h' <;> simp_all
  · intro j tt _ h
    have : j = 0 := by
      have := (Array.getElem?_eq_some_iff.mp h).1
      simp [Config.init] at this
      omega
    subst this
    exact ⟨0, by simp [doneCfg], by simp [wThr]⟩
  · simp [trivLayout]
  · simp [wThr, Witness.empty]
  · simp [wThr, Witness.empty]
  · simp [doneCfg]
  · simp [doneCfg]
  · simp [doneCfg]
  · simp [wThr, Witness.empty]
  · simp [wThr, Witness.empty]
  · simp [wThr, Witness.empty]
  · intro i th hth d e xs he hxs _hxf y hy
    have hi : i = 0 := by
      have := (Array.getElem?_eq_some_iff.mp hth).1
      simp [doneCfg] at this
      omega
    subst hi
    simp [doneCfg] at hth
    subst hth
    rcases d with _ | d <;> simp [frameFv, doneTh, exprFv, atVars] at hxs
    subst hxs
    simp at hy
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [wThr, Witness.empty]
  · simp [wThr, Witness.empty]
  · intro _ _ _ _ _ _ _ _ _ h
    simp only [wThr, Witness.empty] at h
    repeat' split at h
    all_goals simp_all

/-- A toy target with one thread in state `st`, always at a system call at
pc 7, which is the resolved site of the heap abort stub (`Λ.abortLbl .heap`
resolves to 7, no other label resolves): its first system call prints `b`
(phase 0 to 1), its second aborts with kind `heap` (phase 1 to 2), after
which the process has terminated with that outcome. -/
@[reducible] def printAbort (b : Fin 256) (st : I.State) : Target where
  M := {
    I := I, A := A, X := Nat
    runs := fun c tid => c.2 < 2 ∧ tid = 0
    atSys := fun _ _ => True
    spawn := fun _ _ _ _ => False
    sys := fun _ _ c es c' => (c.2 = 0 ∧ es = [.out b] ∧ c' = (c.1, 1)) ∨
      (c.2 = 1 ∧ es = [.abort .heap] ∧ c' = (c.1, 2))
    xfer := fun _ _ _ _ => False
    live := fun c tid => c.2 < 2 ∧ tid = 0
    exited := fun c => if c.2 = 2 then some (.abort .heap) else none
    fault := fun _ => False
    regVal := fun _ _ => 0
    privLoad := fun _ _ => none
    stackRange := fun _ _ => none
    pc := fun _ => 7 }
  Asm := Unit
  load _ _ := some (Config.init [st] [], 0)
  resolve _ Λ l := if l = Λ.abortLbl .heap then some 7 else none

/-- Every step of `printAbort` is one of its two system calls. -/
theorem printAbort_step {b : Fin 256} {st : I.State} {μ : Marks} {tid : Nat}
    {c c' : (printAbort I A b st).M.Cfg} {es : List Ev} (h : (printAbort I A b st).M.Step μ tid c es c') :
    ((c.2 : Nat) = 0 ∧ es = [.out b] ∧ c' = (c.1, (1 : Nat))) ∨
      ((c.2 : Nat) = 1 ∧ es = [.abort .heap] ∧ c' = (c.1, (2 : Nat))) := by
  cases h with
  | instr _ ha _ => exact absurd trivial ha
  | spawn _ h => exact h.elim
  | sys _ h _ _ _ => exact h
  | xfer _ _ _ h => exact h.elim

/-- The configurations of `printAbort` from its loaded one, with their
traces: phase 0 with `[]`, 1 with `[out b]`, 2 with `[out b, abort heap]`. -/
def PrintAbortAt (b : Fin 256) (st : I.State) (t : Config I × Nat) (tr : List Ev) : Prop :=
  t.1 = Config.init [st] [] ∧ ((t.2 = 0 ∧ tr = []) ∨ (t.2 = 1 ∧ tr = [.out b]) ∨
    (t.2 = 2 ∧ tr = [.out b, .abort .heap]))

theorem printAbort_run {b : Fin 256} {st : I.State} {μ : Marks} {c c' : (printAbort I A b st).M.Cfg}
    {tr : List Ev} (h : (printAbort I A b st).M.Run μ c tr c') :
    ∀ trc, PrintAbortAt I b st c trc → PrintAbortAt I b st c' (trc ++ tr) := by
  induction h with
  | refl => intro trc h; simpa using h
  | step hs _ ih =>
    intro trc hc
    rw [← List.append_assoc]
    apply ih
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨h1, h2⟩ := hc
    rcases printAbort_step I A hs with ⟨hp, rfl, rfl⟩ | ⟨hp, rfl, rfl⟩ <;>
      rcases h2 with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> simp_all [PrintAbortAt]

/-- **Accepted: a justified abort.** The source prints `b` and then crosses
the heap budget; a target that prints `b` and then aborts with kind `heap`,
by a thread at the resolved site of `trivLayout.abortLbl .heap`, is
`Correct`. So the clauses that reject early (`not_correct_early_abort`) and
unjustified (`not_correct_spurious_abort`) aborts, with aborts classified by
label, still admit the abort the budget allows: it is justified at the
source configuration after the print (trace `[out b]`, the target's
observable trace), whose next step leaves the heap budget. -/
theorem correct_justified_abort (b : Fin 256) (st : I.State) :
    Correct (printAbort I A b st) (abortSrc b) trivLayout noBudget () := by
  have run : ∀ t0 tr t, (printAbort I A b st).load () trivLayout = some t0 →
      (printAbort I A b st).M.Run ((printAbort I A b st).marks () trivLayout) t0 tr t →
      PrintAbortAt I b st t tr := by
    intro t0 tr t h0 hr
    cases h0
    simpa using printAbort_run I A hr [] ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  have comp : ∀ x : Nat, Components (printAbort I A b st).M trivLayout (wThr _ 0) (Config.init [st] [], x)
      doneCfg :=
    fun x => components_doneCfg (printAbort I A b st).M st x (fun _ => rfl)
  have reach1 : (abortSrc b).Reach [.out b] 1 := by
    have r : (abortSrc b).Run 0 ([.out b] ++ []) 1 := LRun.step ⟨0, script_step rfl⟩ (.refl _)
    rw [List.append_nil] at r
    exact ⟨0, rfl, r⟩
  refine ⟨{
    R := fun t s => t.1 = Config.init [st] [] ∧ (t.2 : Nat) ≤ 2 ∧ s = min (t.2 : Nat) 1
    layout := trivLayout_wf
    start := ⟨(Config.init [st] [], 0), 0, rfl, rfl, rfl, by simp, rfl⟩
    progress := ?_
    sim := ?_
    abort := ?_
    explicit := ?_ }⟩
  · intro t0 tr t h0 hr
    obtain ⟨ht1, ht2⟩ := run t0 tr t h0 hr
    obtain ⟨t1, t2⟩ := t
    simp only at ht1 ht2
    subst ht1
    refine ⟨⟨id, ?_⟩, ?_, ?_⟩
    · rcases ht2 with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · refine .inr ⟨⟨0, by simp, rfl⟩, ?_⟩
        rintro tid ⟨-, rfl⟩
        exact ⟨_, _, .sys ⟨by simp, rfl⟩ (.inl ⟨rfl, rfl, rfl⟩) (by simp) (by simp) (by simp)⟩
      · refine .inr ⟨⟨0, by simp, rfl⟩, ?_⟩
        rintro tid ⟨-, rfl⟩
        refine ⟨_, _, .sys ⟨by simp, rfl⟩ (.inr ⟨rfl, rfl, rfl⟩) (by simp) ?_ (by simp)⟩
        intro k hk
        simp only [List.mem_singleton, Ev.abort.injEq] at hk
        subst hk
        exact ⟨7, by simp [Target.marks], _, rfl, rfl⟩
      · exact .inl (by simp)
    · simp [Config.init]
    · simp [Config.init]
  · rintro t0 tr ⟨t1, (t2 : Nat)⟩ h0 hr
    obtain ⟨ht1, ht2⟩ := run t0 tr _ h0 hr
    dsimp only at ht1 ht2
    subst ht1
    rcases ht2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨[], 0, ⟨0, rfl, .refl _⟩, ⟨rfl, by simp, by simp⟩, by simp⟩
    · exact ⟨[.out b], 1, reach1, ⟨rfl, by simp, by simp⟩, List.prefix_refl _⟩
    · exact ⟨[.out b], 1, reach1, ⟨rfl, by simp, by simp⟩, List.prefix_refl _⟩
  · rintro t0 tr ⟨t1, (t2 : Nat)⟩ tid es t' k h0 hr hs hk
    obtain ⟨ht1, ht2⟩ := run t0 tr _ h0 hr
    dsimp only at ht1 ht2
    subst ht1
    have htid : tid = 0 := hs.runs.2
    subst htid
    rcases printAbort_step I A hs with ⟨-, rfl, -⟩ | ⟨hp, rfl, -⟩
    · simp at hk
    · simp only [List.mem_singleton, Ev.abort.injEq] at hk
      subst hk
      dsimp only at hp
      subst hp
      rcases ht2 with ⟨h2, -⟩ | ⟨-, rfl⟩ | ⟨h2, -⟩
      · omega
      · refine ⟨1, wThr _ 0, 0, reach1, ⟨rfl, by simp, by simp⟩, comp 1, rfl,
          ⟨[], 2, script_step rfl, ?_, ?_⟩⟩
        · show heapUse doneCfg ≤ 0
          simp [heapUse_doneCfg]
        · show ¬ heapUse doneCell ≤ 0
          simp [heapUse_doneCell]
      · omega
  · rintro ⟨t1, (t2 : Nat)⟩ s ⟨h1, -, rfl⟩
    simp only at h1
    subst h1
    refine ⟨wThr _ 0, ?_⟩
    rcases Nat.lt_or_ge t2 1 with h | h
    · rw [show min t2 1 = 0 by omega]
      exact comp t2
    · rw [show min t2 1 = 1 by omega]
      exact comp t2

end Toy

/-! ## P3: skipped stores -/

/-- The source memory after `x := 1; x := 0` on a freshly allocated cell
`x` (label 0, one word): the allocation's zero, then `1`, then `0`. -/
def skipSrc : TermRun.Cfg :=
  { mem := #[⟨⟨0, 0⟩, .num 0, 0⟩, ⟨⟨0, 0⟩, .num 1, 0⟩, ⟨⟨0, 0⟩, .num 0, 0⟩], ths := #[] }

/-- The target memory with only the first store: `x` at address 64 (in
`trivLayout`'s heap), initially 0, one message writing 1. -/
def skipMem : Memory := { init := [], msgs := #[⟨wordLoc 64, 1, 0⟩] }

/-- The target memory with both stores: messages writing 1, then 0. -/
def bothMem : Memory := { init := [], msgs := #[⟨wordLoc 64, 1, 0⟩, ⟨wordLoc 64, 0, 0⟩] }

/-- The witness for `bothMem`: label 0 at 64; source timestamp `k` to target
timestamp `k` (the allocation's zero to the initial write). -/
def wBoth (M : ExtMachine) : Witness M :=
  { Witness.empty M with
    lbl := fun l => if l = 0 then some 64 else none
    lsize := fun _ => 1
    ts := fun k => if k < 3 then some k else none }

/-- The faithful target, which performs both stores, still passes
`Components`. -/
theorem components_both_stores (M : ExtMachine) (x : M.X)
    (hs : ∀ j, M.stackRange ({ threads := #[], mem := bothMem }, x) j = none) :
    Components M trivLayout (wBoth M) ({ threads := #[], mem := bothMem }, x) skipSrc := by
  refine ComponentsAll.scoped ?_ (fun _ => rfl) (fun _ => rfl)
  constructor
  · simp [skipSrc]
  · simp [wBoth, Witness.empty]
  · simp
  · simp [trivLayout]
  · intro l b h
    simp only [wBoth] at h
    split at h <;> simp at h
    subst h
    simp [labelRange, Range.Sub, trivLayout, wBoth]
  · intro l l' b b' hne h h'
    simp only [wBoth] at h h'
    split at h <;> split at h' <;> simp_all
  · intro m hm
    simp [skipSrc] at hm
    rcases hm with rfl | rfl | rfl <;> simp [wBoth]
  · intro k m h
    rcases k with _ | _ | _ | k <;> simp [skipSrc] at h <;> subst h <;>
      simp [wBoth, wordAddr, ValRep, bothMem, wordAt, Memory.read?, Memory.get?, Memory.initVal, wordLoc]
  · intro k m _ h k2 m2 hlt _
    simp only [wBoth] at h
    split at h <;> simp at h
    omega
  · intro k1 k2 k1' k2' h1 h2 _ _ hlt
    refine .inl ?_
    simp only [wBoth] at h1 h2
    split at h1 <;> split at h2 <;> simp at h1 h2
    omega
  · intro k' m' h _
    simp only [bothMem, Memory.get?] at h
    rcases k' with _ | _ | _ | k' <;> simp at h
    · exact ⟨1, by simp [skipSrc], by simp [wBoth]⟩
    · exact ⟨2, by simp [skipSrc], by simp [wBoth]⟩
  · simp [skipSrc]
  · simp [skipSrc]
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [wBoth, Witness.empty]
  · simp [wBoth, Witness.empty]
  · intro _ _ _ _ _ _ _ _ _ h
    simp only [wBoth, Witness.empty] at h
    repeat' split at h
    all_goals simp_all

/-- **A skipped store to a dead cell is accepted**: in `skipSrc` no thread
holds a reference to `x`, so its label is not live (`Live`) and its cells
are runtime-owned; the target that performed only the store of 1 passes
(with the empty witness). The rejected form needs a live cell
(`not_components_skipped_store`). -/
theorem components_skipped_store_dead (M : ExtMachine) (x : M.X)
    (hs : ∀ j, M.stackRange ({ threads := #[], mem := skipMem }, x) j = none) :
    Components M trivLayout (Witness.empty M) ({ threads := #[], mem := skipMem }, x) skipSrc := by
  have nl : ∀ l, ¬ Live skipSrc l := fun l h => live_no_threads rfl h
  constructor <;> simp only [skipSrc] at nl <;> simp [Witness.empty, skipSrc, trivLayout, hs, nl]

/-- A source thread at `ret p`, `p` a reference to label 0 (the cell `x`). -/
def ptrTh : TermRun.TTh := { term := .ret (.var "p"), env := [("p", .ptr .own .int, [TermRun.cst (.loc ⟨0, 0⟩ 0)])] }

/-- `skipSrc` with the thread `ptrTh`, which still reads `p`: `x` is live. -/
def skipSrcL : TermRun.Cfg := { skipSrc with ths := #[ptrTh] }

/-- Label 0 (`x`) is live in `skipSrcL`: `ptrTh` reads `p`. -/
theorem live_skipSrcL : Live skipSrcL 0 :=
  .root ⟨0, ptrTh, 0, ptrTh.env, ["p"], "p", _, _, TermRun.cst (.loc ⟨0, 0⟩ 0), ⟨0, 0⟩, 0, rfl, rfl, rfl,
    by simp, rfl, by simp, rfl, rfl⟩

/-- The witness for the live cell: `wBoth`, source thread 0 to target
thread 0, `p` in register `r`. -/
def wLive (M : ExtMachine) (r : M.I.RegId) : Witness M :=
  { wBoth M with
    thr := fun i => if i = 0 then some 0 else none
    env := fun i d y k => if i = 0 ∧ d = 0 ∧ y = "p" ∧ k = 0 then some (.one (.reg r)) else none }

/-- **The faithful target passes with the cell live**: one thread with `p`
(64) in register `r`, both stores performed. -/
theorem components_live_stores (M : ExtMachine) (st : M.I.State) (x : M.X) (r : M.I.RegId)
    (h64 : M.regVal st r = 64) (hs : ∀ j, M.stackRange ({ Config.init [st] [] with mem := bothMem }, x) j = none) :
    Components M trivLayout (wLive M r) ({ Config.init [st] [] with mem := bothMem }, x) skipSrcL := by
  refine ComponentsAll.scoped ?_ (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i hi
    simp [skipSrcL] at hi
    subst hi
    simp [wLive, Config.init]
  · intro i i' j h h'
    simp only [wLive] at h h'
    split at h <;> split at h' <;> simp_all
  · intro j tt _ h
    have : j = 0 := by
      have := (Array.getElem?_eq_some_iff.mp h).1
      simp [Config.init] at this
      omega
    subst this
    exact ⟨0, by simp [skipSrcL], by simp [wLive]⟩
  · simp [trivLayout]
  · intro l b h
    simp only [wLive, wBoth] at h
    split at h <;> simp at h
    subst h
    simp [labelRange, Range.Sub, trivLayout, wLive, wBoth]
  · intro l l' b b' hne h h'
    simp only [wLive, wBoth] at h h'
    split at h <;> split at h' <;> simp_all
  · intro m hm
    simp [skipSrcL, skipSrc] at hm
    rcases hm with rfl | rfl | rfl <;> simp [wLive, wBoth]
  · intro k m h
    rcases k with _ | _ | _ | k <;> simp [skipSrcL, skipSrc] at h <;> subst h <;>
      simp [wLive, wBoth, wordAddr, ValRep, bothMem, wordAt, Memory.read?, Memory.get?, Memory.initVal, wordLoc]
  · intro k m _ h k2 m2 hlt _
    simp only [wLive, wBoth] at h
    split at h <;> simp at h
    omega
  · intro k1 k2 k1' k2' h1 h2 _ _ hlt
    refine .inl ?_
    simp only [wLive, wBoth] at h1 h2
    split at h1 <;> split at h2 <;> simp at h1 h2
    omega
  · intro k' m' h _
    simp only [bothMem, Memory.get?] at h
    rcases k' with _ | _ | _ | k' <;> simp at h
    · exact ⟨1, by simp [skipSrcL, skipSrc], by simp [wLive, wBoth]⟩
    · exact ⟨2, by simp [skipSrcL, skipSrc], by simp [wLive, wBoth]⟩
  · intro i th j tt hth hthr htt d e he y ty ws hl k wd pl hwd hpl _hxf
    simp only [wLive] at hpl hthr
    split at hpl
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at hpl
      subst hpl
      simp at hthr
      subst hthr
      simp [skipSrcL] at hth
      subst hth
      simp [Config.init] at htt
      subst htt
      simp [frameEnvs, ptrTh] at he
      subst he
      simp [TermRun.lookupE] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp at hwd
      subst hwd
      exact ⟨64, by simp [placeVal, Thread.init, h64],
        by simp [ValRep, TermRun.cst, Promises.TVal.mk0, wordAddr, wLive, wBoth]⟩
    · simp at hpl
  · intro i th hth d e xs he hxs _hxf y hy ty ws hl k hk
    have hi : i = 0 := by
      have := (Array.getElem?_eq_some_iff.mp hth).1
      simp [skipSrcL] at this
      omega
    subst hi
    simp [skipSrcL] at hth
    subst hth
    rcases d with _ | d
    · simp [frameFv, ptrTh, exprFv, atVars] at hxs
      subst hxs
      simp at hy
      subst hy
      simp [frameEnvs, ptrTh] at he
      subst he
      simp [TermRun.lookupE] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp at hk
      subst hk
      exact ⟨.one (.reg r), by simp [wLive]⟩
    · simp [frameFv, ptrTh] at hxs
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [wLive, wBoth, Witness.empty]
  · simp [wLive, wBoth, Witness.empty]
  · intro _ _ _ _ _ _ _ _ _ h
    simp only [wLive, wBoth, Witness.empty] at h
    repeat' split at h
    all_goals simp_all

/-- **Rejected (P3): a skipped store to a live cell.** After the
source's `x := 1; x := 0`, with a thread still reading its reference `p`,
the latest value of `x` is 0; a target that performed only the store of 1
has latest value 1, and no witness makes the components of `R` hold: `x` is
live (`live_skipSrcL`), its epoch starts at allocation (`trivLayout` does
not relocate), the stores of 1 and of 0 are not the first messages to `x`,
so neither may map to the initial write (`ts_first`); both would have to map
to the one target message, against `ts_mono` (both are to the one location
`x`, so the per-location order applies). -/
theorem not_components_skipped_store (M : ExtMachine) (st : M.I.State) (x : M.X) :
    (lastMsg skipSrcL.mem ⟨0, 0⟩).map (·.val) = some (.num 0) ∧
      skipMem.read? (wordLoc 64) skipMem.last = some 1 ∧
      ¬ ∃ w, Components M trivLayout w ({ Config.init [st] [] with mem := skipMem }, x) skipSrcL := by
  refine ⟨rfl, rfl, ?_⟩
  rintro ⟨w, hc⟩
  have h0 : ∀ l, w.since l = 0 := hc.epoch_fixed rfl
  have one : ∀ k v, k ≠ 0 → skipSrcL.mem[k]? = some ⟨⟨0, 0⟩, v, 0⟩ → w.ts k = some 1 := by
    intro k v hk hm
    obtain ⟨k', a, u, hts, -, hr⟩ := hc.mem_rep k _ hm live_skipSrcL (.inl (by simp [h0]))
    rcases k' with _ | _ | k'
    · exact absurd rfl ((hc.ts_first k _ hm live_skipSrcL hts).2 0 ⟨⟨0, 0⟩, .num 0, 0⟩
        (Nat.pos_of_ne_zero hk) rfl)
    · exact hts
    · simp [skipMem, wordAt, Memory.read?, Memory.get?] at hr
  have := hc.ts_mono 1 2 1 1 _ _ rfl rfl rfl live_skipSrcL (by simp [h0]) (one 1 _ (by decide) rfl)
    (one 2 _ (by decide) rfl) (by decide) (by decide) (by decide)
  omega

/-! ## Runtime writes to live memory -/

/-- `x := 1` on a fresh cell `x` (label 0), with `ptrTh` still reading
`p`: `x` is live. -/
def storeL : TermRun.Cfg :=
  { mem := #[⟨⟨0, 0⟩, .num 0, 0⟩, ⟨⟨0, 0⟩, .num 1, 0⟩], ths := #[ptrTh] }

/-- The target memory: the store of 1 at 64, then a write of 3 to the same
word that no source step made. -/
def healMem : Memory := { init := [], msgs := #[⟨wordLoc 64, 1, 0⟩, ⟨wordLoc 64, 3, 0⟩] }

theorem live_storeL : Live storeL 0 :=
  .root ⟨0, ptrTh, 0, ptrTh.env, ["p"], "p", _, _, TermRun.cst (.loc ⟨0, 0⟩ 0), ⟨0, 0⟩, 0, rfl, rfl, rfl,
    by simp, rfl, by simp, rfl, rfl⟩

/-- **Rejected: a target write to live memory with no source step.** The
source stores 1 to the live cell `x`; a target that then writes 3 over it
(a runtime write that changes more than the colour bits, of which
`trivLayout` has none) is not related by any witness: `x` is placed at 64
(the only word holding 1), the write of 3 is inside its range, so it must
be the image of a source message, and neither source message (0 and 1) is
represented by 3. Whatever target epoch `w.tsFrom 0` the witness picks:
after it, `mem_onto` asks for a source image (no write is colour-only);
at or before it, `pre_alloc` asks for a source image or an outstanding
promise, and the initial thread has none. -/
theorem not_components_live_write (M : ExtMachine) (st : M.I.State) (x : M.X) :
    ¬ ∃ w, Components M trivLayout w ({ Config.init [st] [] with mem := healMem }, x) storeL := by
  rintro ⟨w, hc⟩
  have h0 : ∀ l, w.since l = 0 := hc.epoch_fixed rfl
  have hm1 : storeL.mem[1]? = some ⟨⟨0, 0⟩, .num 1, 0⟩ := rfl
  obtain ⟨b, hb, hsz⟩ := hc.lbl_mem ⟨⟨0, 0⟩, .num 1, 0⟩ (by simp [storeL]) live_storeL
  obtain ⟨hal, hr⟩ := hc.lbl_range 0 b hb
  simp only [labelRange, Range.Sub, trivLayout] at hr
  have hsz' : 0 < w.lsize 0 := hsz
  obtain ⟨k', a, v, hts, ha, hw, hv⟩ := hc.mem_rep 1 _ hm1 live_storeL (.inl (by simp [h0]))
  simp only [wordAddr, hb, Option.map_some, Option.some.injEq] at ha
  subst ha
  simp only [ValRep] at hv
  have hb64 : b = 64 := by
    have : b = 48 ∨ b = 56 ∨ b = 64 ∨ b = 72 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · rcases k' with _ | _ | _ | k' <;>
        simp [healMem, wordAt, Memory.read?, Memory.get?, Memory.initVal, wordLoc] at hw <;> omega
    · rcases k' with _ | _ | _ | k' <;>
        simp [healMem, wordAt, Memory.read?, Memory.get?, Memory.initVal, wordLoc] at hw <;> omega
    · rfl
    · rcases k' with _ | _ | _ | k' <;>
        simp [healMem, wordAt, Memory.read?, Memory.get?, Memory.initVal, wordLoc] at hw <;> omega
  subst hb64
  have hr : (labelRange w 0 64).contains (wordLoc 64).addr.toNat := by
    simp [labelRange, Range.contains, wordLoc]; omega
  have hin : ∃ k, k < storeL.mem.size ∧ w.ts k = some 2 := by
    rcases Nat.lt_or_ge (w.tsFrom 0) 2 with hlt | hge
    · rcases hc.mem_onto 2 ⟨wordLoc 64, 3, 0⟩ rfl ⟨0, 64, live_storeL, hb, hlt, hr⟩ with h | hco
      · exact h
      · exact absurd hco (not_colourOnly_zero rfl)
    · rcases hc.pre_alloc rfl 2 ⟨wordLoc 64, 3, 0⟩ rfl ⟨0, 64, live_storeL, hb, hge, hr⟩ with h | ⟨tt, htt, hp⟩
      · exact h
      · simp [Config.init] at htt; subst htt; simp [Thread.init] at hp
  obtain ⟨k, hk, hk2⟩ := hin
  · have hk' : k = 0 ∨ k = 1 := by simp [storeL] at hk; omega
    rcases hk' with rfl | rfl
    · obtain ⟨k'', a', v', hts', ha', hw', hv'⟩ :=
        hc.mem_rep 0 ⟨⟨0, 0⟩, .num 0, 0⟩ rfl live_storeL (.inl (by simp [h0]))
      rw [hk2] at hts'; cases hts'
      simp only [wordAddr, hb, Option.map_some, Option.some.injEq] at ha'
      subst ha'
      simp [healMem, wordAt, Memory.read?, Memory.get?, wordLoc, ValRep] at hw' hv'
      omega
    · obtain ⟨k'', a', v', hts', ha', hw', hv'⟩ :=
        hc.mem_rep 1 ⟨⟨0, 0⟩, .num 1, 0⟩ rfl live_storeL (.inl (by simp [h0]))
      rw [hk2] at hts'; cases hts'
      simp only [wordAddr, hb, Option.map_some, Option.some.injEq] at ha'
      subst ha'
      simp [healMem, wordAt, Memory.read?, Memory.get?, wordLoc, ValRep] at hw' hv'
      omega

/-- **Rejected (never-mirror witness): a write that is no promise.** The
witness is chosen per pair, so a proof may take `tsFrom l` as the target's
last timestamp for every label, exempting every outstanding promise from
`mem_onto`. That choice does not exempt the write of `not_components_live_write`:
it is no thread's outstanding promise, so `pre_alloc` still asks for a
preimage. -/
theorem not_components_live_write_tsFrom_last (M : ExtMachine) (st : M.I.State) (x : M.X) :
    ¬ ∃ w, (∀ l, w.tsFrom l = healMem.last) ∧
      Components M trivLayout w ({ Config.init [st] [] with mem := healMem }, x) storeL :=
  fun ⟨w, _, hc⟩ => not_components_live_write M st x ⟨w, hc⟩

/-- **Rejected (check on (f′)): a fulfilled promise with no
preimage.** The memory of `not_components_live_write`, but the writing
thread still has an outstanding promise, at timestamp 1; the write of 3 at
timestamp 2 is no longer one (it was fulfilled, or never promised). `pre_alloc`
exempts only outstanding promises of the writer, so the write of 3 must still
be the image of a source message, which it cannot be: a fulfilled promise
must gain a preimage. -/
theorem not_components_fulfilled_no_preimage (M : ExtMachine) (st : M.I.State) (x : M.X) :
    ¬ ∃ w, Components M trivLayout w
      ({ threads := #[{ Thread.init st with prom := [1] }], mem := healMem }, x) storeL := by
  rintro ⟨w, hc⟩
  have h0 : ∀ l, w.since l = 0 := hc.epoch_fixed rfl
  have hm1 : storeL.mem[1]? = some ⟨⟨0, 0⟩, .num 1, 0⟩ := rfl
  obtain ⟨b, hb, hsz⟩ := hc.lbl_mem ⟨⟨0, 0⟩, .num 1, 0⟩ (by simp [storeL]) live_storeL
  obtain ⟨hal, hr⟩ := hc.lbl_range 0 b hb
  simp only [labelRange, Range.Sub, trivLayout] at hr
  have hsz' : 0 < w.lsize 0 := hsz
  obtain ⟨k', a, v, hts, ha, hw, hv⟩ := hc.mem_rep 1 _ hm1 live_storeL (.inl (by simp [h0]))
  simp only [wordAddr, hb, Option.map_some, Option.some.injEq] at ha
  subst ha
  simp only [ValRep] at hv
  have hb64 : b = 64 := by
    have : b = 48 ∨ b = 56 ∨ b = 64 ∨ b = 72 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · rcases k' with _ | _ | _ | k' <;>
        simp [healMem, wordAt, Memory.read?, Memory.get?, Memory.initVal, wordLoc] at hw <;> omega
    · rcases k' with _ | _ | _ | k' <;>
        simp [healMem, wordAt, Memory.read?, Memory.get?, Memory.initVal, wordLoc] at hw <;> omega
    · rfl
    · rcases k' with _ | _ | _ | k' <;>
        simp [healMem, wordAt, Memory.read?, Memory.get?, Memory.initVal, wordLoc] at hw <;> omega
  subst hb64
  have hr : (labelRange w 0 64).contains (wordLoc 64).addr.toNat := by
    simp [labelRange, Range.contains, wordLoc]; omega
  have hin : ∃ k, k < storeL.mem.size ∧ w.ts k = some 2 := by
    rcases Nat.lt_or_ge (w.tsFrom 0) 2 with hlt | hge
    · rcases hc.mem_onto 2 ⟨wordLoc 64, 3, 0⟩ rfl ⟨0, 64, live_storeL, hb, hlt, hr⟩ with h | hco
      · exact h
      · exact absurd hco (not_colourOnly_zero rfl)
    · rcases hc.pre_alloc rfl 2 ⟨wordLoc 64, 3, 0⟩ rfl ⟨0, 64, live_storeL, hb, hge, hr⟩ with h | ⟨tt, htt, hp⟩
      · exact h
      · simp at htt; subst htt; simp at hp
  obtain ⟨k, hk, hk2⟩ := hin
  have hk' : k = 0 ∨ k = 1 := by simp [storeL] at hk; omega
  rcases hk' with rfl | rfl
  · obtain ⟨k'', a', v', hts', ha', hw', hv'⟩ :=
      hc.mem_rep 0 ⟨⟨0, 0⟩, .num 0, 0⟩ rfl live_storeL (.inl (by simp [h0]))
    rw [hk2] at hts'; cases hts'
    simp only [wordAddr, hb, Option.map_some, Option.some.injEq] at ha'
    subst ha'
    simp [healMem, wordAt, Memory.read?, Memory.get?, wordLoc, ValRep] at hw' hv'
    omega
  · obtain ⟨k'', a', v', hts', ha', hw', hv'⟩ :=
      hc.mem_rep 1 ⟨⟨0, 0⟩, .num 1, 0⟩ rfl live_storeL (.inl (by simp [h0]))
    rw [hk2] at hts'; cases hts'
    simp only [wordAddr, hb, Option.map_some, Option.some.injEq] at ha'
    subst ha'
    simp [healMem, wordAt, Memory.read?, Memory.get?, wordLoc, ValRep] at hw' hv'
    omega

/-! ## P4: empty register maps -/

/-- A source thread at `ret x` with `x = 5`. -/
def fiveTh : TermRun.TTh := { term := .ret (.var "x"), env := [("x", .int, [TermRun.cst (.num 5)])] }

/-- `fiveTh` does not run the output extern's model (`ret x`). -/
theorem not_externFrame_fiveTh : ¬ ExternFrame fiveTh 0 := by
  simp [ExternFrame, externModelTerms, modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody,
    Scc.Frontend.printAdv, Scc.Frontend.printNext, fiveTh]

/-- A thread at `ret ()` does not run the output extern's model, whatever
its frames: the model bodies' `ret ()` leaves are not `externModelTerms`, so
a user block returning `()` keeps `env_rep` and `env_total`. -/
theorem not_externFrame_ret (th : TermRun.TTh) (d : Nat) (a : CoreTerm.At) (h : th.term = .ret a) :
    ¬ ExternFrame th d := by
  simp [ExternFrame, externModelTerms, modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody,
    Scc.Frontend.printAdv, Scc.Frontend.printNext, h]

/-- The source configuration with that thread and empty memory. -/
def fiveCfg : TermRun.Cfg := { mem := #[], ths := #[fiveTh] }

/-- The witness that maps source thread 0 to target thread 0 and places
variable `x` (thread 0, current frame, word 0) at `o` (nowhere for `none`). -/
def wEnv (M : ExtMachine) (o : Option M.I.RegId) : Witness M :=
  { Witness.empty M with
    thr := fun i => if i = 0 then some 0 else none
    env := fun i d y k => if i = 0 ∧ d = 0 ∧ y = "x" ∧ k = 0 then o.map (fun r => .one (.reg r)) else none }

/-- **The placed variable passes** when the register holds its value: with
`x` placed in a register `r` that holds 5, the components hold. -/
theorem components_env_placed (M : ExtMachine) (st : M.I.State) (x : M.X) (r : M.I.RegId)
    (h5 : M.regVal st r = 5) (hs : ∀ j, M.stackRange (Config.init [st] [], x) j = none) :
    Components M trivLayout (wEnv M (some r)) (Config.init [st] [], x) fiveCfg := by
  refine ComponentsAll.scoped ?_ (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i hi
    simp [fiveCfg] at hi
    subst hi
    simp [wEnv, Config.init]
  · intro i i' j h h'
    simp only [wEnv] at h h'
    split at h <;> split at h' <;> simp_all
  · intro j tt _ h
    have : j = 0 := by
      have := (Array.getElem?_eq_some_iff.mp h).1
      simp [Config.init] at this
      omega
    subst this
    exact ⟨0, by simp [fiveCfg], by simp [wEnv]⟩
  · simp [trivLayout]
  · simp [wEnv, Witness.empty]
  · simp [wEnv, Witness.empty]
  · simp [fiveCfg]
  · simp [fiveCfg]
  · simp [fiveCfg]
  · simp [wEnv, Witness.empty]
  · simp [Config.init, Kraken.Promising.Memory.get?]
  · intro i th j tt hth hthr htt d e he y ty ws hl k wd pl hwd hpl _hxf
    simp only [wEnv] at hpl hthr
    split at hpl
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      simp only [Option.map_some, Option.some.injEq] at hpl
      subst hpl
      simp at hthr
      subst hthr
      simp [fiveCfg] at hth
      subst hth
      simp [Config.init] at htt
      subst htt
      simp [frameEnvs, fiveTh] at he
      subst he
      simp [TermRun.lookupE] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp at hwd
      subst hwd
      exact ⟨5, by simp [placeVal, Thread.init, h5], by simp [ValRep, TermRun.cst, Promises.TVal.mk0]⟩
    · simp at hpl
  · intro i th hth d e xs he hxs _hxf y hy ty ws hl k hk
    have hi : i = 0 := by
      have := (Array.getElem?_eq_some_iff.mp hth).1
      simp [fiveCfg] at this
      omega
    subst hi
    simp [fiveCfg] at hth
    subst hth
    rcases d with _ | d
    · simp [frameFv, fiveTh, exprFv, atVars] at hxs
      subst hxs
      simp at hy
      subst hy
      simp [frameEnvs, fiveTh] at he
      subst he
      simp [TermRun.lookupE] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp at hk
      subst hk
      exact ⟨.one (.reg r), by simp [wEnv]⟩
    · simp [frameFv, fiveTh] at hxs
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [wEnv, Witness.empty]
  · simp [wEnv, Witness.empty]
  · intro _ _ _ _ _ _ _ _ _ h
    simp only [wEnv, Witness.empty] at h
    repeat' split at h
    all_goals simp_all

/-- **Rejected (P4): an empty register map.** The source
variable `x` holds 5 and is read next (`ret x`); on a target where every
register holds 7 and no stack slot is mapped, no witness makes the
components of `R` hold: `env_total` must place `x` somewhere, and every
place holds 7 or nothing. In particular the empty map (`wEnv M none`) is
rejected. -/
theorem not_components_empty_env (M : ExtMachine) (st : M.I.State) (x : M.X)
    (h7 : ∀ st r, M.regVal st r = 7) (hp : ∀ st a, M.privLoad st a = none) :
    TermRun.lookupE fiveTh.env "x" = some (.int, [TermRun.cst (.num 5)]) ∧
      ¬ ∃ w, Components M trivLayout w (Config.init [st] [], x) fiveCfg := by
  refine ⟨rfl, ?_⟩
  rintro ⟨w, hc⟩
  obtain ⟨pl, hpl⟩ := hc.env_total 0 fiveTh rfl 0 fiveTh.env ["x"] rfl rfl
    not_externFrame_fiveTh "x" (by simp) .int
    [TermRun.cst (.num 5)] rfl 0 (by simp)
  obtain ⟨j, hj, hjlt⟩ := hc.thr_total 0 (by simp [fiveCfg])
  have hj0 : j = 0 := by simp [Config.init] at hjlt; omega
  subst hj0
  have hwp := hc.env_rep 0 fiveTh 0 (Thread.init st) rfl hj (by simp [Config.init]) 0 fiveTh.env
    rfl "x" .int [TermRun.cst (.num 5)] rfl 0 (TermRun.cst (.num 5)) pl rfl hpl not_externFrame_fiveTh
  cases pl with
  | one pl =>
    obtain ⟨v, hv, hrep⟩ := hwp
    simp only [ValRep, TermRun.cst, Promises.TVal.mk0] at hrep
    cases pl with
    | reg r =>
      simp [placeVal, h7] at hv
      omega
    | slot a => simp [placeVal, hp] at hv
  | loc pb po =>
    obtain ⟨vb, vo, -, -, hrep⟩ := hwp
    simp [LocRep, TermRun.cst, Promises.TVal.mk0] at hrep
  | imm n =>
    have := hc.env_imm 0 fiveTh 0 fiveTh.term "x" 0 n rfl rfl hpl
    simp [trivLayout] at this

/-! ## Live immediate constants: the immediate table -/

open Classical in
/-- `trivLayout` with the immediate table naming word 0 of variable `y` at
the control point `ret x` (`fiveTh`'s term) as the constant `n`. -/
noncomputable def immLayout (n : Nat) (y : String) : Layout :=
  { trivLayout with imms := fun e z k => if e = fiveTh.term ∧ z = y ∧ k = 0 then some n else none }

/-- The witness that maps source thread 0 to target thread 0 and places
variable `x` (thread 0, current frame, word 0) at the immediate `n`. -/
def wImm (M : ExtMachine) (n : Nat) : Witness M :=
  { Witness.empty M with
    thr := fun i => if i = 0 then some 0 else none
    env := fun i d y k => if i = 0 ∧ d = 0 ∧ y = "x" ∧ k = 0 then some (.imm n) else none }

/-- **Accepted: a live constant at the immediate the table names.** With the
table saying that `x` is 5 at `ret x`, the witness placing `x` at the
immediate 5 gives the components, whatever the registers hold. -/
theorem components_env_imm (M : ExtMachine) (st : M.I.State) (x : M.X)
    (hs : ∀ j, M.stackRange (Config.init [st] [], x) j = none) :
    Components M (immLayout 5 "x") (wImm M 5) (Config.init [st] [], x) fiveCfg := by
  refine ComponentsAll.scoped ?_ (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i hi
    simp [fiveCfg] at hi
    subst hi
    simp [wImm, Config.init]
  · intro i i' j h h'
    simp only [wImm] at h h'
    split at h <;> split at h' <;> simp_all
  · intro j tt _ h
    have : j = 0 := by
      have := (Array.getElem?_eq_some_iff.mp h).1
      simp [Config.init] at this
      omega
    subst this
    exact ⟨0, by simp [fiveCfg], by simp [wImm]⟩
  · simp [immLayout, trivLayout]
  · simp [wImm, Witness.empty]
  · simp [wImm, Witness.empty]
  · simp [fiveCfg]
  · simp [fiveCfg]
  · simp [fiveCfg]
  · simp [wImm, Witness.empty]
  · simp [Config.init, Kraken.Promising.Memory.get?]
  · intro i th j tt hth hthr htt d e he y ty ws hl k wd pl hwd hpl _hxf
    simp only [wImm] at hpl hthr
    split at hpl
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at hpl
      subst hpl
      simp [fiveCfg] at hth
      subst hth
      simp [frameEnvs, fiveTh] at he
      subst he
      simp [TermRun.lookupE] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp at hwd
      subst hwd
      simp [WordPlaceRep, ValRep, TermRun.cst, Promises.TVal.mk0]
    · simp at hpl
  · intro i th hth d e xs he hxs _hxf y hy ty ws hl k hk
    have hi : i = 0 := by
      have := (Array.getElem?_eq_some_iff.mp hth).1
      simp [fiveCfg] at this
      omega
    subst hi
    simp [fiveCfg] at hth
    subst hth
    rcases d with _ | d
    · simp [frameFv, fiveTh, exprFv, atVars] at hxs
      subst hxs
      simp at hy
      subst hy
      simp [frameEnvs, fiveTh] at he
      subst he
      simp [TermRun.lookupE] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp at hk
      subst hk
      exact ⟨.imm 5, by simp [wImm]⟩
    · simp [frameFv, fiveTh] at hxs
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [wImm, Witness.empty]
  · simp [wImm, Witness.empty]
  · intro i th d e y k n hth he hpl
    simp only [wImm] at hpl
    split at hpl
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      simp only [Option.some.injEq, WordPlace.imm.injEq] at hpl
      subst hpl
      simp [fiveCfg] at hth
      subst hth
      simp [frameTerms, fiveTh] at he
      subst he
      simp [immLayout, fiveTh]
    · simp at hpl

/-- **Rejected: an immediate the table does not name.** `x` holds 5 at
`ret x`; on a target where every register holds 7 and no stack slot is
mapped, with a table that names any other constant `n` for `x`, or names a
variable other than `x` (`y`), no witness gives the components: a register or
slot holds 7 or nothing, a pair cannot represent a number, and an immediate
must be the table's (`env_imm`) and represent 5 (`ValRep`). -/
theorem not_components_imm_table (M : ExtMachine) (st : M.I.State) (x : M.X)
    (h7 : ∀ st r, M.regVal st r = 7) (hp : ∀ st a, M.privLoad st a = none) {n : Nat} {y : String}
    (hny : ¬ (n = 5 ∧ y = "x")) :
    ¬ ∃ w, Components M (immLayout n y) w (Config.init [st] [], x) fiveCfg := by
  rintro ⟨w, hc⟩
  obtain ⟨pl, hpl⟩ := hc.env_total 0 fiveTh rfl 0 fiveTh.env ["x"] rfl rfl
    not_externFrame_fiveTh "x" (by simp) .int
    [TermRun.cst (.num 5)] rfl 0 (by simp)
  obtain ⟨j, hj, hjlt⟩ := hc.thr_total 0 (by simp [fiveCfg])
  have hj0 : j = 0 := by simp [Config.init] at hjlt; omega
  subst hj0
  have hwp := hc.env_rep 0 fiveTh 0 (Thread.init st) rfl hj (by simp [Config.init]) 0 fiveTh.env
    rfl "x" .int [TermRun.cst (.num 5)] rfl 0 (TermRun.cst (.num 5)) pl rfl hpl not_externFrame_fiveTh
  cases pl with
  | one pl =>
    obtain ⟨v, hv, hrep⟩ := hwp
    simp only [ValRep, TermRun.cst, Promises.TVal.mk0] at hrep
    cases pl with
    | reg r =>
      simp [placeVal, h7] at hv
      omega
    | slot a => simp [placeVal, hp] at hv
  | loc pb po =>
    obtain ⟨vb, vo, -, -, hrep⟩ := hwp
    simp [LocRep, TermRun.cst, Promises.TVal.mk0] at hrep
  | imm m =>
    have ht := hc.env_imm 0 fiveTh 0 fiveTh.term "x" 0 m rfl rfl hpl
    simp only [WordPlaceRep, ValRep, TermRun.cst, Promises.TVal.mk0] at hwp
    simp only [immLayout] at ht
    split at ht
    · rename_i hc'
      simp only [Option.some.injEq] at ht
      exact hny ⟨by omega, hc'.2.1.symm⟩
    · simp at ht

/-- The value variant: the table says 6 where `x` holds 5. -/
theorem not_components_imm_wrong (M : ExtMachine) (st : M.I.State) (x : M.X)
    (h7 : ∀ st r, M.regVal st r = 7) (hp : ∀ st a, M.privLoad st a = none) :
    ¬ ∃ w, Components M (immLayout 6 "x") w (Config.init [st] [], x) fiveCfg :=
  not_components_imm_table M st x h7 hp (by decide)

/-- The variable variant: the table names `y`, not `x`. -/
theorem not_components_imm_wrong_var (M : ExtMachine) (st : M.I.State) (x : M.X)
    (h7 : ∀ st r, M.regVal st r = 7) (hp : ∀ st a, M.privLoad st a = none) :
    ¬ ∃ w, Components M (immLayout 5 "y") w (Config.init [st] [], x) fiveCfg :=
  not_components_imm_table M st x h7 hp (by decide)

/-! ## Free variables: `cas`'s failure branch -/

/-- A source thread at a `cas` (on unit atoms) whose result is named `x`,
with `x = 5` bound outside: the `ok` branch rebinds `x`, the `fail` branch
reads the outer `x` (`ret x`). -/
def casTh : TermRun.TTh :=
  { fiveTh with term := .cas false false .unit .unit .unit "x" (.ret .unit) (.ret (.var "x")) }

/-- `casTh` does not run the output extern's model (a `cas`). -/
theorem not_externFrame_casTh : ¬ ExternFrame casTh 0 := by
  simp [ExternFrame, externModelTerms, modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody,
    Scc.Frontend.printAdv, Scc.Frontend.printNext, casTh]

/-- The source configuration with that thread and empty memory. -/
def casCfg : TermRun.Cfg := { mem := #[], ths := #[casTh] }

/-- **Rejected (`exprFv`): the outer variable read by a `cas` failure
branch dropped.** `cas` binds its result `x` in `ok` only, so `fail` reads
the outer `x`, which holds 5 and must be placed (`env_total`); on a target
where every register holds 7 and no stack slot is mapped, no witness makes
the components hold. Before `exprFv` matched `TermScope.freeB`, it removed
`x` from both branches, so the empty map passed: the failure branch's reads
were under-reported roots. -/
theorem not_components_cas_fail (M : ExtMachine) (st : M.I.State) (x : M.X)
    (h7 : ∀ st r, M.regVal st r = 7) (hp : ∀ st a, M.privLoad st a = none) :
    exprFv casTh.term = ["x"] ∧ ¬ ∃ w, Components M trivLayout w (Config.init [st] [], x) casCfg := by
  refine ⟨rfl, ?_⟩
  rintro ⟨w, hc⟩
  obtain ⟨pl, hpl⟩ := hc.env_total 0 casTh rfl 0 casTh.env ["x"] rfl rfl
    not_externFrame_casTh "x" (by simp) .int
    [TermRun.cst (.num 5)] rfl 0 (by simp)
  obtain ⟨j, hj, hjlt⟩ := hc.thr_total 0 (by simp [casCfg])
  have hj0 : j = 0 := by simp [Config.init] at hjlt; omega
  subst hj0
  have hwp := hc.env_rep 0 casTh 0 (Thread.init st) rfl hj (by simp [Config.init]) 0 casTh.env
    rfl "x" .int [TermRun.cst (.num 5)] rfl 0 (TermRun.cst (.num 5)) pl rfl hpl not_externFrame_casTh
  cases pl with
  | one pl =>
    obtain ⟨v, hv, hrep⟩ := hwp
    simp only [ValRep, TermRun.cst, Promises.TVal.mk0] at hrep
    cases pl with
    | reg r =>
      simp [placeVal, h7] at hv
      omega
    | slot a => simp [placeVal, hp] at hv
  | loc pb po =>
    obtain ⟨vb, vo, -, -, hrep⟩ := hwp
    simp [LocRep, TermRun.cst, Promises.TVal.mk0] at hrep
  | imm n =>
    have := hc.env_imm 0 casTh 0 casTh.term "x" 0 n rfl rfl hpl
    simp [trivLayout] at this

/-! ## Locatives: base and offset word -/

/-- A source thread at `ret p`, `p` the locative `b[1]`: word 1 of label 0. -/
def locTh : TermRun.TTh :=
  { term := .ret (.var "p"), env := [("p", .loc .own .int, [TermRun.cst (.loc ⟨0, 1⟩ 0)])] }

/-- `locTh` does not run the output extern's model (`ret p`). -/
theorem not_externFrame_locTh : ¬ ExternFrame locTh 0 := by
  simp [ExternFrame, externModelTerms, modelTerms, Scc.Frontend.printBody, Scc.Frontend.printLBody,
    Scc.Frontend.printAdv, Scc.Frontend.printNext, locTh]

/-- `skipSrc` with the thread `locTh`: label 0 is live. -/
def skipSrcLoc : TermRun.Cfg := { skipSrc with ths := #[locTh] }

/-- Label 0 is live in `skipSrcLoc`: `locTh` reads `p`. -/
theorem live_skipSrcLoc : Live skipSrcLoc 0 :=
  .root ⟨0, locTh, 0, locTh.env, ["p"], "p", _, _, TermRun.cst (.loc ⟨0, 1⟩ 0), ⟨0, 1⟩, 0, rfl, rfl, rfl,
    by simp, rfl, by simp, rfl, rfl⟩

/-- The witness for `b[1]`: `wBoth` with label 0 two words long, source
thread 0 to target thread 0, `p` as the pair (register `r`, immediate
`off`). -/
def wLoc (M : ExtMachine) (r : M.I.RegId) (off : Nat) : Witness M :=
  { wBoth M with
    lsize := fun _ => 2
    thr := fun i => if i = 0 then some 0 else none
    env := fun i d y k => if i = 0 ∧ d = 0 ∧ y = "p" ∧ k = 0 then some (.loc (.reg r) (.imm off)) else none }

/-- **Accepted: `b[1]` as `(b, 8)`.** The locative `b[1]` is kept as the
object's base (64, in register `r`) and the offset word 8 (an immediate,
folded into the access's displacement), as the lowering keeps it
(`Scc/LAYOUT.md` §4). -/
theorem components_loc_base_off (M : ExtMachine) (st : M.I.State) (x : M.X) (r : M.I.RegId)
    (h64 : M.regVal st r = 64) (hs : ∀ j, M.stackRange ({ Config.init [st] [] with mem := bothMem }, x) j = none) :
    Components M trivLayout (wLoc M r 8) ({ Config.init [st] [] with mem := bothMem }, x) skipSrcLoc := by
  refine ComponentsAll.scoped ?_ (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i hi
    simp [skipSrcLoc] at hi
    subst hi
    simp [wLoc, Config.init]
  · intro i i' j h h'
    simp only [wLoc] at h h'
    split at h <;> split at h' <;> simp_all
  · intro j tt _ h
    have : j = 0 := by
      have := (Array.getElem?_eq_some_iff.mp h).1
      simp [Config.init] at this
      omega
    subst this
    exact ⟨0, by simp [skipSrcLoc], by simp [wLoc]⟩
  · simp [trivLayout]
  · intro l b h
    simp only [wLoc, wBoth] at h
    split at h <;> simp at h
    subst h
    simp [labelRange, Range.Sub, trivLayout, wLoc, wBoth]
  · intro l l' b b' hne h h'
    simp only [wLoc, wBoth] at h h'
    split at h <;> split at h' <;> simp_all
  · intro m hm
    simp [skipSrcLoc, skipSrc] at hm
    rcases hm with rfl | rfl | rfl <;> simp [wLoc, wBoth]
  · intro k m h
    rcases k with _ | _ | _ | k <;> simp [skipSrcLoc, skipSrc] at h <;> subst h <;>
      simp [wLoc, wBoth, wordAddr, ValRep, bothMem, wordAt, Memory.read?, Memory.get?, Memory.initVal, wordLoc]
  · intro k m _ h k2 m2 hlt _
    simp only [wLoc, wBoth] at h
    split at h <;> simp at h
    omega
  · intro k1 k2 k1' k2' h1 h2 _ _ hlt
    refine .inl ?_
    simp only [wLoc, wBoth] at h1 h2
    split at h1 <;> split at h2 <;> simp at h1 h2
    omega
  · intro k' m' h _
    simp only [bothMem, Memory.get?] at h
    rcases k' with _ | _ | _ | k' <;> simp at h
    · exact ⟨1, by simp [skipSrcLoc, skipSrc], by simp [wLoc, wBoth]⟩
    · exact ⟨2, by simp [skipSrcLoc, skipSrc], by simp [wLoc, wBoth]⟩
  · intro i th j tt hth hthr htt d e he y ty ws hl k wd pl hwd hpl _hxf
    simp only [wLoc] at hpl hthr
    split at hpl
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at hpl
      subst hpl
      simp at hthr
      subst hthr
      simp [skipSrcLoc] at hth
      subst hth
      simp [Config.init] at htt
      subst htt
      simp [frameEnvs, locTh] at he
      subst he
      simp [TermRun.lookupE] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp at hwd
      subst hwd
      exact ⟨64, 8, by simp [placeVal, Thread.init, h64], rfl,
        by simp [LocRep, TermRun.cst, Promises.TVal.mk0, wLoc, wBoth]⟩
    · simp at hpl
  · intro i th hth d e xs he hxs _hxf y hy ty ws hl k hk
    have hi : i = 0 := by
      have := (Array.getElem?_eq_some_iff.mp hth).1
      simp [skipSrcLoc] at this
      omega
    subst hi
    simp [skipSrcLoc] at hth
    subst hth
    rcases d with _ | d
    · simp [frameFv, locTh, exprFv, atVars] at hxs
      subst hxs
      simp at hy
      subst hy
      simp [frameEnvs, locTh] at he
      subst he
      simp [TermRun.lookupE] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp at hk
      subst hk
      exact ⟨.loc (.reg r) (.imm 8), by simp [wLoc]⟩
    · simp [frameFv, locTh] at hxs
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [wLoc, wBoth, Witness.empty]
  · simp [wLoc, wBoth, Witness.empty]
  · intro _ _ _ _ _ _ _ _ _ h
    simp only [wLoc, wBoth, Witness.empty] at h
    repeat' split at h
    all_goals simp_all

/-- The word place of `p` under any witness for `skipSrcLoc` that maps
source thread 0 to target thread 0 represents `b[1]`. -/
theorem env_rep_locTh {M : ExtMachine} {st : M.I.State} {x : M.X} {w : Witness M}
    (hc : Components M trivLayout w ({ Config.init [st] [] with mem := bothMem }, x) skipSrcLoc)
    (hj : w.thr 0 = some 0) {wp : WordPlace M.I.RegId} (hp : w.env 0 0 "p" 0 = some wp) :
    WordPlaceRep M w.lbl st wp (.loc ⟨0, 1⟩ 0) :=
  hc.env_rep 0 locTh 0 (Thread.init st) rfl hj (by simp [Config.init]) 0 locTh.env rfl "p" _ _ rfl 0
    (TermRun.cst (.loc ⟨0, 1⟩ 0)) wp rfl hp not_externFrame_locTh

/-- **Rejected: `b[1]` as `(b + 8, 0)`.** With label 0 at 64, a witness
that keeps `p = b[1]` as the derived address 72 in a register fails
`env_rep`, whatever the offset word (with offset word 0 as well as 8): the
base half must be the label's base (scalar word 0), not an interior
address. -/
theorem not_components_loc_interior (M : ExtMachine) (st : M.I.State) (x : M.X) (r : M.I.RegId)
    (h72 : M.regVal st r = 72) (off : OffPlace M.I.RegId) :
    ¬ ∃ w, w.lbl 0 = some 64 ∧ w.thr 0 = some 0 ∧ w.env 0 0 "p" 0 = some (.loc (.reg r) off) ∧
      Components M trivLayout w ({ Config.init [st] [] with mem := bothMem }, x) skipSrcLoc := by
  rintro ⟨w, hl, hj, hp, hc⟩
  obtain ⟨vb, vo, hb, -, hrep⟩ := env_rep_locTh hc hj hp
  simp [placeVal, h72] at hb
  simp [LocRep, hl] at hrep
  omega

/-- **Rejected: `b[1]` with the base of another label.** With label 0 at 64,
a base register holding 128 (another object's base) fails `env_rep`,
whatever the offset word. -/
theorem not_components_loc_wrong_label (M : ExtMachine) (st : M.I.State) (x : M.X) (r : M.I.RegId)
    (h128 : M.regVal st r = 128) (off : OffPlace M.I.RegId) :
    ¬ ∃ w, w.lbl 0 = some 64 ∧ w.thr 0 = some 0 ∧ w.env 0 0 "p" 0 = some (.loc (.reg r) off) ∧
      Components M trivLayout w ({ Config.init [st] [] with mem := bothMem }, x) skipSrcLoc := by
  rintro ⟨w, hl, hj, hp, hc⟩
  obtain ⟨vb, vo, hb, -, hrep⟩ := env_rep_locTh hc hj hp
  simp [placeVal, h128] at hb
  simp [LocRep, hl] at hrep
  omega

end Scc.Sem.Holes
