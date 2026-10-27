/-
The source machine, as an abstract interface.

WeakCore's whole-program semantics is `TermRun.Step p k arch` on
`TermRun.Cfg`, with dynamic thread creation as the separate step
`TermSpawnStep.Spawn` (`TermSpawnStep.StepX := Step ∨ Spawn`). It has no
extern step and no trace yet (`print` and the exit event are being added
upstream). The `scc` statement needs a source trace, so this file abstracts
the source the same way `Scc/Sem/Ext.lean` abstracts the target:

- `SrcSem`: a configuration type with a projection `core` to `TermRun.Cfg`
  (the part the relation `R` of `Scc/Sem/Correct.lean` inspects: threads,
  register environments, memory), a set of start configurations, and a step
  labelled with the events it emits.
- `SrcSem.ofStepsG p k arch Sp obsTrace`: `TermRun.Step` beside an extra
  configuration step `Sp`, each step labelled with the growth of an observable
  trace; its runs are WeakCore's `StepsG p k arch Sp` runs
  (`ofStepsG_run_stepsG`), so WeakCore's theorems stated along them apply.
- `SrcSem.ofStep` (`Sp` empty) and `SrcSem.ofSpawn` (`Sp := Spawn`), both
  with the empty trace.
- `srcObs`: the observable trace (events cut at the exit point, with `main`'s
  return as an exit) built from a per-configuration event list.
- `source P p`: **the source instance**, `ofStepsG p k arch (Spawn ∨ ext)
  (srcObs trace)` (`sourceG`) with every step gated on `main` not having
  returned, its runs `StepsG` runs (`source_run_stepsG`), with the extern
  step and its event list a hook
  (`SrcHooks`; `SrcHooks.none` until WeakCore's extern step lands, then
  `trace` is its `Cfg.trace` mapped to `Ev`). Parameters `SrcParams`: knobs,
  memory model, thread capacity, start configurations (`mainInit`: empty
  setup block).
- P9: `srcObs` only grows along steps of `source P p` for every
  hook whose event list only grows (`source_obs_mono`), so a run's trace is
  the growth (`source_run_trace`); nothing follows an exit in it
  (`cutAtExit_exit_last`). `srcObs_mono` states the conditions for an
  ungated machine (the event list also stops growing once `main` has
  returned).
-/
import Scc.Sem.Basic
import WeakCore.TermSpawnStep

namespace Scc.Sem

/-- **The source machine interface.** -/
structure SrcSem where
  /-- Configurations. -/
  Cfg : Type
  /-- The core-language configuration inside a configuration. -/
  core : Cfg → TermRun.Cfg
  /-- Start configurations (the state after the setup block, before `main`). -/
  init : Cfg → Prop
  /-- One step of thread `i`, with the events it emits. The thread index ties
  a step to the thread the relation `R` maps a target thread to (the abort
  clause of `Scc/Sem/Correct.lean` asks for a step of that thread). -/
  step : Nat → Cfg → List Ev → Cfg → Prop

namespace SrcSem

variable (S : SrcSem)

/-- Runs of the source machine, with their traces. -/
def Run : S.Cfg → List Ev → S.Cfg → Prop := LRun fun c es c' => ∃ i, S.step i c es c'

/-- Reachable from a start configuration, with trace `tr`. -/
def Reach (tr : List Ev) (s : S.Cfg) : Prop := ∃ s0, S.init s0 ∧ S.Run s0 tr s

/-! ## Observable traces of the core machine

WeakCore's extern design (not yet in the tree) adds an append-only
`Cfg.trace` of events `out b` (from `emit b`) and `exit n` (from `exitEv n`),
with an `Ext` configuration step beside `Spawn` (runs `StepsG p k arch
(Spawn ∨ Ext)`). A behaviour is the trace's growth from the start, cut at the
exit point: the first `exit`, else thread 0 returning with an empty stack.
`srcObs` builds that observable trace from any per-configuration event list
(`out b ↦ Ev.out b`, `exit n ↦ Ev.exit (n % 256)`), and `ofStepsG` labels each
step with its growth. -/

/-- The trace up to and including its first `exit`. -/
def cutAtExit : List Ev → List Ev
  | [] => []
  | .exit c :: _ => [.exit c]
  | e :: es => e :: cutAtExit es

/-- The exit event of `main` returning: thread 0 at `ret` with an empty
stack. Its code is the returned number modulo 256, or 0 for any other result
(`main` returning unit). -/
def mainExit (c : TermRun.Cfg) : List Ev :=
  match c.ths[0]? with
  | some th =>
    match th.term, th.stack with
    | .ret a, [] =>
      match TermRun.evalAt th.env a with
      | some (_, [w]) =>
        match w.val with
        | .num n => [.exit ⟨n % 256, Nat.mod_lt _ (by decide)⟩]
        | _ => [.exit 0]
      | _ => [.exit 0]
    | _, _ => []
  | none => []

/-- The observable trace of a configuration, from its event list `tr`: the
events, then `main`'s exit if it has returned, cut at the first exit. -/
def srcObs (tr : TermRun.Cfg → List Ev) (c : TermRun.Cfg) : List Ev := cutAtExit (tr c ++ mainExit c)

/-! ## Thread-indexed core steps -/

/-- A `TermRun.Step` taken by thread `i`: a thread step of `i` or a promise
of `i`, after which `i` is certified (the two cases of `TermRun.Step`, with
the thread exposed). -/
def StepBy (p : CoreTerm.Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (i : Nat)
    (c c' : TermRun.Cfg) : Prop :=
  (c' ∈ TermRun.threadSteps p k arch c i ∧ TermRun.Certified p k arch c' i) ∨
    ∃ a v w, i < c.ths.size ∧ w < c.mem.size ∧
      TermRun.Certified p k arch (TermRun.promise c i a v w) i ∧ c' = TermRun.promise c i a v w

theorem StepBy.step {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat}
    {c c' : TermRun.Cfg} (h : StepBy p k arch i c c') : TermRun.Step p k arch c c' := by
  rcases h with ⟨hm, hc⟩ | ⟨a, v, w, hi, hw, hc, rfl⟩
  · exact .thread i hm hc
  · exact .prom i a v w hi hw hc

theorem StepBy.of_step {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}
    {c c' : TermRun.Cfg} (h : TermRun.Step p k arch c c') : ∃ i, StepBy p k arch i c c' := by
  cases h with
  | thread i hm hc => exact ⟨i, .inl ⟨hm, hc⟩⟩
  | prom i a v w hi hw hc => exact ⟨i, .inr ⟨a, v, w, hi, hw, hc, rfl⟩⟩

/-- A spawn by thread `i` (the premises of `TermSpawnStep.Spawn.mk`, with the
thread exposed). It does not depend on the program, knobs or architecture
(neither do the premises of `Spawn.mk`). -/
def SpawnBy (cap : Nat) (i : Nat)
    (c c' : TermRun.Cfg) : Prop :=
  ∃ (x f : String) (a : CoreTerm.At) (T : CoreLang.Ty) (ts : List CoreLang.Ty) (e : CoreTerm.Expr)
    (th : TermRun.TTh) (rt : CoreLang.Ty) (ws : List TermRun.Word),
    c.ths[i]? = some th ∧ th.term = .let_ x (.spawn f a T ts) e ∧ th.promises = [] ∧
    c.ths.size < cap ∧ TermRun.evalAt th.env a = some (rt, ws) ∧
    c' = TermSpawnStep.spawnCfg c i th x e f ts T ws

theorem SpawnBy.spawn {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap i : Nat}
    {c c' : TermRun.Cfg} (h : SpawnBy cap i c c') : TermSpawnStep.Spawn p k arch cap c c' := by
  obtain ⟨x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, rfl⟩ := h
  exact .mk i x f a T ts e th rt ws h1 h2 h3 h4 h5

/-! ## Instances -/

/-- **WeakCore's machine with an extra configuration step** `Sp` (spawns,
extern steps; `Sp i` is a step taken by thread `i`), from the start
configurations `init`. A step of thread `i` is a `StepBy i` (a
`TermRun.Step` of `i`) or an `Sp i` step; its events are the growth of the
observable trace `obsTrace` (`srcObs` of the configuration's event list, once
WeakCore has one). Its runs are WeakCore's `StepsG` runs with extra step
`fun c c' => ∃ i, Sp i c c'` (`ofStepsG_run_stepsG`), and when `obsTrace` only
grows along steps the run's trace is exactly the growth
(`ofStepsG_run_trace`). -/
def ofStepsG (p : CoreTerm.Prog) (k : Promises.Knobs) (arch : WeakMem.Arch)
    (Sp : Nat → TermRun.Cfg → TermRun.Cfg → Prop) (obsTrace : TermRun.Cfg → List Ev)
    (init : TermRun.Cfg → Prop) : SrcSem where
  Cfg := TermRun.Cfg
  core := id
  init := init
  step i c es c' := (StepBy p k arch i c c' ∨ Sp i c c') ∧ es = (obsTrace c').drop (obsTrace c).length

/-- `TermRun.Step` alone, with the empty trace. -/
def ofStep (p : CoreTerm.Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (init : TermRun.Cfg → Prop) :
    SrcSem :=
  ofStepsG p k arch (fun _ _ _ => False) (fun _ => []) init

/-- `TermSpawnStep.StepX` (a machine step or a spawn, thread capacity `cap`)
with the empty trace. -/
def ofSpawn (p : CoreTerm.Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (cap : Nat)
    (init : TermRun.Cfg → Prop) : SrcSem :=
  ofStepsG p k arch (SpawnBy cap) (fun _ => []) init

section Instances

variable {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}
  {Sp : Nat → TermRun.Cfg → TermRun.Cfg → Prop} {obsTrace : TermRun.Cfg → List Ev} {init : TermRun.Cfg → Prop}

/-- The runs of `ofStepsG` are WeakCore's `StepsG` runs. -/
theorem ofStepsG_run_stepsG {c c' : TermRun.Cfg} {tr : List Ev}
    (h : (ofStepsG p k arch Sp obsTrace init).Run c tr c') :
    TermSpawnStep.StepsG p k arch (fun c c' => ∃ i, Sp i c c') c c' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    obtain ⟨i, hs, -⟩ := hs
    exact .step (hs.imp StepBy.step fun h => ⟨i, h⟩) ih

/-- If the observable trace only grows along steps, a run's trace is its
growth. -/
theorem ofStepsG_run_trace
    (hmono : ∀ i c c', (StepBy p k arch i c c' ∨ Sp i c c') → obsTrace c <+: obsTrace c')
    {c c' : TermRun.Cfg} {tr : List Ev} (h : (ofStepsG p k arch Sp obsTrace init).Run c tr c') :
    obsTrace c' = obsTrace c ++ tr := by
  induction h with
  | refl => simp
  | step hs _ ih =>
    obtain ⟨i, hst, rfl⟩ := hs
    rw [ih, ← List.append_assoc, List.prefix_iff_eq_append.mp (hmono _ _ _ hst)]

/-- The runs of `ofSpawn` are WeakCore's `StepsX` runs. -/
theorem ofSpawn_run_stepsX {cap : Nat} {c c' : TermRun.Cfg} {tr : List Ev}
    (h : (ofSpawn p k arch cap init).Run c tr c') : TermSpawnStep.StepsX p k arch cap c c' :=
  (ofStepsG_run_stepsG h).mono fun _ _ ⟨_, hs⟩ => hs.spawn

/-- The runs of `ofStep` are runs of `TermRun.Step` alone (`StepsG` with no
extra steps). -/
theorem ofStep_run_stepsG {c c' : TermRun.Cfg} {tr : List Ev}
    (h : (ofStep p k arch init).Run c tr c') : TermSpawnStep.StepsG p k arch (fun _ _ => False) c c' :=
  (ofStepsG_run_stepsG h).mono fun _ _ ⟨_, hs⟩ => hs

end Instances

/-- A configuration with no threads takes no `TermRun.Step`. -/
theorem no_step_of_no_threads {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}
    {c c' : TermRun.Cfg} (h : c.ths = #[]) : ¬ TermRun.Step p k arch c c' := by
  intro hs
  cases hs with
  | thread i hm _ =>
    simp [TermRun.threadSteps, h] at hm
  | prom i _ _ _ hi _ _ =>
    simp [h] at hi

/-- A configuration with no threads takes no `StepBy` step. -/
theorem no_stepBy_of_no_threads {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}
    {i : Nat} {c c' : TermRun.Cfg} (h : c.ths = #[]) : ¬ StepBy p k arch i c c' :=
  fun hs => no_step_of_no_threads h hs.step

/-- The `main` start configuration of a program whose setup block is empty:
one thread entering `main` on a unit argument, empty memory, no labels
allocated before the run. -/
def mainStart : TermRun.Cfg where
  mem := #[]
  ths := #[{ term := .tail "main" [] (.var "a") [], env := [("a", .unit, [])] }]

/-! ## The source instance

`source P p` is WeakCore's machine for program `p`: `TermRun.Step` and
`TermSpawnStep.Spawn` (thread capacity `P.cap`), beside the extern step,
which WeakCore does not have yet and which is therefore a hook
(`SrcHooks`, in the style of the target's `Hooks`), empty in
`SrcHooks.none`. Each step is labelled with the growth of `srcObs` of the
hook's event list. -/

/-- **The source's extern hook**: the parts of WeakCore's extern design
(not yet in the tree) the source instance needs. Each is an explicit field;
nothing here gives it a meaning. -/
structure SrcHooks where
  /-- An extern configuration step of thread `i` (`emit b`, `exitEv n`). -/
  ext : Nat → TermRun.Cfg → TermRun.Cfg → Prop
  /-- The configuration's append-only event list (WeakCore's `Cfg.trace`,
  `out b ↦ Ev.out b`, `exit n ↦ Ev.exit (n % 256)`). -/
  trace : TermRun.Cfg → List Ev

/-- No extern step and the empty event list: the source is WeakCore's
machine as it is today, whose only observable event is `main`'s exit. -/
def SrcHooks.none : SrcHooks := ⟨fun _ _ _ => False, fun _ => []⟩

/-- **The parameters of the source instance**: WeakCore's knobs (all on),
the memory model of the target architecture (`arm` for AArch64, `tso` for
x64), the thread capacity of `Spawn`, the start configurations (the state
after the setup block), and the extern hook. The capacity bounds the source
threads: it must be at least the target's thread slots (a target spawn needs
a source spawn), and above `B.threads` for a `threads` abort to be
justifiable (the spawn that crosses the part must exist). -/
structure SrcParams where
  k : Promises.Knobs := Promises.Knobs.all
  arch : WeakMem.Arch
  cap : Nat
  init : TermRun.Cfg → Prop
  hooks : SrcHooks := SrcHooks.none

/-- The start of a program with an empty setup block (`mainStart`), its
label stripe width at the thread capacity `cap` (`TermRun.Cfg.cap`, so that
`Cfg.n` is constant along runs with spawns). -/
def mainInit (cap : Nat) : TermRun.Cfg → Prop := (· = { mainStart with cap := cap })

/-- The ungated steps of `source P p`: `ofStepsG` with the extra step "a
spawn by thread `i` (`SpawnBy P.cap i`) or an extern step of `i`" and the
observable trace `srcObs P.hooks.trace`. -/
def sourceG (P : SrcParams) (p : CoreTerm.Prog) : SrcSem :=
  ofStepsG p P.k P.arch (fun i c c' => SpawnBy P.cap i c c' ∨ P.hooks.ext i c c') (srcObs P.hooks.trace) P.init

/-- **The source machine of program `p`**: the steps of `sourceG P p`, but
no thread steps once `main` has returned (`mainExit c ≠ []`): the process
has exited (the target's `exit_group`), so no event follows `main`'s exit
(P9, `source_run_trace`). The gate is on configurations and
excludes no program. Its runs are WeakCore's `StepsG p P.k P.arch
(Spawn ∨ ext)` runs (`source_run_stepsG`). -/
def source (P : SrcParams) (p : CoreTerm.Prog) : SrcSem where
  Cfg := TermRun.Cfg
  core := id
  init := P.init
  step i c es c' := mainExit c = [] ∧ (sourceG P p).step i c es c'

/-- A run of `source P p` is a run of `sourceG P p` (drop the gate). -/
theorem source_run_sourceG {P : SrcParams} {p : CoreTerm.Prog} {c c' : TermRun.Cfg} {tr : List Ev}
    (h : (source P p).Run c tr c') : (sourceG P p).Run c tr c' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    obtain ⟨i, -, hs⟩ := hs
    exact .step ⟨i, hs⟩ ih

/-- **The runs of `source P p` are WeakCore's `StepsG` runs** with extra step
"a spawn or an extern step". -/
theorem source_run_stepsG {P : SrcParams} {p : CoreTerm.Prog} {c c' : TermRun.Cfg} {tr : List Ev}
    (h : (source P p).Run c tr c') :
    TermSpawnStep.StepsG p P.k P.arch (fun c c' => ∃ i, SpawnBy P.cap i c c' ∨ P.hooks.ext i c c') c c' :=
  ofStepsG_run_stepsG (source_run_sourceG h)

/-! ## The observable trace only grows (P9)

`srcObs tr c` is `cutAtExit (tr c ++ mainExit c)`. With no extern step
(`SrcHooks.none`) it is `mainExit c` cut, which is `[]` until thread 0 has
returned with an empty stack and constant afterwards: a finished thread
takes no thread step (`tstep` has no case for `ret` with an empty stack), a
promise of thread 0 changes only its promises, another thread's step or
spawn changes only its own slot (and appends the child), and thread 0 at
`ret` is at no spawn site. So even the trace of a run of the ungated
`sourceG P p` with no extern step is the growth of `srcObs` (`srcObs_mono`).

With an extern hook the same holds if the event list only grows along steps
and no longer grows once `main` has returned (`srcObs_mono`). The second
condition is not automatic: if other threads could still emit after `main`'s
return, `mainExit` would no longer be at the end of the trace
(`[out 1, exit 0]` becoming `[out 1, out 2, exit 0]`), and the trace would
not be the growth. The process exits when `main` returns (the target's
`exit_group`), so `source` gates every step on thread 0 not being finished:
then only the first condition is needed (`source_obs_mono`,
`source_run_trace`), for every hook. -/

/-- What `mainExit` reads: thread 0's term, stack and environment. -/
def mainView (c : TermRun.Cfg) : Option (CoreTerm.Expr × List TermRun.Frame × TermRun.Env) :=
  c.ths[0]?.map fun th => (th.term, th.stack, th.env)

theorem mainExit_congr {c c' : TermRun.Cfg} (h : mainView c' = mainView c) : mainExit c' = mainExit c := by
  unfold mainView at h
  unfold mainExit
  cases h0 : c.ths[0]? <;> cases h1 : c'.ths[0]? <;> simp_all

/-- A non-empty `mainExit`: thread 0 has finished. -/
theorem mainExit_done {c : TermRun.Cfg} (h : mainExit c ≠ []) :
    ∃ th a, c.ths[0]? = some th ∧ th.term = .ret a ∧ th.stack = [] := by
  unfold mainExit at h
  split at h
  · rename_i th h0
    split at h
    · rename_i _ _ a ht hs
      exact ⟨th, a, h0, ht, hs⟩
    · exact absurd rfl h
  · exact absurd rfl h

/-- A finished thread takes no thread step. -/
theorem tstep_ret_nil {g : TermRun.G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TermRun.TTh}
    {a : CoreTerm.At} (ht : th.term = .ret a) (hs : th.stack = []) : TermRun.tstep g mem pairs th = [] := by
  simp [TermRun.tstep, ht, hs]

theorem getElem?_set!_ne {α : Type} {ths : Array α} {i j : Nat} {x : α} (h : i ≠ j) :
    (ths.set! i x)[j]? = ths[j]? := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [h]

/-- **Once `main` has returned, no step of WeakCore's machine (thread step,
promise, spawn) changes what `mainExit` reads.** -/
theorem mainView_step {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap i : Nat}
    {c c' : TermRun.Cfg} (hd : mainExit c ≠ []) (hs : StepBy p k arch i c c' ∨ SpawnBy cap i c c') :
    mainView c' = mainView c := by
  obtain ⟨th0, a, h0, ht, hst⟩ := mainExit_done hd
  rcases hs with (⟨hm, -⟩ | ⟨a', v, w, -, -, -, rfl⟩) | ⟨x, f, a', T, ts, e, th, rt, ws, h1, h2, -, -, -, rfl⟩
  · unfold TermRun.threadSteps at hm
    split at hm
    · simp at hm
    · rename_i thi hi
      obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := List.mem_map.mp hm
      by_cases hi0 : i = 0
      · subst hi0
        rw [h0] at hi
        cases hi
        rw [tstep_ret_nil ht hst] at hr
        simp at hr
      · simp [mainView, Array.set!_eq_setIfInBounds, hi0]
  · unfold TermRun.promise
    split
    · rfl
    · rename_i thi hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [h0] at hi
        cases hi
        simp [mainView, h0, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        exact fun h => by simp [h] at h0
      · simp [mainView, Array.set!_eq_setIfInBounds, hi0]
  · by_cases hi0 : i = 0
    · subst hi0
      rw [h0] at h1
      cases h1
      rw [ht] at h2
      cases h2
    · have hlt : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp h0).1
      simp only [mainView, TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, Array.getElem?_push,
        Array.size_set!, getElem?_set!_ne hi0]
      simp [show (0 : Nat) ≠ c.ths.size by omega]

/-- A step of WeakCore's machine keeps the number of threads (`threadSteps`
and `promise` replace one slot). -/
theorem stepBy_size {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat}
    {c c' : TermRun.Cfg} (hs : StepBy p k arch i c c') : c'.ths.size = c.ths.size := by
  rcases hs with ⟨hm, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
  · unfold TermRun.threadSteps at hm
    split at hm
    · simp at hm
    · obtain ⟨⟨mem, pairs, th'⟩, -, rfl⟩ := List.mem_map.mp hm
      simp
  · unfold TermRun.promise
    split <;> simp

/-- A spawn adds one thread, below the capacity. -/
theorem spawnBy_size {cap i : Nat} {c c' : TermRun.Cfg} (hs : SpawnBy cap i c c') :
    c'.ths.size = c.ths.size + 1 ∧ c.ths.size < cap := by
  obtain ⟨x, f, a, T, ts, e, th, rt, ws, -, -, -, hlt, -, rfl⟩ := hs
  simp [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, hlt]

/-- `cutAtExit` is monotone in the trace. -/
theorem cutAtExit_append (l m : List Ev) : cutAtExit l <+: cutAtExit (l ++ m) := by
  induction l with
  | nil => exact List.nil_prefix
  | cons e es ih =>
    cases e with
    | exit c => exact List.prefix_refl _
    | _ => simpa [cutAtExit] using ih

/-- **P9, general form**: `srcObs tr` only grows along a step of WeakCore's
machine or an extra step `Sp`, if the event list `tr` only grows along the
step, does not grow once `main` has returned, and `Sp` keeps what
`mainExit` reads once `main` has returned. -/
theorem srcObs_mono {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap i : Nat}
    {Sp : Nat → TermRun.Cfg → TermRun.Cfg → Prop} {tr : TermRun.Cfg → List Ev} {c c' : TermRun.Cfg}
    (hs : StepBy p k arch i c c' ∨ SpawnBy cap i c c' ∨ Sp i c c') (hgrow : tr c <+: tr c')
    (hfrz : mainExit c ≠ [] → tr c' = tr c)
    (hsp : Sp i c c' → mainExit c ≠ [] → mainView c' = mainView c) :
    srcObs tr c <+: srcObs tr c' := by
  unfold srcObs
  by_cases hd : mainExit c = []
  · rw [hd, List.append_nil]
    obtain ⟨d, hd'⟩ := hgrow
    rw [← hd', List.append_assoc]
    exact cutAtExit_append _ _
  · have hv : mainView c' = mainView c := by
      rcases hs with hs | hs | hs
      · exact mainView_step (cap := cap) hd (.inl hs)
      · exact mainView_step (p := p) (k := k) (arch := arch) hd (.inr hs)
      · exact hsp hs hd
    rw [hfrz hd, mainExit_congr hv]
    exact List.prefix_refl _

/-- **P9 for the source instance**: `srcObs` only grows along every step of
`source P p`, for every hook whose event list only grows along the steps
(`SrcHooks.none` included). A step starts where `main` has not returned
(the gate), so `srcObs c` is `cutAtExit` of the event list, a prefix of
`cutAtExit` of the longer list at `c'`. -/
theorem source_obs_mono {p : CoreTerm.Prog} {P : SrcParams}
    (hgrow : ∀ i c c', StepBy p P.k P.arch i c c' ∨ SpawnBy P.cap i c c' ∨ P.hooks.ext i c c' →
      P.hooks.trace c <+: P.hooks.trace c')
    {i : Nat} {c c' : TermRun.Cfg} {es : List Ev} (hs : (source P p).step i c es c') :
    srcObs P.hooks.trace c <+: srcObs P.hooks.trace c' := by
  obtain ⟨hd, hst, -⟩ := hs
  unfold srcObs
  rw [hd, List.append_nil]
  obtain ⟨d, hd'⟩ := hgrow _ _ _ hst
  rw [← hd', List.append_assoc]
  exact cutAtExit_append _ _

/-- **The trace of a run of `source P p` is the growth of its observable
trace**, for every hook whose event list only grows along the steps. -/
theorem source_run_trace {p : CoreTerm.Prog} {P : SrcParams}
    (hgrow : ∀ i c c', StepBy p P.k P.arch i c c' ∨ SpawnBy P.cap i c c' ∨ P.hooks.ext i c c' →
      P.hooks.trace c <+: P.hooks.trace c')
    {c c' : TermRun.Cfg} {tr : List Ev}
    (h : (source P p).Run c tr c') : srcObs P.hooks.trace c' = srcObs P.hooks.trace c ++ tr := by
  induction h with
  | refl => simp
  | step hs _ ih =>
    obtain ⟨i, hst⟩ := hs
    have hm := source_obs_mono hgrow hst
    obtain ⟨-, -, rfl⟩ := hst
    rw [ih, ← List.append_assoc, List.prefix_iff_eq_append.mp hm]

/-- `SrcHooks.none`'s event list only grows (it is constant). -/
theorem grow_none {p : CoreTerm.Prog} {P : SrcParams} (hP : P.hooks = SrcHooks.none) :
    ∀ i c c', StepBy p P.k P.arch i c c' ∨ SpawnBy P.cap i c c' ∨ P.hooks.ext i c c' →
      P.hooks.trace c <+: P.hooks.trace c' := by
  rw [hP]
  exact fun _ _ _ _ => List.prefix_refl _

/-- **`cutAtExit` ends at its first exit**: nothing follows an exit in it. -/
theorem cutAtExit_exit_last {l pre rest : List Ev} {c : Fin 256}
    (h : cutAtExit l = pre ++ .exit c :: rest) : rest = [] := by
  induction l generalizing pre with
  | nil => simp [cutAtExit] at h
  | cons e es ih =>
    cases e with
    | exit c' =>
      cases pre with
      | nil => simp [cutAtExit] at h; exact h.2
      | cons x xs => simp [cutAtExit] at h
    | _ =>
      cases pre with
      | nil => simp [cutAtExit] at h
      | cons x xs =>
        simp only [cutAtExit, List.cons_append, List.cons.injEq] at h
        exact ih h.2

/-! ## `main`'s exit and outstanding promises

`mainExit` fires when thread 0 is at `ret` with an empty stack, whatever its
promise set. That never matters on a reachable configuration: thread 0
reaches `ret` only by a step after which it is certified (`TermRun.Step`
certifies the stepping thread), and a finished thread can only add promises
in a solo run (`solo_done`), so it is certified only with none
(`certified_done`); later steps of other threads leave its slot alone, and
it takes no promise step (that would need certification again). So on every
reachable configuration of `source P p` where `main` has returned, thread 0
has no outstanding promise (`source_mainExit_noProm`), and the target's exit
at `main`'s return is matched by a source configuration whose own steps
were all certified. Other threads may still have promises there; they are
never fulfilled, which nothing observes (`Scc/DESIGN.md` §3, K5). -/

/-- Thread 0, if finished, has no outstanding promise. -/
def MainDoneNoProm (c : TermRun.Cfg) : Prop :=
  ∀ th, c.ths[0]? = some th → TermRun.isDone th = true → th.promises = []

/-- A finished thread takes no thread step. -/
theorem tstep_isDone {g : TermRun.G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TermRun.TTh}
    (h : TermRun.isDone th = true) : TermRun.tstep g mem pairs th = [] := by
  cases ht : th.term <;> cases hs : th.stack <;> simp [TermRun.isDone, ht, hs] at h <;>
    simp [TermRun.tstep, ht, hs]

/-- **A solo run of a finished thread 0 only adds promises.** -/
theorem solo_done {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c'' : TermRun.Cfg}
    (h : TermRun.Solo p k arch 0 c c'') :
    ∀ th, c.ths[0]? = some th → TermRun.isDone th = true →
      ∃ th'', c''.ths[0]? = some th'' ∧ th.promises <+: th''.promises := by
  induction h with
  | refl => intro th h _; exact ⟨th, h, List.prefix_refl _⟩
  | thread hm _ _ =>
    intro th h hd
    unfold TermRun.threadSteps at hm
    simp [h, tstep_isDone hd] at hm
  | ext hm _ _ =>
    intro th h hd
    obtain ⟨th0, _, _, _, _, _, _, _, h0, ht, _⟩ := TermRun.extSteps_elim hm
    rw [h] at h0; cases h0
    simp [TermRun.isDone, ht] at hd
  | @prom c0 _ a v w _ _ ih =>
    intro th h hd
    have hlt : 0 < _ := (Array.getElem?_eq_some_iff.mp h).1
    obtain ⟨th'', h'', hp⟩ := ih { th with promises := th.promises ++ [c0.mem.size] }
      (by unfold TermRun.promise; rw [h]; simp [Array.set!_eq_setIfInBounds, hlt])
      (by simpa [TermRun.isDone] using hd)
    exact ⟨th'', h'', (List.prefix_append _ _).trans hp⟩

/-- **A finished thread 0 is certified only with no promises.** -/
theorem certified_done {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c : TermRun.Cfg}
    {th : TermRun.TTh} (hc : TermRun.Certified p k arch c 0) (h : c.ths[0]? = some th)
    (hd : TermRun.isDone th = true) : th.promises = [] := by
  obtain ⟨c'', hs, hn⟩ := hc
  obtain ⟨th'', h'', hp⟩ := solo_done hs th h hd
  simp [TermRun.noPromises, h''] at hn
  rw [hn] at hp
  exact List.prefix_nil.mp hp

/-- A step or spawn of a thread other than 0 leaves slot 0 alone. -/
theorem slot0_step {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap i : Nat}
    {c c' : TermRun.Cfg} (hi0 : i ≠ 0) (hs : StepBy p k arch i c c' ∨ SpawnBy cap i c c') :
    c'.ths[0]? = c.ths[0]? := by
  rcases hs with (⟨hm, -⟩ | ⟨a', v, w, -, -, -, rfl⟩) | ⟨x, f, a', T, ts, e, th, rt, ws, h1, -, -, -, -, rfl⟩
  · unfold TermRun.threadSteps at hm
    split at hm
    · simp at hm
    · obtain ⟨⟨mem, pairs, th'⟩, -, rfl⟩ := List.mem_map.mp hm
      simp [Array.set!_eq_setIfInBounds, hi0]
  · unfold TermRun.promise
    split
    · rfl
    · simp [Array.set!_eq_setIfInBounds, hi0]
  · have hlt : i < c.ths.size := (Array.getElem?_eq_some_iff.mp h1).1
    simp only [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, Array.getElem?_push, Array.size_set!,
      getElem?_set!_ne hi0]
    simp [show (0 : Nat) ≠ c.ths.size by omega]

/-- **`MainDoneNoProm` is preserved by WeakCore's steps and spawns.** -/
theorem mainDoneNoProm_step {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap i : Nat}
    {c c' : TermRun.Cfg} (H : MainDoneNoProm c) (hs : StepBy p k arch i c c' ∨ SpawnBy cap i c c') :
    MainDoneNoProm c' := by
  by_cases hi0 : i = 0
  · subst hi0
    intro th' h' hd
    rcases hs with (⟨-, hc⟩ | ⟨a, v, w, -, -, hc, rfl⟩) | ⟨x, f, a, T, ts, e, th, rt, ws, h1, -, hp, -, -, rfl⟩
    · exact certified_done hc h' hd
    · exact certified_done hc h' hd
    · have hlt : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp h1).1
      rw [show (TermSpawnStep.spawnCfg c 0 th x e f ts T ws).ths[0]? = some (TermSpawnStep.spawnPar c 0 th x e)
        from ?_] at h'
      · cases h'
        simp [TermSpawnStep.spawnPar, TermRun.withS, TermSpawnStep.spawnS, TermRun.fenceS, TermRun.stOf, hp]
      · simp only [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, Array.getElem?_push, Array.size_set!]
        rw [ite_eq_right (by omega)]
        simp [Array.set!_eq_setIfInBounds, hlt]
  · rw [MainDoneNoProm, slot0_step hi0 hs]
    exact H

/-- **On every reachable configuration of the source, a finished thread 0
has no outstanding promise**, if that holds at the start (it does at
`mainInit`, `mainInit_noProm`) and an extern step from a configuration where
`main` has not returned does not finish thread 0 with promises (`hext`;
vacuous for `SrcHooks.none`, `ext_none`). The gate does not give `hext`:
it stops steps after `main`'s return, but the hook is an arbitrary relation
and could finish thread 0 in one step. -/
theorem source_mainDoneNoProm {p : CoreTerm.Prog} {P : SrcParams}
    (hext : ∀ i c c', P.hooks.ext i c c' → mainExit c = [] → MainDoneNoProm c → MainDoneNoProm c')
    (hinit : ∀ c, P.init c → MainDoneNoProm c) {tr : List Ev} {s : TermRun.Cfg}
    (h : (source P p).Reach tr s) : MainDoneNoProm s := by
  obtain ⟨s0, h0, hr⟩ := h
  have H := hinit s0 h0
  clear h0
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, hd, hs, -⟩ := hs
    apply ih
    rcases hs with hs | hs | hs
    · exact mainDoneNoProm_step (cap := 0) H (.inl hs)
    · exact mainDoneNoProm_step (p := p) (k := P.k) (arch := P.arch) H (.inr hs)
    · exact hext _ _ _ hs hd H

/-- `SrcHooks.none` has no extern step. -/
theorem ext_none {P : SrcParams} (hP : P.hooks = SrcHooks.none) :
    ∀ i c c', P.hooks.ext i c c' → mainExit c = [] → MainDoneNoProm c → MainDoneNoProm c' := by
  rw [hP]
  exact fun _ _ _ h => h.elim

/-- At `mainInit`, thread 0 is entering `main`, not finished. -/
theorem mainInit_noProm (cap : Nat) : ∀ c, mainInit cap c → MainDoneNoProm c := by
  rintro c rfl th h hd
  simp [mainStart] at h
  subst h
  simp [TermRun.isDone] at hd

/-- **Where `main`'s exit fires, thread 0 has no outstanding promise**, on
every reachable configuration of the source (extern steps as in
`source_mainDoneNoProm`). -/
theorem source_mainExit_noProm {p : CoreTerm.Prog} {P : SrcParams}
    (hext : ∀ i c c', P.hooks.ext i c c' → mainExit c = [] → MainDoneNoProm c → MainDoneNoProm c')
    (hinit : ∀ c, P.init c → MainDoneNoProm c) {tr : List Ev} {s : TermRun.Cfg}
    (h : (source P p).Reach tr s) (hx : mainExit s ≠ []) :
    ∃ th, s.ths[0]? = some th ∧ th.promises = [] := by
  obtain ⟨th, a, h0, ht, hst⟩ := mainExit_done hx
  exact ⟨th, h0, source_mainDoneNoProm hext hinit h th h0 (by simp [TermRun.isDone, ht, hst])⟩

end SrcSem

end Scc.Sem
