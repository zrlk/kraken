/-
**Prototype: the source with WeakCore's extern step** (design spike, not
part of the statement). `Scc/Sem/SrcExt.lean`'s `source P p` takes its
extern step and event list from a hook (`SrcHooks`); every theorem so far
uses `SrcHooks.none`. WeakCore now has the step (`TermExtStep.Ext`: `emit`,
`exitEv`, `current`) and the event list (`TermRun.Cfg.trace`). This file
builds the hook from them and checks that the source's existing results
carry over. The hook and its parts (`evOf`, `traceOf`, `ExtBy`, `wcHooks`)
are the statement's definitions in `Scc/Sem/SrcOut.lean`; this file proves:

- `ExtBy.ext`, `ExtBy.of_ext`: `ExtBy` is `TermExtStep.Ext` with the stepping
  thread exposed.
- `UsesWc P p`: the parameters' hook is `wcHooks` at their own knobs and model.
- `grow_wc`: its event list only grows along every step (P9's premise of
  `source_obs_mono`/`source_run_trace`).
- `ext_wc`: its extern steps keep `MainDoneNoProm` (the premise of
  `source_mainExit_noProm`): a step that finishes thread 0 leaves it
  certified, hence without promises.
- `run_wc`: with the hook, `source`'s runs are WeakCore's `StepsE` runs
  (machine steps, spawns, extern steps).
-/
import Scc.Sem.SrcOut
import WeakCore.ExtArmZ

namespace Scc.Sem.SrcOutProto

open CoreLang CoreTerm TermRun TermExtStep
open Scc.Sem.SrcSem

/-! ## The step, thread-indexed

`evOf`, `traceOf`, `ExtBy` and `wcHooks` are defined in `Scc/Sem/SrcOut.lean`. -/

theorem _root_.Scc.Sem.SrcSem.ExtBy.ext {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat}
    {c c' : Cfg} (h : ExtBy p k arch i c c') : Ext p k arch c c' := by
  obtain ⟨x, n, a, e, th, rt, ws, rs, h1, h2, h3, h4, h5, h6, rfl⟩ := h
  exact .mk i x n a e th rt ws rs h1 h2 h3 h4 h5 h6

theorem _root_.Scc.Sem.SrcSem.ExtBy.of_ext {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}
    {c c' : Cfg} (h : Ext p k arch c c') : ∃ i, ExtBy p k arch i c c' := by
  obtain ⟨i, x, n, a, e, th, rt, ws, rs, h1, h2, h3, h4, h5, h6, rfl⟩ := h.elim
  exact ⟨i, x, n, a, e, th, rt, ws, rs, h1, h2, h3, h4, h5, h6, rfl⟩

/-! ## The hook -/

/-- Parameters whose hook is WeakCore's, at their own knobs and model. -/
def UsesWc (P : SrcParams) (p : Prog) : Prop := P.hooks = wcHooks p P.k P.arch

/-- A machine step keeps the trace. -/
theorem stepBy_trace {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat} {c c' : Cfg}
    (h : StepBy p k arch i c c') : c'.trace = c.trace :=
  ExtArmZ.step_trace h.step

/-- A spawn keeps the trace. -/
theorem spawnBy_trace {cap i : Nat} {c c' : Cfg} (h : SpawnBy cap i c c') : c'.trace = c.trace := by
  obtain ⟨x, f, a, T, ts, e, th, rt, ws, -, -, -, -, -, rfl⟩ := h
  rfl

/-- **P9's premise for WeakCore's hook**: the event list only grows along
every step of `source P p`. -/
theorem grow_wc {P : SrcParams} {p : Prog} (hP : UsesWc P p) :
    ∀ i c c', StepBy p P.k P.arch i c c' ∨ SpawnBy P.cap i c c' ∨ P.hooks.ext i c c' →
      P.hooks.trace c <+: P.hooks.trace c' := by
  rw [hP]
  rintro i c c' (h | h | h)
  · simp only [wcHooks, traceOf, stepBy_trace h]; exact List.prefix_refl _
  · simp only [wcHooks, traceOf, spawnBy_trace h]; exact List.prefix_refl _
  · exact (Ext.frame h.ext).2.2.2.2.2.filterMap _

/-- **The trace of a run of the source with WeakCore's hook is the growth of
its observable trace** (`source_run_trace` at `grow_wc`). -/
theorem run_trace_wc {P : SrcParams} {p : Prog} (hP : UsesWc P p) {c c' : Cfg} {tr : List Ev}
    (h : (source P p).Run c tr c') : srcObs P.hooks.trace c' = srcObs P.hooks.trace c ++ tr :=
  source_run_trace (grow_wc hP) h

/-- **The extern steps keep `MainDoneNoProm`**: thread 0, if the step
finishes it, is certified after the step, so it has no promise
(`certified_done`); another thread's step leaves slot 0 alone. -/
theorem ext_wc {P : SrcParams} {p : Prog} (hP : UsesWc P p) :
    ∀ i c c', P.hooks.ext i c c' → mainExit c = [] → MainDoneNoProm c → MainDoneNoProm c' := by
  rw [hP]
  rintro i c c' ⟨x, n, a, e, th, rt, ws, rs, h1, -, -, -, -, hc, rfl⟩ - H
  have H' : MainDoneNoProm (extCfg c i th x n e ws rs) := by
    by_cases hi0 : i = 0
    · subst hi0
      intro th' h' hd
      exact certified_done hc h' hd
    · intro th' h' hd
      rw [extCfg_ths_ne c th x n e ws rs (Ne.symm hi0)] at h'
      exact H th' h' hd
  intro th' h' hd
  rcases wake_get (extCfg c i th x n e ws rs) i (relView th.vs) n ws 0 with e' | ⟨t0, u, h1', h2'⟩
  · rw [e'] at h'; exact H' th' h' hd
  · rw [h2'] at h'; cases h'; exact H' t0 h1' (by simpa [TermRun.isDone] using hd)

/-- **With WeakCore's hook, the runs of `source P p` are WeakCore's `StepsE`
runs** (machine steps, spawns at capacity `P.cap`, extern steps). -/
theorem run_wc {P : SrcParams} {p : Prog} (hP : UsesWc P p) {c c' : Cfg} {tr : List Ev}
    (h : (source P p).Run c tr c') : TermSpawnStep.StepsG p P.k P.arch
      (fun c c' => TermSpawnStep.Spawn p P.k P.arch P.cap c c' ∨ Ext p P.k P.arch c c') c c' := by
  have h' := source_run_stepsG h
  rw [hP] at h'
  exact h'.mono fun _ _ ⟨i, hs⟩ => hs.elim (fun h => .inl h.spawn) (fun h => .inr h.ext)

end Scc.Sem.SrcOutProto
