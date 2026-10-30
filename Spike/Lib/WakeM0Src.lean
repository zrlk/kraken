/-
**Source steps of `main` after the spawn** (`post_step0`). ISA-generic; the thread-0 twins of `Spike/Lib/WorkerSrcStep.lean`.

A step of thread 0 may change `mainExit`, so the source machine's gate and
the observation at each step are about thread 0 itself: before a local step
`main` has not returned (a `ret` on an empty stack has no `tstep`), and the
caller supplies `mainExit = []` at the end of the run.

- `source_step_nil'`: `source_step_nil` with `mainExit s' = []` in place of
  thread 0 kept.
- `mainExit_of_localStepS`: a thread 0 at a control with a local step has
  not returned.
- `localRunS_run_source_0`: a local run of thread 0 on one frame with no
  promise, `main` not returned at its end, is a source run with the empty
  trace.
-/
import Spike.Lib.WorkerSrcStep

namespace Spike.Lib.WakeM0Src

open CoreLang CoreTerm TermRun
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto TermExtStep
open Spike.Lib Spike.Lib.WorkerSrcStep

variable {P : SrcParams} {p : Prog}

/-- **A silent step of thread `i`** under WeakCore's hook, before and after
which `main` has not returned and which keeps the event list, is a source
step with the empty trace. -/
theorem source_step_nil' (hP : UsesWc P p) {s s' : Cfg} {i : Nat}
    (hst : StepBy p P.k P.arch i s s' ∨ P.hooks.ext i s s') (hex : mainExit s = []) (hex' : mainExit s' = [])
    (htr : s'.trace = s.trace) :
    (source P p).step i s [] s' := by
  refine ⟨hex, hst.imp_right Or.inr, ?_⟩
  have e2 : P.hooks.trace s' = P.hooks.trace s := by rw [hP]; simp only [wcHooks, traceOf, htr]
  simp only [srcObs, hex, hex', List.append_nil, e2, List.drop_length]

/-- **Before a local step `main` has not returned**: thread 0 at a control
with a local step is not at a `ret` on an empty stack. -/
theorem mainExit_of_localStepS {c c₁ : Ctl} (hs : LocalStepS p c c₁) {g : G} (hg : g.p = p) {s : Cfg} {th : TTh}
    (hi : s.ths[0]? = some th) (ht : th.term = c.term) (he : th.env = c.env) (hσ : th.σs = []) :
    mainExit s = [] := by
  unfold mainExit
  rw [hi]
  simp only
  split
  · rename_i a htm hst
    have h := hs.2 g s.mem s.pairs th hg ht he hσ
    simp [TermRun.tstep, htm, hst] at h
  · rfl

/-- **A local run of thread 0** on one frame with no promise, `main` not
returned at its end, is a source run with the empty trace. -/
theorem localRunS_run_source_0 (hP : UsesWc P p) {c c' : Ctl} (h : LocalRunS p c c') :
    ∀ {s : Cfg} {th : TTh}, s.ths[0]? = some th → th.term = c.term → th.env = c.env → th.σs = [] →
      th.stack = [] → th.promises = [] →
      mainExit { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } = [] →
      (source P p).Run s [] { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } := by
  induction h with
  | refl c =>
    intro s th hi ht he _ _ _ _
    have e1 : { th with term := c.term, env := c.env } = th := by rw [← ht, ← he]
    have e2 : s.ths.set! 0 th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [e1, e2]
    exact .refl _
  | @step c c₁ c' hs hr ih =>
    intro s th hi ht he hσ hk hp hex'
    let th₁ : TTh := { th with term := c₁.term, env := c₁.env }
    have hi' : ({ s with ths := s.ths.set! 0 th₁ } : Cfg).ths[0]? = some th₁ := getElem?_set!_self hi th₁
    have hex : mainExit s = [] := mainExit_of_localStepS hs (g := gOf p P.k P.arch s 0) rfl hi ht he hσ
    have h2 := ih (s := { s with ths := s.ths.set! 0 th₁ }) hi' rfl rfl hσ hk hp
      (by simp only [th₁, set!_set!]; exact hex')
    simp only [th₁, set!_set!] at h2
    have hex₁ : mainExit { s with ths := s.ths.set! 0 th₁ } = [] := by
      cases hr with
      | refl => simpa [th₁] using hex'
      | step hs' _ => exact mainExit_of_localStepS hs' (g := gOf p P.k P.arch s 0) rfl hi' rfl rfl hσ
    have h1 : (source P p).step 0 s [] { s with ths := s.ths.set! 0 th₁ } :=
      source_step_nil' hP (.inl (.inl ⟨SrcMem.mem_threadSteps (mem' := s.mem) (pairs' := s.pairs) hi
        (by rw [hs.2 _ _ _ _ rfl ht he hσ]; exact List.mem_singleton.mpr rfl),
        certified_nil hi' (by simpa [th₁] using hp)⟩)) hex hex₁ rfl
    exact LRun.step ⟨0, h1⟩ h2

/-- info: 'Spike.Lib.WakeM0Src.localRunS_run_source_0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localRunS_run_source_0

end Spike.Lib.WakeM0Src
