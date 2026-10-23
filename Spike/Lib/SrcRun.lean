/-
**Local runs of thread 0 under the source instance** (`SrcSem.source P p`,
the source `Scc.Correct` states), with no extern step
(`P.hooks = SrcHooks.none`): the analogue of `Spike.Lib.LocalRun.run`
(stated for `SrcSem.ofStep`) under `source`'s gate (no step once `main` has
returned, `mainExit`) and observable trace (`main`'s exit).

- `localStep_not_ret`: a thread at `ret` with one frame takes no local step.
- `mainExit_of_not_ret`: thread 0 not at `ret` (one frame): `main` has not
  returned.
- `LocalRun.run_source`: a local run of thread 0 (one frame, no promises),
  from a control not at `ret`, is a run of `source P p` whose trace is the
  `mainExit` of the configuration it lands in: empty unless the run ends at
  `main`'s `ret` (`run_source_nil`), and then `main`'s exit event (the
  target's `exit_group`).
-/
import Spike.Lib.Src

namespace Spike.Lib

open CoreLang CoreTerm
open Scc.Sem (SrcSem)
open Scc.Sem.SrcSem (mainExit srcObs cutAtExit)

variable {p : Prog}

/-- **A thread at `ret` with one frame takes no local step**: `tstep` has
no outcome there. -/
theorem localStep_not_ret {c c₁ : Ctl} (h : LocalStep p c c₁) : ∀ a, c.term ≠ .ret a := by
  intro a hc
  have := h.2 { p := p, k := Promises.Knobs.all, arch := .arm, n := 0, i := 0, lbase := 0 } #[] []
    { term := c.term, env := c.env } rfl rfl rfl rfl rfl
  simp [TermRun.tstep, hc] at this

/-- **`main` has not returned** while thread 0, with one frame, is not at
`ret`. -/
theorem mainExit_of_not_ret {s : TermRun.Cfg} {th : TermRun.TTh} (h0 : s.ths[0]? = some th)
    (hr : ∀ a, th.term ≠ .ret a) : mainExit s = [] := by
  unfold mainExit
  rw [h0]
  simp only
  split <;> simp_all

/-- `main`'s exit is cut at itself. -/
theorem cutAtExit_mainExit (s : TermRun.Cfg) : cutAtExit (mainExit s) = mainExit s := by
  unfold mainExit
  repeat' split
  all_goals rfl

variable {P : SrcSem.SrcParams}

/-- **A local run of thread 0 under the source instance**: from a control
not at `ret`, with one frame and no promises, a local run is a run of
`source P p` with `main`'s exit at the landing configuration as its trace
(each step certified by the empty solo run; `main` returns at most at the
last step, a thread at `ret` taking no local step). -/
theorem LocalRun.run_source (hP : P.hooks = SrcSem.SrcHooks.none) {c c' : Ctl} (h : LocalRun p c c') :
    ∀ {s : TermRun.Cfg} {th : TermRun.TTh}, s.ths[0]? = some th → th.term = c.term → th.env = c.env →
      th.σs = [] → th.stack = [] → th.promises = [] → (∀ a, c.term ≠ .ret a) →
      (SrcSem.source P p).Run s
        (mainExit { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } })
        { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } := by
  induction h with
  | refl c =>
    intro s th hi ht he _ hst _ hr
    have : { th with term := c.term, env := c.env } = th := by rw [← ht, ← he]
    rw [this]
    have hs : s.ths.set! 0 th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [hs, show ({ s with ths := s.ths } : TermRun.Cfg) = s from rfl,
      mainExit_of_not_ret hi (fun a h => hr a (ht ▸ h))]
    exact .refl _
  | @step c c₁ c' hs hrun ih =>
    intro s th hi ht he hσ hst hp hr
    have hm := hs.mem_threadSteps (k := P.k) (arch := P.arch) hi ht he hσ hst
    have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
    have hi' : ({ s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } : TermRun.Cfg).ths[0]? =
        some { th with term := c₁.term, env := c₁.env } := by
      simp [hlt]
    have hex0 : mainExit s = [] := mainExit_of_not_ret hi (fun a h => hr a (ht ▸ h))
    have hstep : ∀ es, es = mainExit { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } →
        (SrcSem.source P p).step 0 s es { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } := by
      intro es hes
      refine ⟨hex0, .inl (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), ?_⟩
      · simp [TermRun.noPromises, hlt, hp]
      · simp only [srcObs, hP, SrcSem.SrcHooks.none, List.nil_append, hex0, cutAtExit,
          List.length_nil, List.drop_zero, cutAtExit_mainExit, hes]
    by_cases hr₁ : ∀ a, c₁.term ≠ .ret a
    · have h2 := ih hi' rfl rfl hσ hst hp hr₁
      simp only [set!_set!] at h2
      have hnil : mainExit { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } = [] :=
        mainExit_of_not_ret hi' hr₁
      have h1 : (SrcSem.source P p).Run s ([] ++ [])
          { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } :=
        Scc.Sem.LRun.step ⟨0, hstep [] hnil.symm⟩ (.refl _)
      exact Scc.Sem.LRun.trans h1 h2
    · -- `c₁` is at `ret`: the rest of the run is empty.
      have hc' : c' = c₁ := by
        cases hrun with
        | refl => rfl
        | step hs' _ => exact absurd (localStep_not_ret hs') hr₁
      subst hc'
      have h1 : (SrcSem.source P p).Run s
          (mainExit { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } ++ [])
          { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } :=
        Scc.Sem.LRun.step ⟨0, hstep _ rfl⟩ (.refl _)
      rwa [List.append_nil] at h1

/-- **A local run of thread 0 that does not end at `ret`** is a run of
`source P p` with the empty trace. -/
theorem LocalRun.run_source_nil (hP : P.hooks = SrcSem.SrcHooks.none) {c c' : Ctl} (h : LocalRun p c c')
    {s : TermRun.Cfg} {th : TermRun.TTh} (hi : s.ths[0]? = some th) (ht : th.term = c.term) (he : th.env = c.env)
    (hσ : th.σs = []) (hst : th.stack = []) (hp : th.promises = []) (hr : ∀ a, c.term ≠ .ret a)
    (hr' : ∀ a, c'.term ≠ .ret a) :
    (SrcSem.source P p).Run s [] { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } := by
  have h1 := h.run_source hP hi ht he hσ hst hp hr
  have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  rwa [mainExit_of_not_ret (th := { th with term := c'.term, env := c'.env }) (by simp [hlt]) hr'] at h1

end Spike.Lib
