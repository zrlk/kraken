/-
**Segments at any call depth**: the source thread's suspended frames next
to the target state and the control, the source runs that call and return
(`FrameRun`), what one instruction does at depth (`OutS`), and segments over
fragments with frames (`SegS`, `SegWS`).

- `LocalStep.toS`, `LocalRun.toS`: a local step (one frame) is a local step
  at any depth (`LocalStepS`, `Spike/Lib/SrcFrames.lean`): it is not at
  `ret` (`localStep_not_ret`), and a frame at the bottom of the stack does
  not change a step off `ret` (`TermSpawnSim.tstep_app_eq`). So every
  segment proved for `main`'s body holds inside a callee unchanged.
- `FrameStep`, `FrameRun`: a source run of one thread with its frames: local
  steps at any depth, a call of a code block with no type arguments (at
  any index arguments, `tstep_call_nil`), a return into the top frame (`tstep_ret`); every frame
  pushed has no type variables. `FrameStep.tstep`: the step's one `tstep`
  successor.
- `FrameRun.run_source`: a frame run of thread 0 (no type variables, no
  promises), from a pair other than `main`'s return, is a run of
  `source P p` (`HookOK P p`, its event list with no exit event) whose
  trace is `main`'s exit at the configuration it lands in
  (`FrameRun.run_source_nil`: empty when it does not end at `main`'s
  return, for every `HookOK` hook; `FrameStep.source_step_obs`,
  `source_step`, `source_step_nil`: one frame step).
- `FragS`, `OutS`, `KOutS`: a fragment with the frames; what one instruction
  does at frames `fs`: a frame run and then an `Out` row under the memory
  side at the frames reached (`OutS.pre`; `OutS.lift`: no run), or a silent
  instruction whose source side is a frame run (`OutS.frame`: a call's
  `bl`); an outside move, after which the source takes a frame run.
- `SegS`, `SegWS`: `Seg`, `SegW` over fragments with frames, every row
  landing with a pending frame run (`Pend`); `SegWS.liftS` (`Seg.liftS`): a
  segment at fixed frames; `SegWS.seq`, `mono_pre`, `mono_post`, `or_pre`,
  `step`; `pre_run`, `post_run`: a frame run before the entry, after the
  exit (a call's, a return's).
- `abortJustified_overflowS`: `abortJustified_overflow` at any depth.
-/
import Spike.Lib.SrcFrames
import Spike.Lib.SegW
import WeakCore.TermSpawnSim

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising
open Scc.Sem (SrcSem Budget AbortJustified NoBigNumT)
open Scc.Sem.SrcSem (mainExit srcObs cutAtExit)

variable {p : Prog}

/-! ## Local steps at any depth -/

/-- **A local step is a local step at any depth**: the one-frame step is
off `ret`, and frames at the bottom of the stack do not change it. -/
theorem LocalStep.toS {c c' : Ctl} (h : LocalStep p c c') : LocalStepS p c c' := by
  refine ⟨h.1, fun g mem pairs th hg ht he hσ => ?_⟩
  have hnr := localStep_not_ret h
  suffices H : ∀ (rs : List TermRun.Frame) (th : TermRun.TTh), th.stack = rs.reverse → th.term = c.term →
      th.env = c.env → th.σs = [] →
      TermRun.tstep g mem pairs th = [(mem, pairs, { th with term := c'.term, env := c'.env })] from
    H th.stack.reverse th (by simp) ht he hσ
  intro rs
  induction rs with
  | nil => intro th hst ht he hσ; exact h.2 g mem pairs th hg ht he hσ hst
  | cons f0 l ih =>
    intro th hst ht he hσ
    have happ : th = TermSpawnSim.app f0 { th with stack := l.reverse } := by
      obtain ⟨⟩ := th
      simp only [List.reverse_cons] at hst
      simp [TermSpawnSim.app, hst]
    have key := TermSpawnSim.tstep_app_eq f0 g mem pairs { th with stack := l.reverse }
      (fun a hr => absurd (hr.symm.trans ht).symm (hnr a))
    rw [ih { th with stack := l.reverse } rfl ht he hσ] at key
    rw [congrArg (TermRun.tstep g mem pairs) happ, key]
    simp only [List.map_cons, List.map_nil, TermSpawnSim.app]
    obtain ⟨⟩ := th
    simp only [List.reverse_cons] at hst
    simp [hst]

/-- **A local run is a local run at any depth.** -/
theorem LocalRun.toS {c c' : Ctl} (h : LocalRun p c c') : LocalRunS p c c' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs.toS ih

/-- A control at `ret` takes no local step at any depth. -/
theorem LocalStepS.not_ret {c c' : Ctl} (h : LocalStepS p c c') : ∀ a, c.term ≠ .ret a :=
  localStep_not_ret h.toLocalStep

/-- A control at a buffer allocation takes no local step: the step
allocates (`allocBuf` counts the allocation), so it does not keep the
thread. -/
theorem localStep_not_newBuf {c c₁ : Ctl} (h : LocalStep p c c₁) :
    ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e := by
  intro x a τ e ht
  have := h.2 { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 } #[] []
    { term := c.term, env := c.env } rfl rfl rfl rfl rfl
  simp only [TermRun.tstep, ht, TermRun.evalOp, TermRun.ol, List.map_eq_singleton_iff] at this
  obtain ⟨r, hr, hf⟩ := this
  have hn := congrArg (fun q => q.2.2.nalloc) hf
  simp only [TermRun.withS] at hn
  revert hr hn
  cases TermRun.evalAt c.env a <;> simp only [Option.toList, Option.bind, bind, pure] <;> try simp
  rename_i v
  cases TermRun.numOf v.2 <;> simp only <;> try simp
  cases TermRun.accs (TermRun.close [] τ) <;> simp only <;> try simp
  intro hr hn
  subst hr
  simp [TermRun.allocBuf, TermRun.stOf] at hn

/-- A control at a buffer allocation takes no local step at any depth. -/
theorem LocalStepS.not_newBuf {c c' : Ctl} (h : LocalStepS p c c') : ∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e :=
  localStep_not_newBuf h.toLocalStep

/-! ## Frame runs -/

/-- **One source step of a thread with its frames** (no type variables): a
local step at any depth, a call of a code block with no type arguments,
at any index arguments (`tstep` ignores them; the frame pushed returns into
`x` and then `e`, in the caller's environment), or a return into the top
frame (which has no type variables). -/
inductive FrameStep (p : Prog) : Ctl × List TermRun.Frame → Ctl × List TermRun.Frame → Prop
  | loc {c c' : Ctl} {fs : List TermRun.Frame} : LocalStepS p c c' → FrameStep p (c, fs) (c', fs)
  | call {c : Ctl} {fs : List TermRun.Frame} {x f : String} {is : List String} {a : At} {e : Expr} {d : Decl}
      {t : Ty} {ws : List TermRun.Word} :
      c.term = .let_ x (.call f is a []) e → p.find? (·.name == f) = some d →
      TermRun.evalAt c.env a = some (t, ws) →
      FrameStep p (c, fs) (⟨d.body, [(d.arg, d.argTy, ws)], none⟩, ⟨x, e, c.env, [], d.retTy⟩ :: fs)
  | ret {c : Ctl} {fr : TermRun.Frame} {fs : List TermRun.Frame} {a : At} {t : Ty} {ws : List TermRun.Word} :
      c.term = .ret a → fr.σs = [] → TermRun.evalAt c.env a = some (t, ws) →
      FrameStep p (c, fr :: fs) (⟨fr.body, (fr.x, fr.ty, ws) :: fr.env, none⟩, fs)

/-- Zero or more frame steps. -/
inductive FrameRun (p : Prog) : Ctl × List TermRun.Frame → Ctl × List TermRun.Frame → Prop
  | refl (q : Ctl × List TermRun.Frame) : FrameRun p q q
  | step {q q₁ q' : Ctl × List TermRun.Frame} : FrameStep p q q₁ → FrameRun p q₁ q' → FrameRun p q q'

namespace FrameRun

theorem single {q q' : Ctl × List TermRun.Frame} (h : FrameStep p q q') : FrameRun p q q' := .step h (.refl _)

theorem trans {q q₁ q' : Ctl × List TermRun.Frame} (h₁ : FrameRun p q q₁) (h₂ : FrameRun p q₁ q') :
    FrameRun p q q' := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- A local run at any depth is a frame run at fixed frames. -/
theorem ofLocalS {c c' : Ctl} (h : LocalRunS p c c') (fs : List TermRun.Frame) : FrameRun p (c, fs) (c', fs) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.loc hs) ih

/-- A local run is a frame run at any fixed frames. -/
theorem ofLocal {c c' : Ctl} (h : LocalRun p c c') (fs : List TermRun.Frame) : FrameRun p (c, fs) (c', fs) :=
  ofLocalS h.toS fs

end FrameRun

/-- **A frame step's `tstep`**: for a thread at its pair (no type
variables), one successor, with memory and pairs kept, at the step's
control and frames. -/
theorem FrameStep.tstep {q q' : Ctl × List TermRun.Frame} (h : FrameStep p q q') {g : TermRun.G}
    {mem : WeakMem.Memory} {pairs : List Nat} {th : TermRun.TTh} (hg : g.p = p) (ht : th.term = q.1.term)
    (he : th.env = q.1.env) (hσ : th.σs = []) (hst : th.stack = q.2) :
    TermRun.tstep g mem pairs th =
      [(mem, pairs, { th with term := q'.1.term, env := q'.1.env, stack := q'.2 })] := by
  cases h with
  | loc hs =>
    rw [hs.2 g mem pairs th hg ht he hσ]
    obtain ⟨⟩ := th
    simp only at hst
    simp [hst]
  | call hc hd ha =>
    rw [tstep_call_nil (ht ▸ hc) hσ (hg ▸ hd) (he ▸ ha)]
    simp [he, hst]
  | ret hc hfr ha =>
    rw [tstep_ret (ht ▸ hc) hst (he ▸ ha)]
    obtain ⟨⟩ := th
    simp only at hσ
    simp [hσ, hfr]

/-- A thread at a buffer allocation takes no frame step. -/
theorem FrameStep.not_newBuf {q q' : Ctl × List TermRun.Frame} (h : FrameStep p q q') :
    ∀ x a τ e, q.1.term ≠ .let_ x (.newBuf a τ) e := by
  intro x a τ e hc
  cases h with
  | loc hs => exact hs.not_newBuf x a τ e hc
  | call ht => rw [hc] at ht; cases ht
  | ret ht => rw [hc] at ht; cases ht

/-- A thread at `ret` with no frame left takes no frame step. -/
theorem FrameStep.not_main_ret {c : Ctl} {q' : Ctl × List TermRun.Frame} (h : FrameStep p (c, []) q') :
    ∀ a, c.term ≠ .ret a := by
  intro a hc
  cases h with
  | loc hs => exact hs.not_ret a hc
  | call ht => rw [hc] at ht; cases ht

/-- **A frame run from a buffer allocation or from `main`'s return is
empty.** -/
theorem FrameRun.eq_of_stuck {q q' : Ctl × List TermRun.Frame} (h : FrameRun p q q')
    (hs : (∃ x a τ e, q.1.term = .let_ x (.newBuf a τ) e) ∨ (q.2 = [] ∧ ∃ a, q.1.term = .ret a)) : q' = q := by
  cases h with
  | refl => rfl
  | step h1 _ =>
    exfalso
    rcases hs with ⟨x, a, τ, e, hc⟩ | ⟨h0, a, hc⟩
    · exact h1.not_newBuf x a τ e hc
    · obtain ⟨c, fs⟩ := q
      simp only at h0 hc
      subst h0
      exact h1.not_main_ret a hc

/-- **`main` has not returned** at a pair other than `main`'s return. -/
theorem mainExit_of_pair {s : TermRun.Cfg} {th : TermRun.TTh} (h0 : s.ths[0]? = some th)
    (hr : th.stack = [] → ∀ a, th.term ≠ .ret a) : mainExit s = [] := by
  unfold mainExit
  rw [h0]
  simp only
  split <;> simp_all

variable {P : SrcSem.SrcParams}

/-- **A frame step of thread 0 is a step of the source instance**, for a
hook the consumer accepts, before `main` has returned: its trace is the
growth of `srcObs`. -/
theorem FrameStep.source_step_obs {q q' : Ctl × List TermRun.Frame}
    (h : FrameStep p q q') {s : TermRun.Cfg} {th : TermRun.TTh} (hi : s.ths[0]? = some th)
    (ht : th.term = q.1.term) (he : th.env = q.1.env) (hσ : th.σs = []) (hst : th.stack = q.2)
    (hp : th.promises = []) (hex : mainExit s = []) :
    (SrcSem.source P p).step 0 s
      ((srcObs P.hooks.trace
          { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } }).drop
        (srcObs P.hooks.trace s).length)
      { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } := by
  have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  have hm := tstep_mem_threadSteps (k := P.k) (arch := P.arch) hi (h.tstep rfl ht he hσ hst)
  refine ⟨hex, .inl (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), rfl⟩
  simp [TermRun.noPromises, hlt, hp]

/-- **A frame step of thread 0 is a step of the source instance**, for a
hook the consumer accepts whose event list has no exit event, before `main`
has returned: its trace is `main`'s exit at the configuration it lands in. -/
theorem FrameStep.source_step (hP : HookOK P p) {q q' : Ctl × List TermRun.Frame}
    (h : FrameStep p q q') {s : TermRun.Cfg} {th : TermRun.TTh} (hi : s.ths[0]? = some th)
    (ht : th.term = q.1.term) (he : th.env = q.1.env) (hσ : th.σs = []) (hst : th.stack = q.2)
    (hp : th.promises = []) (hex : mainExit s = []) (hxT : ∀ x, Scc.Sem.Ev.exit x ∉ P.hooks.trace s) :
    (SrcSem.source P p).step 0 s
      (mainExit { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } })
      { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } := by
  have h1 := h.source_step_obs (P := P) hi ht he hσ hst hp hex
  rwa [obs_exit hxT (hP.trace_set _ _) hex] at h1

/-- **A frame step of thread 0 with the empty trace**: as
`FrameStep.source_step`, when `main` has returned neither before nor after
it, for every hook the consumer accepts. -/
theorem FrameStep.source_step_nil (hP : HookOK P p) {q q' : Ctl × List TermRun.Frame}
    (h : FrameStep p q q') {s : TermRun.Cfg} {th : TermRun.TTh} (hi : s.ths[0]? = some th)
    (ht : th.term = q.1.term) (he : th.env = q.1.env) (hσ : th.σs = []) (hst : th.stack = q.2)
    (hp : th.promises = []) (hex : mainExit s = [])
    (hex' : mainExit { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } =
      []) :
    (SrcSem.source P p).step 0 s []
      { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } := by
  have h1 := h.source_step_obs (P := P) hi ht he hσ hst hp hex
  rwa [obs_nil (hP.trace_set _ _) hex hex'] at h1

/-- **A frame run of thread 0 under the source instance** (`HookOK`)
(no type variables, no promises), from a pair other than `main`'s return:
a run whose trace is `main`'s exit at the configuration it lands in (`main`
returns at most at the last step: no frame step leaves `main`'s return), when
the hook's event list has no exit event. -/
theorem FrameRun.run_source (hP : HookOK P p) {q q' : Ctl × List TermRun.Frame}
    (h : FrameRun p q q') :
    ∀ {s : TermRun.Cfg} {th : TermRun.TTh}, s.ths[0]? = some th → th.term = q.1.term → th.env = q.1.env →
      th.σs = [] → th.stack = q.2 → th.promises = [] → (q.2 = [] → ∀ a, q.1.term ≠ .ret a) →
      (∀ x, Scc.Sem.Ev.exit x ∉ P.hooks.trace s) →
      (SrcSem.source P p).Run s
        (mainExit { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } })
        { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } := by
  induction h with
  | refl q =>
    intro s th hi ht he _ hst _ hr _
    have : { th with term := q.1.term, env := q.1.env, stack := q.2 } = th := by rw [← ht, ← he, ← hst]
    rw [this]
    have hs : s.ths.set! 0 th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [hs, show ({ s with ths := s.ths } : TermRun.Cfg) = s from rfl,
      mainExit_of_pair hi (fun h a e => hr (hst ▸ h) a (ht ▸ e))]
    exact .refl _
  | @step q q₁ q' hs hrun ih =>
    intro s th hi ht he hσ hst hp hr hxT
    have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
    let th₁ : TermRun.TTh := { th with term := q₁.1.term, env := q₁.1.env, stack := q₁.2 }
    have hi' : ({ s with ths := s.ths.set! 0 th₁ } : TermRun.Cfg).ths[0]? = some th₁ := by simp [hlt]
    have hex0 := mainExit_of_pair hi (fun h a e => hr (hst ▸ h) a (ht ▸ e))
    have h1 := hs.source_step hP hi ht he hσ hst hp hex0 hxT
    by_cases hr₁ : q₁.2 = [] → ∀ a, q₁.1.term ≠ .ret a
    · have h2 := ih (s := { s with ths := s.ths.set! 0 th₁ }) (th := th₁) hi' rfl rfl hσ rfl hp hr₁
        (by rw [hP.trace_set]; exact hxT)
      simp only [set!_set!, th₁] at h2
      rw [mainExit_of_pair hi' (fun h a e => hr₁ h a e)] at h1
      have h1' : (SrcSem.source P p).Run s ([] ++ []) { s with ths := s.ths.set! 0 th₁ } :=
        Scc.Sem.LRun.step ⟨0, h1⟩ (.refl _)
      exact Scc.Sem.LRun.trans h1' h2
    · -- `q₁` is `main`'s return: the rest of the run is empty.
      have hq : q' = q₁ := by
        cases hrun with
        | refl => rfl
        | step hs' _ =>
          exfalso
          apply hr₁
          intro h0 a
          obtain ⟨c₁, fs₁⟩ := q₁
          simp only at h0
          subst h0
          exact hs'.not_main_ret a
      subst hq
      have h1' : (SrcSem.source P p).Run s
          (mainExit { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } }
            ++ [])
          { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } :=
        Scc.Sem.LRun.step ⟨0, h1⟩ (.refl _)
      rwa [List.append_nil] at h1'

/-- **A frame run that does not end at `main`'s return** is a run of the
source instance with the empty trace, for every hook the consumer accepts. -/
theorem FrameRun.run_source_nil (hP : HookOK P p) {q q' : Ctl × List TermRun.Frame}
    (h : FrameRun p q q') :
    ∀ {s : TermRun.Cfg} {th : TermRun.TTh}, s.ths[0]? = some th → th.term = q.1.term → th.env = q.1.env →
      th.σs = [] → th.stack = q.2 → th.promises = [] → (q.2 = [] → ∀ a, q.1.term ≠ .ret a) →
      (q'.2 = [] → ∀ a, q'.1.term ≠ .ret a) →
      (SrcSem.source P p).Run s []
        { s with ths := s.ths.set! 0 { th with term := q'.1.term, env := q'.1.env, stack := q'.2 } } := by
  induction h with
  | refl q =>
    intro s th hi ht he _ hst _ _ _
    have : { th with term := q.1.term, env := q.1.env, stack := q.2 } = th := by rw [← ht, ← he, ← hst]
    rw [this]
    have hs : s.ths.set! 0 th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [hs]
    exact .refl _
  | @step q q₁ q' hs hrun ih =>
    intro s th hi ht he hσ hst hp hr hr'
    have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
    let th₁ : TermRun.TTh := { th with term := q₁.1.term, env := q₁.1.env, stack := q₁.2 }
    have hi' : ({ s with ths := s.ths.set! 0 th₁ } : TermRun.Cfg).ths[0]? = some th₁ := by simp [hlt]
    have hr₁ : q₁.2 = [] → ∀ a, q₁.1.term ≠ .ret a := by
      cases hrun with
      | refl => exact hr'
      | step hs' _ =>
        intro h0 a
        obtain ⟨c₁, fs₁⟩ := q₁
        simp only at h0
        subst h0
        exact hs'.not_main_ret a
    have h1 := hs.source_step_nil hP hi ht he hσ hst hp (mainExit_of_pair hi (fun h a e => hr (hst ▸ h) a (ht ▸ e)))
      (mainExit_of_pair hi' (fun h a e => hr₁ h a e))
    have h2 := ih (s := { s with ths := s.ths.set! 0 th₁ }) (th := th₁) hi' rfl rfl hσ rfl hp hr₁ hr'
    simp only [set!_set!, th₁] at h2
    exact Scc.Sem.LRun.trans (tr := []) (tr' := []) (Scc.Sem.LRun.step (es := []) (tr := []) ⟨0, h1⟩ (.refl _)) h2

/-! ## What one instruction does at depth -/

/-- **A fragment with the source thread's suspended frames.** -/
abbrev FragS (I : ISA) := I.State → Ctl → List TermRun.Frame → Prop

/-- **What one instruction does at frames `fs`** from the pair `(s, c)`,
landing in `X`: the source takes a frame run to `(c₁, fs₁)` and then the
instruction is an `Out` row there (the memory side at `fs₁`; `OutS.lift`: no
run), or a silent instruction whose source side is a frame run (a call's
`bl`, a callee's `ret`). The run before the row lets a pair whose source
is still to return (a callee's held-back `ret`) step at its caller's
frames. -/
inductive OutS {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide I)
    (X : FragS I) (s : I.State) (c : Ctl) (fs : List TermRun.Frame) : Prop where
  | pre (c₁ : Ctl) (fs₁ : List TermRun.Frame) :
      FrameRun p (c, fs) (c₁, fs₁) → Out p lbl (ms fs₁) (fun s c => X s c fs₁) s c₁ → OutS p lbl ms X s c fs
  | frame (s' : I.State) (c' : Ctl) (fs' : List TermRun.Frame) :
      I.exec s = some (.done s') → FrameRun p (c, fs) (c', fs') → X s' c' fs' → OutS p lbl ms X s c fs

namespace OutS

variable {I : ISA} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I}
  {X Y : FragS I} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}

/-- An `Out` row at the frames. -/
theorem lift (h : Out p lbl (ms fs) (fun s c => X s c fs) s c) : OutS p lbl ms X s c fs :=
  .pre c fs (.refl _) h

theorem mono (h : OutS p lbl ms X s c fs) (hXY : ∀ s c fs, X s c fs → Y s c fs) : OutS p lbl ms Y s c fs := by
  cases h with
  | pre c₁ fs₁ hr h => exact .pre c₁ fs₁ hr (h.mono fun s c => hXY s c fs₁)
  | frame s' c' fs' he hr hx => exact .frame s' c' fs' he hr (hXY _ _ _ hx)

/-- **A frame run before**: a row from `(c₁, fs₁)` is one from `(c, fs)` when
the source runs from the latter to the former. -/
theorem run {c₁ : Ctl} {fs₁ : List TermRun.Frame} (hr : FrameRun p (c, fs) (c₁, fs₁))
    (h : OutS p lbl ms X s c₁ fs₁) : OutS p lbl ms X s c fs := by
  cases h with
  | pre c₂ fs₂ hr' h => exact .pre c₂ fs₂ (hr.trans hr') h
  | frame s' c' fs' he hr' hx => exact .frame s' c' fs' he (hr.trans hr') hx

end OutS

/-- **Every outside move lands in `X`**, at any frames: every `K`-successor
`s'` of `s` is in `X`, with the source after a frame run from `(c, fs)`. -/
def KOutS {I : ISA} (K : I.State → I.State → Prop) (p : Prog) (X : FragS I) (s : I.State) (c : Ctl)
    (fs : List TermRun.Frame) : Prop :=
  ∀ s', K s s' → ∃ c' fs', FrameRun p (c, fs) (c', fs') ∧ X s' c' fs'

namespace KOutS

variable {I : ISA} {K : I.State → I.State → Prop} {X Y : FragS I} {s : I.State} {c : Ctl}
  {fs : List TermRun.Frame}

theorem mono (h : KOutS K p X s c fs) (hXY : ∀ s c fs, X s c fs → Y s c fs) : KOutS K p Y s c fs :=
  fun s' hk => let ⟨c', fs', hr, hx⟩ := h s' hk; ⟨c', fs', hr, hXY _ _ _ hx⟩

theorem none (h : ∀ s', ¬ K s s') : KOutS K p X s c fs := fun s' hk => (h s' hk).elim

/-- `KOut` at fixed frames. -/
theorem ofKOut {X₀ : Frag I} (h : KOut K p X₀ s c) (hX : ∀ s c, X₀ s c → X s c fs) : KOutS K p X s c fs :=
  fun s' hk => let ⟨c', hr, hx⟩ := h s' hk; ⟨c', fs, .ofLocal hr fs, hX _ _ hx⟩

theorem run {c₁ : Ctl} {fs₁ : List TermRun.Frame} (hr : FrameRun p (c, fs) (c₁, fs₁)) (h : KOutS K p X s c₁ fs₁) :
    KOutS K p X s c fs :=
  fun s' hk => let ⟨c', fs', hr', hx⟩ := h s' hk; ⟨c', fs', hr.trans hr', hx⟩

end KOutS

/-- **A pair with a pending frame run to `P`**: the source runs from
`(c, fs)` to a pair of `P` at the same state (a callee's return, taken at its
caller's next instruction). -/
def Pend {I : ISA} (p : Prog) (P : FragS I) : FragS I :=
  fun s c fs => ∃ c' fs', FrameRun p (c, fs) (c', fs') ∧ P s c' fs'

namespace Pend

variable {I : ISA} {P Q : FragS I} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}

/-- A pair of `P` has the empty pending run. -/
theorem of (h : P s c fs) : Pend p P s c fs := ⟨c, fs, .refl _, h⟩

theorem mono (h : Pend p P s c fs) (hPQ : ∀ s c fs, P s c fs → Q s c fs) : Pend p Q s c fs :=
  let ⟨c', fs', hr, h⟩ := h; ⟨c', fs', hr, hPQ _ _ _ h⟩

/-- Two pending runs are one. -/
theorem trans (h : Pend p (Pend p P) s c fs) : Pend p P s c fs :=
  let ⟨_, _, hr, _, _, hr', h⟩ := h; ⟨_, _, hr.trans hr', h⟩

/-- A pending run into `P` or a pending run into `Q` is a pending run into
`P` or `Q`. -/
theorem or_pend (h : Pend p (fun s c fs => P s c fs ∨ Pend p Q s c fs) s c fs) :
    Pend p (fun s c fs => P s c fs ∨ Q s c fs) s c fs :=
  trans (h.mono fun _ _ _ h => h.elim (fun h => of (.inl h)) fun h => h.mono fun _ _ _ => .inr)

end Pend

/-! ## Segments at depth -/

/-- **Segment simulation with frames, inside `W`, closed under `K`**: as
`SegW` over fragments with frames; every instruction lands with a pending
frame run (`Pend`: the source may still run after the row, as after a
callee's `ret`, the consumer's `PendN`); after an outside move (`K`) the
source takes a frame run (`KOutS`). -/
def SegWS {I : ISA} (W : FragS I) (K : I.State → I.State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide I) (P Q : FragS I) : Prop :=
  ∃ inv : FragS I, (∀ s c fs, P s c fs → inv s c fs) ∧ (∀ s c fs, inv s c fs → W s c fs) ∧
    ∀ s c fs, inv s c fs → ((∀ s', ¬ K s s') → OutS p lbl ms (Pend p fun s c fs => inv s c fs ∨ Q s c fs) s c fs) ∧
      KOutS K p (fun s c fs => inv s c fs ∨ Q s c fs) s c fs

/-- **Segment simulation with frames**: `SegWS` with no outside move and no
bound. -/
def SegS {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide I)
    (P Q : FragS I) : Prop :=
  SegWS (fun _ _ _ => True) (fun _ _ => False) p lbl ms P Q

/-- A fragment at fixed frames `fs`. -/
def Frag.at {I : ISA} (P : Frag I) (fs : List TermRun.Frame) : FragS I := fun s c fs' => P s c ∧ fs' = fs

namespace SegWS

variable {I : ISA} {W : FragS I} {K : I.State → I.State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
  {ms : List TermRun.Frame → MemSide I} {P P' Q Q' R : FragS I}

/-- **A segment at fixed frames**: a `SegW` under the memory side at `fs`,
inside `W` at `fs`. -/
theorem liftS {W₀ : Frag I} {P₀ Q₀ : Frag I} (fs : List TermRun.Frame) (h : SegW W₀ K p lbl (ms fs) P₀ Q₀)
    (hW : ∀ s c, W₀ s c → W s c fs) : SegWS W K p lbl ms (P₀.at fs) (Q₀.at fs) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  refine ⟨inv.at fs, fun s c fs' ⟨h, e⟩ => ⟨hP s c h, e⟩, fun s c fs' ⟨h, e⟩ => e ▸ hW s c (hiW s c h), ?_⟩
  rintro s c fs' ⟨hi, rfl⟩
  obtain ⟨hout, hk⟩ := hcl s c hi
  refine ⟨fun hK => .lift ((hout hK).mono fun s c h => ?_), KOutS.ofKOut hk fun s c h => ?_⟩
  · exact .of (h.imp (fun h => ⟨h, rfl⟩) (fun h => ⟨h, rfl⟩))
  · exact h.imp (fun h => ⟨h, rfl⟩) (fun h => ⟨h, rfl⟩)

/-- **One instruction** from every pair of `P` into `Q`, none of them moved
from outside. -/
theorem step (hW : ∀ s c fs, P s c fs → W s c fs) (hK : ∀ s c fs, P s c fs → ∀ s', ¬ K s s')
    (h : ∀ s c fs, P s c fs → OutS p lbl ms Q s c fs) : SegWS W K p lbl ms P Q :=
  ⟨P, fun _ _ _ h => h, hW, fun s c fs hp =>
    ⟨fun _ => (h s c fs hp).mono fun _ _ _ h => .of (.inr h), KOutS.none (hK s c fs hp)⟩⟩

/-- **Sequencing**: the exit of the first segment is the entry of the
second. -/
theorem seq (h₁ : SegWS W K p lbl ms P Q) (h₂ : SegWS W K p lbl ms Q R) : SegWS W K p lbl ms P R := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c fs => i₁ s c fs ∨ i₂ s c fs, fun s c fs h => .inl (hs₁ s c fs h),
    fun s c fs h => h.elim (hw₁ s c fs) (hw₂ s c fs), ?_⟩
  rintro s c fs (h | h)
  · obtain ⟨ho, hk⟩ := ho₁ s c fs h
    refine ⟨fun hK => (ho hK).mono fun s c fs h => h.mono fun s c fs h => ?_, hk.mono fun s c fs h => ?_⟩
    · exact h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c fs h))
    · exact h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c fs h))
  · obtain ⟨ho, hk⟩ := ho₂ s c fs h
    refine ⟨fun hK => (ho hK).mono fun s c fs h => h.mono fun s c fs h => ?_, hk.mono fun s c fs h => ?_⟩
    · exact h.elim (fun h => .inl (.inr h)) .inr
    · exact h.elim (fun h => .inl (.inr h)) .inr

theorem mono_pre (h : SegWS W K p lbl ms P Q) (hP : ∀ s c fs, P' s c fs → P s c fs) : SegWS W K p lbl ms P' Q :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, fun s c fs h => hs s c fs (hP s c fs h), hw, ho⟩

theorem mono_post (h : SegWS W K p lbl ms P Q) (hQ : ∀ s c fs, Q s c fs → Q' s c fs) : SegWS W K p lbl ms P Q' :=
  let ⟨i, hs, hw, ho⟩ := h
  ⟨i, hs, hw, fun s c fs h =>
    ⟨fun hK => ((ho s c fs h).1 hK).mono fun _ _ _ h => h.mono fun s c fs h => h.imp_right (hQ s c fs),
      (ho s c fs h).2.mono fun s c fs h => h.imp_right (hQ s c fs)⟩⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegWS W K p lbl ms P Q) (h' : SegWS W K p lbl ms P' Q) :
    SegWS W K p lbl ms (fun s c fs => P s c fs ∨ P' s c fs) Q := by
  obtain ⟨i, hs, hw, ho⟩ := h
  obtain ⟨i', hs', hw', ho'⟩ := h'
  refine ⟨fun s c fs => i s c fs ∨ i' s c fs, fun s c fs h => h.imp (hs s c fs) (hs' s c fs),
    fun s c fs h => h.elim (hw s c fs) (hw' s c fs), ?_⟩
  rintro s c fs (h | h)
  · exact ⟨fun hK => ((ho s c fs h).1 hK).mono fun s c fs h => h.mono fun s c fs h => h.imp_left .inl,
      (ho s c fs h).2.mono fun s c fs h => h.imp_left .inl⟩
  · exact ⟨fun hK => ((ho' s c fs h).1 hK).mono fun s c fs h => h.mono fun s c fs h => h.imp_left .inr,
      (ho' s c fs h).2.mono fun s c fs h => h.imp_left .inr⟩

/-- A segment from nowhere. -/
theorem empty (h : ∀ s c fs, ¬ P s c fs) : SegWS W K p lbl ms P Q :=
  ⟨fun _ _ _ => False, fun s c fs hP => h s c fs hP, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩

/-- **An entry family**: segments from each `P g` give one from their
union. -/
theorem exists_pre {γ : Sort _} {P : γ → FragS I} (h : ∀ g, SegWS W K p lbl ms (P g) Q) :
    SegWS W K p lbl ms (fun s c fs => ∃ g, P g s c fs) Q := by
  refine ⟨fun s c fs => ∃ g, Classical.choose (h g) s c fs,
    fun s c fs ⟨g, hg⟩ => ⟨g, (Classical.choose_spec (h g)).1 s c fs hg⟩,
    fun s c fs ⟨g, hg⟩ => (Classical.choose_spec (h g)).2.1 s c fs hg, ?_⟩
  rintro s c fs ⟨g, hg⟩
  have ho := (Classical.choose_spec (h g)).2.2 s c fs hg
  exact ⟨fun hK => (ho.1 hK).mono fun s c fs h => h.mono fun s c fs h => h.imp_left fun h => ⟨g, h⟩,
    ho.2.mono fun s c fs h => h.imp_left fun h => ⟨g, h⟩⟩

/-- **A pending frame run before a segment**: a segment from `P` is one
from the pairs with a pending frame run to `P` (`Pend`), given that `W`
holds at a pair whose source runs to a pair of `W` at the same state. -/
theorem prerun (h : SegWS W K p lbl ms P Q)
    (hW : ∀ s c fs c' fs', FrameRun p (c, fs) (c', fs') → W s c' fs' → W s c fs) :
    SegWS W K p lbl ms (Pend p P) Q := by
  obtain ⟨inv, hs, hw, ho⟩ := h
  refine ⟨Pend p inv, fun s c fs ⟨c', fs', hr, h⟩ => ⟨c', fs', hr, hs s c' fs' h⟩,
    fun s c fs ⟨c', fs', hr, h⟩ => hW s c fs c' fs' hr (hw s c' fs' h), ?_⟩
  rintro s c fs ⟨c', fs', hr, h⟩
  have hX : ∀ s c fs, (inv s c fs ∨ Q s c fs) → (Pend p inv s c fs ∨ Q s c fs) :=
    fun s c fs h => h.imp_left fun h => ⟨c, fs, .refl _, h⟩
  exact ⟨fun hK => (((ho s c' fs' h).1 hK).run hr).mono fun s c fs h => h.mono hX,
    (((ho s c' fs' h).2).run hr).mono hX⟩

/-- **A frame run before a segment, at the entry**: a segment from `P'` is
one from `P` when every pair of `P` is inside `W` and has a pending frame
run to `P'` (`Pend`; a caller's pair at a callee's entry, the source's call
still to take). Unlike `prerun`, only `P`'s pairs join the invariant. -/
theorem pre_run {P' : FragS I} (h : SegWS W K p lbl ms P' Q)
    (hP : ∀ s c fs, P s c fs → W s c fs ∧ Pend p P' s c fs) : SegWS W K p lbl ms P Q := by
  obtain ⟨inv, hs, hw, ho⟩ := h
  refine ⟨fun s c fs => inv s c fs ∨ P s c fs, fun s c fs h => .inr h,
    fun s c fs h => h.elim (hw s c fs) fun h => (hP s c fs h).1, ?_⟩
  have hX : ∀ s c fs, (inv s c fs ∨ Q s c fs) → ((inv s c fs ∨ P s c fs) ∨ Q s c fs) :=
    fun s c fs h => h.imp_left .inl
  rintro s c fs (h | h)
  · exact ⟨fun hK => ((ho s c fs h).1 hK).mono fun s c fs h => h.mono hX, (ho s c fs h).2.mono hX⟩
  · obtain ⟨c', fs', hr, h'⟩ := (hP s c fs h).2
    have ho' := ho s c' fs' (hs s c' fs' h')
    exact ⟨fun hK => ((ho'.1 hK).run hr).mono fun s c fs h => h.mono hX, (ho'.2.run hr).mono hX⟩

/-- **A frame run after a segment**: a segment to the pairs with a pending
frame run to `Q` (`Pend`; a callee's exit, the source's return still to
take) is one to `Q`, the run taken with the row that lands there. -/
theorem post_run (h : SegWS W K p lbl ms P (Pend p Q)) : SegWS W K p lbl ms P Q := by
  obtain ⟨inv, hs, hw, ho⟩ := h
  refine ⟨inv, hs, hw, fun s c fs hi => ⟨fun hK => ((ho s c fs hi).1 hK).mono fun _ _ _ h => h.or_pend, ?_⟩⟩
  intro s' hk
  obtain ⟨c', fs', hr, h⟩ := (ho s c fs hi).2 s' hk
  rcases h with h | ⟨c'', fs'', hr', h⟩
  · exact ⟨c', fs', hr, .inl h⟩
  · exact ⟨c'', fs'', hr.trans hr', .inr h⟩

end SegWS

/-! ## The overflow abort at depth -/

/-- **The overflow abort is justified at any call depth** (`abortJustified_overflow`
without the one-frame premise): thread `i` is `OvfReady`, has no type
variables, no promises, and no big number in its frames yet. -/
theorem abortJustified_overflowS {k : Promises.Knobs} {arch : WeakMem.Arch}
    {Sp : Nat → TermRun.Cfg → TermRun.Cfg → Prop} {obsTrace : TermRun.Cfg → List Scc.Sem.Ev}
    {init : TermRun.Cfg → Prop} {B : Budget} {tr : List Scc.Sem.Ev} {s : TermRun.Cfg} {i : Nat} {th : TermRun.TTh}
    (hi : s.ths[i]? = some th) (hc : OvfReady (Ctl.of th)) (hσ : th.σs = [])
    (hp : th.promises = []) (hnb : NoBigNumT i s) :
    AbortJustified B (SrcSem.ofStepsG p k arch Sp obsTrace init) tr s i .overflow := by
  obtain ⟨x, a, b, e, ta, tb, wa, wb, n, m, ht, ha, hb, hna, hnb', hbig⟩ := hc
  have hs := localStepS_add (p := p) ht ha hb
  have hm := hs.mem_threadSteps (k := k) (arch := arch) hi rfl rfl hσ
  have hlt : i < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  refine ⟨_, _, ⟨.inl (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), rfl⟩, hnb, ?_⟩
  · simp [TermRun.noPromises, hlt, hp]
  · intro h
    have h' := h { th with term := e, env := (x, .int, [TermRun.addW wa wb]) :: th.env }
      (by simp [SrcSem.ofStepsG, hlt, Ctl.of])
    have := h' ((x, .int, [TermRun.addW wa wb]) :: th.env) (by simp [Scc.Sem.frameEnvs])
      (x, .int, [TermRun.addW wa wb]) List.mem_cons_self _ List.mem_cons_self (n + m)
      (by simp [TermRun.addW, hna, hnb', TermRun.cst, Promises.TVal.mk0])
    omega

end Spike.Lib
