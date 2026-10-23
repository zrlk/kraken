/-
The source half of the per-construct judgement: local steps in closed
form, their lifting to whole configurations, and the justification of the
overflow abort.

* `localStep_add`: `let x = a + b in e` is a local step, binding `x` to
  `addW` of the two operand words (WeakCore's `Int` is unbounded: the sum
  of two numbers is a number, however large); `localStep_sub`: `let x =
  a - b in e`, binding `x` to `subW` (truncated subtraction);
* `LocalStep.mem_threadSteps`, `LocalRun.run`: a local step of source
  thread `i` is one of its thread steps, and a local run of a thread with
  no promises is a source run with the empty trace (each step certified by
  the empty solo run);
* `OvfReady`: the thread is at `let x = a + b in e` with two numbers whose
  sum is at least `2^64`, the point where the target's checked addition
  takes its abort edge;
* `abortJustified_overflow`: at such a point, with no big number in the
  thread's frames yet (`NoBigNumT`, the budget part of the overflow kind)
  and no promises, the abort of kind `overflow` is justified
  (`Scc.Sem.AbortJustified`): the thread's next step, the addition, crosses
  the budget part, for every `SrcSem.ofStepsG` source (any extra step, any
  observable trace).
-/
import Spike.Lib.Seg

namespace Spike.Lib

open CoreLang CoreTerm
open Scc.Sem (SrcSem AbortJustified NoBigNumT Budget frameEnvs)

/-! ## Local steps in closed form -/

/-- **`let x = a + b in e` is a local step**, binding `x` to `addW wa wb`
for the operand words `wa`, `wb`. -/
theorem localStep_add {p : Prog} {c : Ctl} {x : String} {a b : At} {e : Expr} {ta tb : Ty} {wa wb : TermRun.Word}
    (ht : c.term = .let_ x (.add a b) e) (ha : TermRun.evalAt c.env a = some (ta, [wa]))
    (hb : TermRun.evalAt c.env b = some (tb, [wb])) :
    LocalStep p c ⟨e, (x, .int, [TermRun.addW wa wb]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hb, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- **`let x = a - b in e` is a local step**, binding `x` to `subW wa wb`
(truncated subtraction) for the operand words `wa`, `wb`. -/
theorem localStep_sub {p : Prog} {c : Ctl} {x : String} {a b : At} {e : Expr} {ta tb : Ty} {wa wb : TermRun.Word}
    (ht : c.term = .let_ x (.sub a b) e) (ha : TermRun.evalAt c.env a = some (ta, [wa]))
    (hb : TermRun.evalAt c.env b = some (tb, [wb])) :
    LocalStep p c ⟨e, (x, .int, [TermRun.subW wa wb]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hb, TermRun.ol, TermRun.withS, TermRun.stOf]

/-! ## Lifting to configurations -/

variable {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch}

/-- **A local step of source thread `i` is one of its thread steps.** -/
theorem LocalStep.mem_threadSteps {c c' : Ctl} (h : LocalStep p c c') {s : TermRun.Cfg} {i : Nat}
    {th : TermRun.TTh} (hi : s.ths[i]? = some th) (ht : th.term = c.term) (he : th.env = c.env)
    (hσ : th.σs = []) (hst : th.stack = []) :
    { s with ths := s.ths.set! i { th with term := c'.term, env := c'.env } } ∈ TermRun.threadSteps p k arch s i := by
  unfold TermRun.threadSteps
  simp only [hi]
  rw [h.2 _ _ _ _ rfl ht he hσ hst]
  simp

theorem set!_set! {α : Type} (a : Array α) (i : Nat) (x y : α) : (a.set! i x).set! i y = a.set! i y := by
  simp [Array.set!_eq_setIfInBounds]

/-- **A local run of a source thread without promises is a source run with
the empty trace**, for every `SrcSem.ofStep` source. -/
theorem LocalRun.run {init : TermRun.Cfg → Prop} {c c' : Ctl} (h : LocalRun p c c') :
    ∀ {s : TermRun.Cfg} {i : Nat} {th : TermRun.TTh}, s.ths[i]? = some th → th.term = c.term → th.env = c.env →
      th.σs = [] → th.stack = [] → th.promises = [] →
      (SrcSem.ofStep p k arch init).Run s []
        { s with ths := s.ths.set! i { th with term := c'.term, env := c'.env } } := by
  induction h with
  | refl c =>
    intro s i th hi ht he _ _ _
    have : { th with term := c.term, env := c.env } = th := by rw [← ht, ← he]
    rw [this]
    have hs : s.ths.set! i th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [hs]
    exact .refl _
  | @step c c₁ c' hs _ ih =>
    intro s i th hi ht he hσ hst hp
    have hm := hs.mem_threadSteps (k := k) (arch := arch) hi ht he hσ hst
    have hi' : ({ s with ths := s.ths.set! i { th with term := c₁.term, env := c₁.env } } : TermRun.Cfg).ths[i]? =
        some { th with term := c₁.term, env := c₁.env } := by
      have hlt : i < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
      simp [hlt]
    have h2 := ih hi' rfl rfl hσ hst hp
    simp only [set!_set!] at h2
    refine Scc.Sem.LRun.trans (tr := []) (tr' := []) (Scc.Sem.LRun.step (es := []) (tr := []) ⟨i, .inl
      (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), rfl⟩ (.refl _)) h2
    have hlt : i < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
    simp [TermRun.noPromises, hlt, hp]

/-! ## The overflow abort -/

/-- **The source thread is about to overflow**: its term is
`let x = a + b in e`, both operands are numbers, and their sum is at least
`2^64`. -/
def OvfReady (c : Ctl) : Prop :=
  ∃ x a b e ta tb wa wb n m, c.term = .let_ x (.add a b) e ∧ TermRun.evalAt c.env a = some (ta, [wa]) ∧
    TermRun.evalAt c.env b = some (tb, [wb]) ∧ wa.val = .num n ∧ wb.val = .num m ∧ 2 ^ 64 ≤ n + m

/-- **The overflow abort is justified** at a source configuration whose
thread `i` is `OvfReady`, has one frame, no promises, and no big number in
its frames yet: its next step (the addition, certified by the empty solo
run) crosses the overflow part of every budget. -/
theorem abortJustified_overflow {Sp : Nat → TermRun.Cfg → TermRun.Cfg → Prop} {obsTrace : TermRun.Cfg → List Scc.Sem.Ev}
    {init : TermRun.Cfg → Prop} {B : Budget} {tr : List Scc.Sem.Ev} {s : TermRun.Cfg} {i : Nat} {th : TermRun.TTh}
    (hi : s.ths[i]? = some th) (hc : OvfReady (Ctl.of th)) (hσ : th.σs = []) (hst : th.stack = [])
    (hp : th.promises = []) (hnb : NoBigNumT i s) :
    AbortJustified B (SrcSem.ofStepsG p k arch Sp obsTrace init) tr s i .overflow := by
  obtain ⟨x, a, b, e, ta, tb, wa, wb, n, m, ht, ha, hb, hna, hnb', hbig⟩ := hc
  have hs := localStep_add (p := p) ht ha hb
  have hm := hs.mem_threadSteps (k := k) (arch := arch) hi rfl rfl hσ hst
  have hlt : i < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  refine ⟨_, _, ⟨.inl (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), rfl⟩, hnb, ?_⟩
  · simp [TermRun.noPromises, hlt, hp]
  · intro h
    have h' := h { th with term := e, env := (x, .int, [TermRun.addW wa wb]) :: th.env }
      (by simp [SrcSem.ofStepsG, hlt, Ctl.of])
    have := h' ((x, .int, [TermRun.addW wa wb]) :: th.env) (by simp [frameEnvs])
      (x, .int, [TermRun.addW wa wb]) List.mem_cons_self _ List.mem_cons_self (n + m)
      (by simp [TermRun.addW, hna, hnb', TermRun.cst, Promises.TVal.mk0])
    omega

end Spike.Lib
