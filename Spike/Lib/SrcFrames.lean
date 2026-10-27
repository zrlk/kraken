/-
**Source steps at any call depth**: local steps that do not look at the
call stack, the three frame steps (`call`, `ret`, `tail`) with their exact
post-states, and the lifting of both to runs of the source instance
(`SrcSem.source P p`) for thread 0 inside a call (a nonempty stack).

- `LocalStepS`: `LocalStep` without the one-frame premise (`stack = []`):
  `tstep` has one successor, which changes only the term and environment,
  whatever the stack. `LocalStepS.toLocalStep` forgets the extra
  generality, so the one-frame lemmas (`localStep_add`, …) stay as they are.
- `LocalRunS`: zero or more of them (`single`, `trans`, `toLocalRun`).
- `localStepS_ifeq` (`_eq`, `_ne`): `ifeq a b yes no` on two numbers takes
  `yes` if they are equal, `no` otherwise; `localStepS_add`, `_sub`,
  `_atom`, `_pair`, `_nameI`, `_cvt`, `_asLanes`, `_split`, `_unpack`: the
  closed forms of `Spike.Lib.Src`, `Spike.Lib.Form` at any depth.
- `tstep_call` (`tstep_call_nil`), `tstep_ret`, `tstep_tail`
  (`tstep_tail_nil`): the frame steps for a thread without type variables
  (`σs = []`), with the pushed `TermRun.Frame`, the entered body and its
  environment (the argument bound at the callee's declared type, closed at
  the call's type arguments), and the popped frame's continuation.
- `TraceThs`: the hook's event list ignores the threads (true of
  `SrcHooks.none`, `traceThs_none`, of WeakCore's hook, `traceThs_wc`, and
  of every `HookOK` hook, `HookOK.traceThs`).
- `mainExit_of_stack`: `main` has not returned while thread 0 is inside a
  call.
- `tstep_source_obs`, `tstep_source`: a one-successor `tstep` of thread 0
  that keeps memory and pairs and leaves no promise is a step of `source P
  p`, with the growth of `srcObs` as its trace, and with the empty trace
  when `main` has returned neither before nor after and the hook ignores
  the threads (`TraceThs`).
- `LocalRunS.run_source`: a local run of thread 0 inside a call (no type
  variables, no promises) is a run of `source P p` with the empty trace,
  for every hook that ignores the threads.
-/
import Scc.Sem.SrcOutProto
import Spike.Lib.SrcRun

namespace Spike.Lib

open CoreLang CoreTerm
open Scc.Sem (SrcSem)
open Scc.Sem.SrcSem (mainExit srcObs cutAtExit)

variable {p : Prog}

/-! ## Local steps at any depth -/

/-- **A local source step at any call depth** in program `p`: for a thread
with control `c` and no type variables (`σs = []`), whatever its call
stack, `TermRun.tstep` has exactly one successor, which keeps memory, the
pair list and every other field of the thread (the stack included) and has
control `c'`. The step leaves no hold. -/
def LocalStepS (p : Prog) (c c' : Ctl) : Prop :=
  c'.hold = none ∧
  ∀ (g : TermRun.G) (mem : WeakMem.Memory) (pairs : List Nat) (th : TermRun.TTh), g.p = p →
    th.term = c.term → th.env = c.env → th.σs = [] →
    TermRun.tstep g mem pairs th = [(mem, pairs, { th with term := c'.term, env := c'.env })]

/-- A local step at any depth is a local step (with one frame). -/
theorem LocalStepS.toLocalStep {c c' : Ctl} (h : LocalStepS p c c') : LocalStep p c c' :=
  ⟨h.1, fun g mem pairs th hg ht he hσ _ => h.2 g mem pairs th hg ht he hσ⟩

/-- Zero or more local steps at any depth. -/
inductive LocalRunS (p : Prog) : Ctl → Ctl → Prop
  | refl (c : Ctl) : LocalRunS p c c
  | step {c c₁ c' : Ctl} : LocalStepS p c c₁ → LocalRunS p c₁ c' → LocalRunS p c c'

theorem LocalRunS.single {c c' : Ctl} (h : LocalStepS p c c') : LocalRunS p c c' :=
  .step h (.refl _)

theorem LocalRunS.trans {c c₁ c' : Ctl} (h₁ : LocalRunS p c c₁) (h₂ : LocalRunS p c₁ c') :
    LocalRunS p c c' := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- A local run at any depth is a local run (with one frame). -/
theorem LocalRunS.toLocalRun {c c' : Ctl} (h : LocalRunS p c c') : LocalRun p c c' := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs.toLocalStep ih

/-- **`ifeq a b yes no` on two numbers** continues with `yes` if they are
equal and with `no` otherwise, in the same environment. -/
theorem localStepS_ifeq {c : Ctl} {a b : At} {yes no : Expr} {ta tb : Ty} {wa wb : TermRun.Word} {n m : Nat}
    (ht : c.term = .ifeq a b yes no) (ha : TermRun.evalAt c.env a = some (ta, [wa]))
    (hb : TermRun.evalAt c.env b = some (tb, [wb])) (hna : wa.val = .num n) (hnb : wb.val = .num m) :
    LocalStepS p c ⟨if n = m then yes else no, c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  obtain ⟨⟩ := th
  simp only at ht' he
  subst ht' he
  simp [TermRun.tstep, ht, ha, hb, hna, hnb]

/-- `ifeq` on two equal numbers takes `yes`. -/
theorem localStepS_ifeq_eq {c : Ctl} {a b : At} {yes no : Expr} {ta tb : Ty} {wa wb : TermRun.Word} {n : Nat}
    (ht : c.term = .ifeq a b yes no) (ha : TermRun.evalAt c.env a = some (ta, [wa]))
    (hb : TermRun.evalAt c.env b = some (tb, [wb])) (hna : wa.val = .num n) (hnb : wb.val = .num n) :
    LocalStepS p c ⟨yes, c.env, none⟩ := by
  simpa using localStepS_ifeq (p := p) ht ha hb hna hnb

/-- `ifeq` on two different numbers takes `no`. -/
theorem localStepS_ifeq_ne {c : Ctl} {a b : At} {yes no : Expr} {ta tb : Ty} {wa wb : TermRun.Word} {n m : Nat}
    (ht : c.term = .ifeq a b yes no) (ha : TermRun.evalAt c.env a = some (ta, [wa]))
    (hb : TermRun.evalAt c.env b = some (tb, [wb])) (hna : wa.val = .num n) (hnb : wb.val = .num m)
    (hnm : n ≠ m) : LocalStepS p c ⟨no, c.env, none⟩ := by
  simpa [hnm] using localStepS_ifeq (p := p) ht ha hb hna hnb

/-- `let x = a + b in e` (`localStep_add`) at any depth. -/
theorem localStepS_add {c : Ctl} {x : String} {a b : At} {e : Expr} {ta tb : Ty} {wa wb : TermRun.Word}
    (ht : c.term = .let_ x (.add a b) e) (ha : TermRun.evalAt c.env a = some (ta, [wa]))
    (hb : TermRun.evalAt c.env b = some (tb, [wb])) :
    LocalStepS p c ⟨e, (x, .int, [TermRun.addW wa wb]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hb, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- `let x = a - b in e` (`localStep_sub`) at any depth. -/
theorem localStepS_sub {c : Ctl} {x : String} {a b : At} {e : Expr} {ta tb : Ty} {wa wb : TermRun.Word}
    (ht : c.term = .let_ x (.sub a b) e) (ha : TermRun.evalAt c.env a = some (ta, [wa]))
    (hb : TermRun.evalAt c.env b = some (tb, [wb])) :
    LocalStepS p c ⟨e, (x, .int, [TermRun.subW wa wb]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hb, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- `let x = a` (`localStep_atom`) at any depth. -/
theorem localStepS_atom {c : Ctl} {x : String} {e : Expr} {t : Ty} {ws : List TermRun.Word} {a : At}
    (ht : c.term = .let_ x (.atom a) e) (ha : TermRun.evalAt c.env a = some (t, ws)) :
    LocalStepS p c ⟨e, (x, t, ws) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- `let x = (a, b)` (`localStep_pair`) at any depth. -/
theorem localStepS_pair {c : Ctl} {x : String} {e : Expr} {t u : Ty} {ws us : List TermRun.Word} {a b : At}
    (ht : c.term = .let_ x (.pair a b) e) (ha : TermRun.evalAt c.env a = some (t, ws))
    (hb : TermRun.evalAt c.env b = some (u, us)) :
    LocalStepS p c ⟨e, (x, .prod t u, ws ++ us) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hb, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- `let x = nameI a` (`localStep_nameI`) at any depth. -/
theorem localStepS_nameI {c : Ctl} {x : String} {e : Expr} {t : Ty} {ws : List TermRun.Word} {a : At}
    (ht : c.term = .let_ x (.nameI a) e) (ha : TermRun.evalAt c.env a = some (t, ws)) :
    LocalStepS p c ⟨e, (x, t, ws) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- `let x = cvt sg w a` of a number binds the converted number, at any
depth. -/
theorem localStepS_cvt {c : Ctl} {x : String} {e : Expr} {sg : Bool} {w : Wd} {a : At} {t : Ty} {n : Nat}
    (ht : c.term = .let_ x (.cvt sg w a) e) (ha : TermRun.evalAt c.env a = some (t, [TermRun.cst (.num n)])) :
    LocalStepS p c ⟨e, (x, .fix sg w, [TermRun.cst (.num (TermRun.cvtN t w n))]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, TermRun.ol, TermRun.withS, TermRun.stOf,
    TermRun.numOf, TermRun.cst, Promises.TVal.mk0]

/-- `let x = asLanes sg w a` (`localStep_asLanes`) at any depth. -/
theorem localStepS_asLanes {c : Ctl} {x : String} {e : Expr} {t : Ty} {ws : List TermRun.Word} {a : At}
    {sg : Bool} {w : Wd} {n : Nat} (ht : c.term = .let_ x (.asLanes sg w a) e)
    (ha : TermRun.evalAt c.env a = some (t, ws)) (hn : TermRun.numOf ws = some n) :
    LocalStepS p c ⟨e, (x, .lanes sg w, [TermRun.cst (.num (n % TermRun.W64))]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hn, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- `let (x, y) = a` (`localStep_split`) at any depth. -/
theorem localStepS_split {c : Ctl} {x y : String} {e : Expr} {ws : List TermRun.Word} {a : At} {u v : Ty}
    {us : List TermRun.Acc} (ht : c.term = .split a x y e) (ha : TermRun.evalAt c.env a = some (.prod u v, ws))
    (hu : TermRun.accs u = some us) :
    LocalStepS p c ⟨e, (y, v, ws.drop (TermRun.nWords us)) :: (x, u, ws.take (TermRun.nWords us)) :: c.env,
      none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [TermRun.tstep, ht', ht, he, ha, hu]

/-- `let <i, x> = unpack a` (`localStep_unpack`) at any depth. -/
theorem localStepS_unpack {c : Ctl} {x i : String} {e : Expr} {ws : List TermRun.Word} {a : At} {b : Ty}
    (ht : c.term = .unpack a i x e) (ha : TermRun.evalAt c.env a = some (.iex b, ws)) :
    LocalStepS p c ⟨e, (x, b, ws) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _
  simp [TermRun.tstep, ht', ht, he, ha]

/-! ## Frame steps -/

/-- Closing at no type variables is the identity. -/
theorem close_nil (τ : Ty) : TermRun.close [] τ = τ := TermStep.substTs_nil' τ 0 0

/-- **`let x = call f a ts in e`**, for a thread without type variables:
one successor, with memory and pairs kept, which pushes the frame
returning into `x` and then `e` (the caller's environment, no type
variables, the callee's return type at `ts`) and enters `f`'s body with
its argument bound to `a`'s words at its declared type at `ts`. -/
theorem tstep_call {g : TermRun.G} {mem : WeakMem.Memory} {pairs : List Nat} {th : TermRun.TTh} {x f : String}
    {is : List String} {a : At} {ts : List Ty} {e : Expr} {d : Decl} {t : Ty} {ws : List TermRun.Word}
    (ht : th.term = .let_ x (.call f is a ts) e) (hσ : th.σs = []) (hd : g.p.find? (·.name == f) = some d)
    (ha : TermRun.evalAt th.env a = some (t, ws)) :
    TermRun.tstep g mem pairs th =
      [(mem, pairs,
        { th with
          term := d.body, env := [(d.arg, TermRun.close ts.reverse d.argTy, ws)], σs := ts.reverse,
          stack := ⟨x, e, th.env, [], TermRun.close ts.reverse d.retTy⟩ :: th.stack })] := by
  have hts : ts.map (TermRun.close []) = ts := by rw [show TermRun.close [] = id from funext close_nil, List.map_id]
  simp [TermRun.tstep, ht, TermRun.callFrame, TermRun.enter, hd, ha, hσ, hts, TermRun.ol]

/-- `tstep_call` at no type arguments. -/
theorem tstep_call_nil {g : TermRun.G} {mem : WeakMem.Memory} {pairs : List Nat} {th : TermRun.TTh} {x f : String}
    {is : List String} {a : At} {e : Expr} {d : Decl} {t : Ty} {ws : List TermRun.Word}
    (ht : th.term = .let_ x (.call f is a []) e) (hσ : th.σs = []) (hd : g.p.find? (·.name == f) = some d)
    (ha : TermRun.evalAt th.env a = some (t, ws)) :
    TermRun.tstep g mem pairs th =
      [(mem, pairs,
        { th with
          term := d.body, env := [(d.arg, d.argTy, ws)], stack := ⟨x, e, th.env, [], d.retTy⟩ :: th.stack })] := by
  rw [tstep_call ht hσ hd ha]
  simp [close_nil, hσ]

/-- **`ret a` inside a call**: one successor, with memory and pairs kept,
which pops the top frame and continues with its body, its environment
extended by its variable bound to `a`'s words at the frame's type, and its
type variables. -/
theorem tstep_ret {g : TermRun.G} {mem : WeakMem.Memory} {pairs : List Nat} {th : TermRun.TTh} {a : At}
    {fr : TermRun.Frame} {rest : List TermRun.Frame} {t : Ty} {ws : List TermRun.Word}
    (ht : th.term = .ret a) (hst : th.stack = fr :: rest) (ha : TermRun.evalAt th.env a = some (t, ws)) :
    TermRun.tstep g mem pairs th =
      [(mem, pairs,
        { th with term := fr.body, env := (fr.x, fr.ty, ws) :: fr.env, σs := fr.σs, stack := rest })] := by
  simp [TermRun.tstep, ht, hst, ha]

/-- **`tail f a ts`**, for a thread without type variables: one successor,
with memory, pairs and the stack kept, which enters `f`'s body with its
argument bound to `a`'s words at its declared type at `ts`. -/
theorem tstep_tail {g : TermRun.G} {mem : WeakMem.Memory} {pairs : List Nat} {th : TermRun.TTh} {f : String}
    {is : List String} {a : At} {ts : List Ty} {d : Decl} {t : Ty} {ws : List TermRun.Word}
    (ht : th.term = .tail f is a ts) (hσ : th.σs = []) (hd : g.p.find? (·.name == f) = some d)
    (ha : TermRun.evalAt th.env a = some (t, ws)) :
    TermRun.tstep g mem pairs th =
      [(mem, pairs,
        { th with term := d.body, env := [(d.arg, TermRun.close ts.reverse d.argTy, ws)], σs := ts.reverse })] := by
  have hts : ts.map (TermRun.close []) = ts := by rw [show TermRun.close [] = id from funext close_nil, List.map_id]
  simp [TermRun.tstep, ht, TermRun.enter, hd, ha, hσ, hts, TermRun.ol]

/-- `tstep_tail` at no type arguments: a local step at any depth. -/
theorem localStepS_tail {c : Ctl} {f : String} {is : List String} {a : At} {d : Decl} {t : Ty}
    {ws : List TermRun.Word} (ht : c.term = .tail f is a []) (hd : p.find? (·.name == f) = some d)
    (ha : TermRun.evalAt c.env a = some (t, ws)) :
    LocalStepS p c ⟨d.body, [(d.arg, d.argTy, ws)], none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th hg ht' he hσ
  rw [tstep_tail (ht' ▸ ht) hσ (hg ▸ hd) (he ▸ ha)]
  simp [close_nil, hσ]

/-! ## Lifting to the source instance -/

/-- **A one-successor `tstep` of thread `i`** is one of its thread steps. -/
theorem tstep_mem_threadSteps {k : Promises.Knobs} {arch : WeakMem.Arch} {s : TermRun.Cfg} {i : Nat}
    {th th' : TermRun.TTh} (hi : s.ths[i]? = some th)
    (h : TermRun.tstep (TermRun.gOf p k arch s i) s.mem s.pairs th = [(s.mem, s.pairs, th')]) :
    { s with ths := s.ths.set! i th' } ∈ TermRun.threadSteps p k arch s i := by
  unfold TermRun.threadSteps
  simp only [hi]
  rw [h]
  simp

/-- **A local step at any depth of source thread `i` is one of its thread
steps.** -/
theorem LocalStepS.mem_threadSteps {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Ctl}
    (h : LocalStepS p c c') {s : TermRun.Cfg} {i : Nat} {th : TermRun.TTh} (hi : s.ths[i]? = some th)
    (ht : th.term = c.term) (he : th.env = c.env) (hσ : th.σs = []) :
    { s with ths := s.ths.set! i { th with term := c'.term, env := c'.env } } ∈
      TermRun.threadSteps p k arch s i :=
  tstep_mem_threadSteps hi (h.2 _ _ _ _ rfl ht he hσ)

variable {P : SrcSem.SrcParams}

/-- **The hook's event list ignores the threads**: replacing the thread
array keeps it. -/
def TraceThs (P : SrcSem.SrcParams) : Prop :=
  ∀ (c : TermRun.Cfg) (ths : Array TermRun.TTh), P.hooks.trace { c with ths := ths } = P.hooks.trace c

theorem traceThs_none (hP : P.hooks = SrcSem.SrcHooks.none) : TraceThs P := by
  intro c ths; rw [hP]; rfl

theorem traceThs_wc (hP : Scc.Sem.SrcOutProto.UsesWc P p) : TraceThs P := by
  intro c ths; rw [hP]; rfl

theorem HookOK.traceThs (hP : HookOK P p) : TraceThs P := hP.trace_set

/-- **`main` has not returned while thread 0 is inside a call.** -/
theorem mainExit_of_stack {s : TermRun.Cfg} {th : TermRun.TTh} (h0 : s.ths[0]? = some th)
    (hst : th.stack ≠ []) : mainExit s = [] := by
  unfold mainExit
  rw [h0]
  simp only
  split
  · simp_all
  · rfl

/-- **A one-successor `tstep` of thread 0** that keeps memory and pairs
and leaves no promise, before `main` has returned, is a step of `source P
p` whose trace is the growth of `srcObs`. -/
theorem tstep_source_obs {s : TermRun.Cfg} {th th' : TermRun.TTh} (hi : s.ths[0]? = some th)
    (h : TermRun.tstep (TermRun.gOf p P.k P.arch s 0) s.mem s.pairs th = [(s.mem, s.pairs, th')])
    (hp : th'.promises = []) (hex : mainExit s = []) :
    (SrcSem.source P p).step 0 s
      ((srcObs P.hooks.trace { s with ths := s.ths.set! 0 th' }).drop (srcObs P.hooks.trace s).length)
      { s with ths := s.ths.set! 0 th' } := by
  have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  refine ⟨hex, .inl (.inl ⟨tstep_mem_threadSteps hi h, ⟨_, .refl _, ?_⟩⟩), rfl⟩
  simp [TermRun.noPromises, hlt, hp]

/-- **A one-successor `tstep` of thread 0 with the empty trace**: as
`tstep_source_obs`, when `main` has returned neither before nor after and
the hook ignores the threads. -/
theorem tstep_source (hT : TraceThs P) {s : TermRun.Cfg} {th th' : TermRun.TTh} (hi : s.ths[0]? = some th)
    (h : TermRun.tstep (TermRun.gOf p P.k P.arch s 0) s.mem s.pairs th = [(s.mem, s.pairs, th')])
    (hp : th'.promises = []) (hex : mainExit s = []) (hex' : mainExit { s with ths := s.ths.set! 0 th' } = []) :
    (SrcSem.source P p).step 0 s [] { s with ths := s.ths.set! 0 th' } := by
  have h1 := tstep_source_obs hi h hp hex
  have e : ((srcObs P.hooks.trace { s with ths := s.ths.set! 0 th' }).drop
      (srcObs P.hooks.trace s).length : List Scc.Sem.Ev) = [] := by
    simp only [srcObs, hex, hex', List.append_nil]
    rw [hT s (s.ths.set! 0 th'), List.drop_length]
  rwa [e] at h1

/-- **A local run of thread 0 inside a call** (a nonempty stack, no type
variables, no promises) is a run of `source P p` with the empty trace, for
every hook that ignores the threads: `main` cannot return while the stack
is nonempty. -/
theorem LocalRunS.run_source (hT : TraceThs P) {c c' : Ctl} (h : LocalRunS p c c') :
    ∀ {s : TermRun.Cfg} {th : TermRun.TTh}, s.ths[0]? = some th → th.term = c.term → th.env = c.env →
      th.σs = [] → th.stack ≠ [] → th.promises = [] →
      (SrcSem.source P p).Run s [] { s with ths := s.ths.set! 0 { th with term := c'.term, env := c'.env } } := by
  induction h with
  | refl c =>
    intro s th hi ht he _ _ _
    have : { th with term := c.term, env := c.env } = th := by rw [← ht, ← he]
    rw [this]
    have hs : s.ths.set! 0 th = s.ths := by
      obtain ⟨hlt, hx⟩ := Array.getElem?_eq_some_iff.mp hi
      subst hx
      simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
    rw [hs]
    exact .refl _
  | @step c c₁ c' hs _ ih =>
    intro s th hi ht he hσ hst hp
    have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
    have hi' : ({ s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } : TermRun.Cfg).ths[0]? =
        some { th with term := c₁.term, env := c₁.env } := by
      simp [hlt]
    have h1 : (SrcSem.source P p).step 0 s []
        { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } :=
      tstep_source hT hi (hs.2 _ _ _ _ rfl ht he hσ) hp (mainExit_of_stack hi hst) (mainExit_of_stack hi' hst)
    have h2 := ih hi' rfl rfl hσ hst hp
    simp only [set!_set!] at h2
    exact Scc.Sem.LRun.trans (tr := []) (tr' := []) (Scc.Sem.LRun.step (es := []) (tr := []) ⟨0, h1⟩ (.refl _)) h2

end Spike.Lib
