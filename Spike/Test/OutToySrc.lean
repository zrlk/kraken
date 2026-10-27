/-
**Prototype: a source that prints** (design spike for output, source half).
`main` binds `n = 72`, converts it to a byte `b = cvt U8 n`, emits `b`
(`ext emit b`, WeakCore's extern step), binds `z = 0` and returns it. Under the source
with WeakCore's extern hook (`Scc.Sem.SrcSem.wcHooks`) its source
reaches the observable trace `[out 72, exit 0]` (`toy_reach`): the byte
first, then `main`'s exit.

- `localStep_src`: a local step of thread 0 (not at `ret` before or after)
  is a step of `source P p` with the empty trace, for every `P` using
  WeakCore's hook (the analogue of `LocalRun.run_source`, which is stated
  for the empty hook).
- `localStep_src_obs`: the same for a step that may land at `ret`, with the
  growth of `srcObs` (`main`'s exit) as its trace.
- `emit_src`: thread 0 at `let x = ext emit a in e`, with no promises, takes
  the extern step; its trace is the growth of `srcObs` (the byte, and
  `main`'s exit if `e` is a `ret`).
- `st1`…`st5`: the toy's five source steps, separately (`s0` … `s4`,
  `sEnd`): three with trace `[]`, the `emit` with `[out 72]`, the binding
  into `ret z` with `[exit 0]`.
- `localStep_cvt`: `let x = cvt w a` is a local step.
-/
import Scc.Sem.SrcOutProto
import Spike.Lib.SrcRun
import Spike.Lib.Form
import Spike.Lib.A64Consumer

namespace Spike.Test.OutToySrc

open CoreLang CoreTerm TermRun TermExtStep
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib

/-! ## Generic steps under WeakCore's hook -/

/-- **`let x = cvt w a`** binds the converted number. -/
theorem localStep_cvt {p : Prog} {c : Ctl} {x : String} {e : Expr} {sg : Bool} {w : Wd} {a : At} {t : Ty}
    {n : Nat} (ht : c.term = .let_ x (.cvt sg w a) e) (ha : evalAt c.env a = some (t, [cst (.num n)])) :
    LocalStep p c ⟨e, (x, .fix sg w, [cst (.num (cvtN t w n))]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp [tstep, ht', ht, evalOp, he, ha, ol, withS, stOf, numOf, cst, Promises.TVal.mk0]

/-- **A local step of thread 0 is a source step with the empty trace**
under WeakCore's hook, when thread 0 is not at `ret` before or after. -/
theorem localStep_src {P : SrcParams} {p : Prog} (hP : UsesWc P p) {c c₁ : Ctl} (h : LocalStep p c c₁)
    {s : Cfg} {th : TTh} (hi : s.ths[0]? = some th) (ht : th.term = c.term) (he : th.env = c.env)
    (hσ : th.σs = []) (hst : th.stack = []) (hp : th.promises = []) (hr : ∀ a, c.term ≠ .ret a)
    (hr₁ : ∀ a, c₁.term ≠ .ret a) :
    (source P p).step 0 s [] { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } := by
  have hm := h.mem_threadSteps (k := P.k) (arch := P.arch) hi ht he hσ hst
  have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  have hi' : ({ s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } : Cfg).ths[0]? =
      some { th with term := c₁.term, env := c₁.env } := by simp [hlt]
  have hex0 := mainExit_of_not_ret hi (fun a h => hr a (ht ▸ h))
  refine ⟨hex0, .inl (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), ?_⟩
  · simp [noPromises, hlt, hp]
  · rw [hP]
    simp only [srcObs, wcHooks, traceOf, hex0, mainExit_of_not_ret hi' hr₁, List.append_nil, List.drop_length]

/-- **A local step of thread 0 is a source step** under WeakCore's hook,
when thread 0 is not at `ret` before it: its trace is the growth of
`srcObs`, which is `main`'s exit if the step lands at `ret` (the step into
`main`'s return; `[]` otherwise, `localStep_src`). Every hook. -/
theorem localStep_src_obs {P : SrcParams} {p : Prog} {c c₁ : Ctl} (h : LocalStep p c c₁)
    {s : Cfg} {th : TTh} (hi : s.ths[0]? = some th) (ht : th.term = c.term) (he : th.env = c.env)
    (hσ : th.σs = []) (hst : th.stack = []) (hp : th.promises = []) (hr : ∀ a, c.term ≠ .ret a) :
    (source P p).step 0 s
      ((srcObs P.hooks.trace { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } }).drop
        (srcObs P.hooks.trace s).length)
      { s with ths := s.ths.set! 0 { th with term := c₁.term, env := c₁.env } } := by
  have hm := h.mem_threadSteps (k := P.k) (arch := P.arch) hi ht he hσ hst
  have hlt : 0 < s.ths.size := (Array.getElem?_eq_some_iff.mp hi).1
  refine ⟨mainExit_of_not_ret hi (fun a h => hr a (ht ▸ h)), .inl (.inl ⟨hm, ⟨_, .refl _, ?_⟩⟩), rfl⟩
  simp [noPromises, hlt, hp]

/-- **The extern step `emit` of thread 0** under WeakCore's hook, with no
promises: its trace is the growth of `srcObs`. -/
theorem emit_src {P : SrcParams} {p : Prog} (hP : UsesWc P p) {s : Cfg} {th : TTh} {x : String} {a : At}
    {e : Expr} {rt : Ty} {ws : List Word} (hi : s.ths[0]? = some th) (ht : th.term = .let_ x (.ext .emit a) e)
    (hp : th.promises = []) (ha : evalAt th.env a = some (rt, ws)) :
    (source P p).step 0 s
      ((srcObs P.hooks.trace (extCfg s 0 th x .emit e ws [])).drop (srcObs P.hooks.trace s).length)
      (extCfg s 0 th x .emit e ws []) := by
  refine ⟨mainExit_of_not_ret hi (fun b h => by rw [ht] at h; cases h), .inr (.inr ?_), rfl⟩
  rw [hP]
  exact ⟨x, .emit, a, e, th, rt, ws, [], hi, ht, fun _ => hp, ha, rfl,
    ⟨_, .refl _, by rw [extCfg_noPromises hi, hp]; rfl⟩, rfl⟩

/-! ## The toy -/

/-- `main`'s body: `let n = 72; let b = cvt U8 n; let r = emit b; let z = 0;
ret z`. The binding after the `emit` puts the byte and `main`'s exit in two
source steps, as the target's write and `exit_group` are two steps. -/
def toyBody : Expr :=
  .let_ "n" (.atom (.lit 72)) (.let_ "b" (.cvt false .w8 (.var "n"))
    (.let_ "r" (.ext .emit (.var "b")) (.let_ "z" (.atom (.lit 0)) (.ret (.var "z")))))

/-- The toy's `main`. -/
def toyD : Decl := { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int, body := toyBody }

/-- The toy program. -/
def toyProg : Prog := [toyD]

-- The toy is a well-typed WeakCore program (the checker, executed).
#guard accepts (checkProg toyProg)

/-- The source parameters: those of the single-thread theorems (`srcP1`)
with WeakCore's extern hook. -/
def toyP (arch : WeakMem.Arch) : SrcParams :=
  { arch, cap := 1, init := mainInit 1, hooks := wcHooks toyProg .all arch }

theorem toyP_wc (arch : WeakMem.Arch) : UsesWc (toyP arch) toyProg := rfl

/-- The start's tail call enters `main`. -/
theorem toy_start : LocalStep toyProg A64Consumer.c0 ⟨toyBody, [("u", .unit, [])], none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th hg ht he hs _
  simp only [tstep, ht, enter, hg, he, A64Consumer.c0, evalAt, lookupE, List.find?, ol, Option.map,
    Option.toList]
  obtain ⟨⟩ := th
  simp only at hs
  subst hs
  rfl

/-- The start's thread. -/
def th0 : TTh := { term := .tail "main" [] (.var "a") [], env := [("a", .unit, [])] }

/-- The byte's words. -/
def wsB : List Word := [cst (.num (cvtN (.intS (.lit 72)) .w8 72))]

/-- The environments after `main`'s entry and each binding. -/
def env1 : Env := [("u", .unit, [])]
def env2 : Env := ("n", .intS (.lit 72), [cst (.num 72)]) :: env1
def env3 : Env := ("b", .fix false .w8, wsB) :: env2
def env4 : Env := ("r", .unit, []) :: env3
def env5 : Env := ("z", .intS (.lit 0), [cst (.num 0)]) :: env4

/-- The terms at those points. -/
def t4 : Expr := .let_ "z" (.atom (.lit 0)) (.ret (.var "z"))
def t3 : Expr := .let_ "r" (.ext .emit (.var "b")) t4
def t2 : Expr := .let_ "b" (.cvt false .w8 (.var "n")) t3

def th1 : TTh := { th0 with term := toyBody, env := env1 }
def th2 : TTh := { th1 with term := t2, env := env2 }
def th3 : TTh := { th2 with term := t3, env := env3 }
def th4 : TTh := { th3 with term := t4, env := env4 }

/-- The start; `main` entered; after `n`; after `b` (at the `emit`). -/
def s0 : Cfg := { mainStart with cap := 1 }
def s1 : Cfg := { s0 with ths := s0.ths.set! 0 th1 }
def s2 : Cfg := { s1 with ths := s1.ths.set! 0 th2 }
def s3 : Cfg := { s2 with ths := s2.ths.set! 0 th3 }

/-- After the `emit`: the byte in the trace, `main` at `let z = 0; ret z`. -/
def s4 : Cfg := extCfg s3 0 th3 "r" .emit t4 wsB []

/-- At `main`'s `ret z`. -/
def sEnd : Cfg := { s4 with ths := s4.ths.set! 0 { th4 with term := .ret (.var "z"), env := env5 } }

theorem s4_th : s4.ths[0]? = some th4 := rfl
theorem s3_obs : srcObs traceOf s3 = [] := by decide
theorem s4_obs : srcObs traceOf s4 = [.out 72] := by decide
theorem sEnd_obs : srcObs traceOf sEnd = [.out 72, .exit 0] := by decide

variable (arch : WeakMem.Arch)

/-- Entering `main`. -/
theorem st1 : (source (toyP arch) toyProg).step 0 s0 [] s1 :=
  localStep_src (toyP_wc arch) toy_start (c₁ := ⟨toyBody, env1, none⟩) (th := th0) rfl rfl rfl rfl rfl rfl
    (fun _ h => by cases h) (fun _ h => by cases h)

/-- `let n = 72`. -/
theorem st2 : (source (toyP arch) toyProg).step 0 s1 [] s2 :=
  localStep_src (toyP_wc arch) (c := ⟨toyBody, env1, none⟩) (c₁ := ⟨t2, env2, none⟩)
    (Form.localStep_atom rfl rfl) (th := th1) rfl rfl rfl rfl rfl rfl
    (fun _ h => by cases h) (fun _ h => by cases h)

/-- `let b = cvt U8 n`. -/
theorem st3 : (source (toyP arch) toyProg).step 0 s2 [] s3 :=
  localStep_src (toyP_wc arch) (c := ⟨t2, env2, none⟩) (c₁ := ⟨t3, env3, none⟩) (localStep_cvt rfl rfl)
    (th := th2) rfl rfl rfl rfl rfl rfl
    (fun _ h => by cases h) (fun _ h => by cases h)

/-- `let r = emit b`: the byte. -/
theorem st4 : (source (toyP arch) toyProg).step 0 s3 [.out 72] s4 := by
  have h := emit_src (toyP_wc arch) (s := s3) (th := th3) (x := "r") (e := t4) (ws := wsB) rfl rfl rfl rfl
  have e : (srcObs (toyP arch).hooks.trace s4).drop (srcObs (toyP arch).hooks.trace s3).length = [.out 72] := by
    change (srcObs traceOf s4).drop (srcObs traceOf s3).length = _
    rw [s4_obs, s3_obs]; rfl
  change (source (toyP arch) toyProg).step 0 s3
    ((srcObs (toyP arch).hooks.trace s4).drop (srcObs (toyP arch).hooks.trace s3).length) s4 at h
  rwa [e] at h

/-- `let z = 0` into `ret z`: `main`'s exit. -/
theorem st5 : (source (toyP arch) toyProg).step 0 s4 [.exit 0] sEnd := by
  have h := localStep_src_obs (P := toyP arch) (p := toyProg) (c := ⟨t4, env4, none⟩)
    (c₁ := ⟨.ret (.var "z"), env5, none⟩)
    (Form.localStep_atom rfl rfl) s4_th rfl rfl rfl rfl rfl (fun _ h => by cases h)
  have e : (srcObs (toyP arch).hooks.trace sEnd).drop (srcObs (toyP arch).hooks.trace s4).length =
      [.exit 0] := by
    change (srcObs traceOf sEnd).drop (srcObs traceOf s4).length = _
    rw [sEnd_obs, s4_obs]; rfl
  change (source (toyP arch) toyProg).step 0 s4
    ((srcObs (toyP arch).hooks.trace sEnd).drop (srcObs (toyP arch).hooks.trace s4).length) sEnd at h
  rwa [e] at h

/-- **The toy's source reaches `[out 72, exit 0]`** under WeakCore's hook,
for every memory model: the byte at the `emit`, `main`'s exit one step
later. -/
theorem toy_reach : (source (toyP arch) toyProg).Reach [.out 72, .exit 0] sEnd := by
  refine ⟨s0, rfl, ?_⟩
  have r5 : (source (toyP arch) toyProg).Run s4 ([.exit 0] ++ []) sEnd := LRun.step ⟨0, st5 arch⟩ (.refl _)
  have r4 : (source (toyP arch) toyProg).Run s3 ([.out 72] ++ [.exit 0]) sEnd := LRun.step ⟨0, st4 arch⟩ r5
  have r3 : (source (toyP arch) toyProg).Run s2 ([] ++ [.out 72, .exit 0]) sEnd := LRun.step ⟨0, st3 arch⟩ r4
  have r2 : (source (toyP arch) toyProg).Run s1 ([] ++ [.out 72, .exit 0]) sEnd := LRun.step ⟨0, st2 arch⟩ r3
  exact LRun.step ⟨0, st1 arch⟩ r2

end Spike.Test.OutToySrc
