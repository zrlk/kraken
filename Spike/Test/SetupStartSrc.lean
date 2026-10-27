/-
**Prototype: the source starts before the setup block** (design spike).
Today's start (`SrcSem.mainInit`) enters `main` on a unit argument, which
fits `main(a : Unit)` only. For `main(a : S * Ptr pub Void)` with a setup
block `rodata(u : Unit) : S`, the start `setupStart` (`Scc/Sem/SrcOut.lean`) runs the setup
as an ordinary call of thread 0 and then enters `main`:

  `let r = call rodata u; let a = (r, me); tail main a`

with `u` the unit and `me` the main thread's `Ptr pub Void` stand-in
(`meW`, a parameter of the start). `rodata`'s `ret` has a frame below it, so
`mainExit` stays empty until `main` returns (`toy_reach`: a setup returning
`7` and a `main` returning its first component reach `[exit 7]` under the
single-thread parameters with this start).

- `step_src`: a thread step of thread 0 with a single successor, from a
  configuration where `main` has not returned and thread 0 has no promises,
  is a source step whose trace is the growth of `srcObs`.
-/
import Scc.Sem.SrcOut
import Spike.Lib.SrcRun
import Scc.Frontend

namespace Spike.Test.SetupStartSrc

open CoreLang CoreTerm TermRun
open Scc.Sem Scc.Sem.SrcSem
open Spike.Lib

/-! ## The start

`setupTerm`, `setupStart` and `setupInit` are the statement's definitions in
`Scc/Sem/SrcOut.lean` (namespace `Scc.Sem.SrcSem`, opened here). -/

/-! ## A generic step -/

/-- **A deterministic thread step of thread 0 is a source step**: its
single successor, with thread 0 having no promises after it (the empty
certificate), while `main` has not returned. -/
theorem step_src {P : SrcParams} {p : Prog} {s s' : Cfg} {th' : TTh} (hex : mainExit s = [])
    (hts : threadSteps p P.k P.arch s 0 = [s']) (h0 : s'.ths[0]? = some th') (hp : th'.promises = []) :
    (source P p).step 0 s ((srcObs P.hooks.trace s').drop (srcObs P.hooks.trace s).length) s' :=
  ⟨hex, .inl (.inl ⟨by simp [hts], ⟨_, .refl _, by simp [noPromises, h0, hp]⟩⟩), rfl⟩

/-! ## The toy -/

/-- The setup block: `let v = 7; ret v`. -/
def rodataD : Decl :=
  { name := "rodata", idx := [], arg := "u", argTy := .unit, retTy := .int,
    body := .let_ "v" (.atom (.lit 7)) (.ret (.var "v")) }

/-- `main`: `let (x, me) = a; ret x`. -/
def mainD : Decl :=
  { name := "main", idx := [], arg := "a", argTy := .prod .int (.ptr .pub .void), retTy := .int,
    body := .split (.var "a") "x" "me" (.ret (.var "x")) }

def toyProg : Prog := [rodataD, mainD]

-- A well-typed program, and `scc`'s entry check classifies it as a setup
-- program (`main(a : S * Ptr pub Void)` with `rodata(u : Unit) : S`).
#guard accepts (checkProg toyProg)
#guard (Scc.Frontend.entryOf "" toyProg).toOption.map (·.arg) == some Scc.Frontend.EntryArg.setupTid

/-- The single-thread parameters with the start before the setup. -/
def toyP (arch : WeakMem.Arch) : SrcParams := { arch, cap := 1, init := setupInit 1 }

/-- The stand-in word used in the run (any word works). -/
def meW : Word := cst (.num 0)

def s0 : Cfg := setupStart 1 meW

/-- The configurations along the run, as computed by `threadSteps`. -/
def nexts (arch : WeakMem.Arch) (s : Cfg) : Cfg :=
  (threadSteps toyProg .all arch s 0).headD s

def s1 (arch : WeakMem.Arch) : Cfg := nexts arch s0
def s2 (arch : WeakMem.Arch) : Cfg := nexts arch (s1 arch)
def s3 (arch : WeakMem.Arch) : Cfg := nexts arch (s2 arch)
def s4 (arch : WeakMem.Arch) : Cfg := nexts arch (s3 arch)
def s5 (arch : WeakMem.Arch) : Cfg := nexts arch (s4 arch)
def s6 (arch : WeakMem.Arch) : Cfg := nexts arch (s5 arch)

/-- **The toy's source reaches `[exit 7]`** from the start before the setup:
the call into `rodata`, its binding and return (into the wrapper's frame:
no exit), the pair, the tail call into `main`, its split and its `ret`. -/
theorem toy_reach (arch : WeakMem.Arch) : (source (toyP arch) toyProg).Reach [.exit 7] (s6 arch) := by
  refine ⟨s0, ⟨meW, rfl⟩, ?_⟩
  have st : ∀ s s' : Cfg, mainExit s = [] → threadSteps toyProg .all arch s 0 = [s'] →
      (∃ th', s'.ths[0]? = some th' ∧ th'.promises = []) →
      (source (toyP arch) toyProg).step 0 s ((srcObs (fun _ => []) s').drop (srcObs (fun _ => []) s).length) s' :=
    fun s s' hex hts ⟨th', h0, hp⟩ => step_src (P := toyP arch) hex hts h0 hp
  have go : ∀ s, (∃ th', s.ths[0]? = some th' ∧ th'.promises = []) → mainExit s = [] →
      threadSteps toyProg .all arch s 0 = [nexts arch s] →
      (∃ th', (nexts arch s).ths[0]? = some th' ∧ th'.promises = []) →
      (source (toyP arch) toyProg).step 0 s
        ((srcObs (fun _ => []) (nexts arch s)).drop (srcObs (fun _ => []) s).length) (nexts arch s) :=
    fun s _ hex hts hp => st s _ hex hts hp
  have e : ∀ s, mainExit s = [] → mainExit (nexts arch s) = [] →
      (srcObs (fun _ => []) (nexts arch s)).drop (srcObs (fun _ => []) s).length = [] := by
    intro s h h'; simp [srcObs, h, h', cutAtExit]
  have h1 := go s0 ⟨_, rfl, rfl⟩ (by decide) (by cases arch <;> rfl) (by cases arch <;> exact ⟨_, rfl, rfl⟩)
  have h2 := go (s1 arch) (by cases arch <;> exact ⟨_, rfl, rfl⟩) (by cases arch <;> decide)
    (by cases arch <;> rfl) (by cases arch <;> exact ⟨_, rfl, rfl⟩)
  have h3 := go (s2 arch) (by cases arch <;> exact ⟨_, rfl, rfl⟩) (by cases arch <;> decide)
    (by cases arch <;> rfl) (by cases arch <;> exact ⟨_, rfl, rfl⟩)
  have h4 := go (s3 arch) (by cases arch <;> exact ⟨_, rfl, rfl⟩) (by cases arch <;> decide)
    (by cases arch <;> rfl) (by cases arch <;> exact ⟨_, rfl, rfl⟩)
  have h5 := go (s4 arch) (by cases arch <;> exact ⟨_, rfl, rfl⟩) (by cases arch <;> decide)
    (by cases arch <;> rfl) (by cases arch <;> exact ⟨_, rfl, rfl⟩)
  have h6 := go (s5 arch) (by cases arch <;> exact ⟨_, rfl, rfl⟩) (by cases arch <;> decide)
    (by cases arch <;> rfl) (by cases arch <;> exact ⟨_, rfl, rfl⟩)
  rw [e _ (by decide) (by cases arch <;> decide)] at h1
  rw [e _ (by cases arch <;> decide) (by cases arch <;> decide)] at h2 h3 h4 h5
  have e6 : (srcObs (fun _ => []) (nexts arch (s5 arch))).drop (srcObs (fun _ => []) (s5 arch)).length =
      [.exit 7] := by
    cases arch <;> decide
  rw [e6] at h6
  let S := source (toyP arch) toyProg
  have r6 : S.Run (s5 arch) ([.exit 7] ++ []) (s6 arch) := LRun.step ⟨0, h6⟩ (.refl _)
  have r5 : S.Run (s4 arch) ([] ++ [.exit 7]) (s6 arch) := LRun.step ⟨0, h5⟩ r6
  have r4 : S.Run (s3 arch) ([] ++ [.exit 7]) (s6 arch) := LRun.step ⟨0, h4⟩ r5
  have r3 : S.Run (s2 arch) ([] ++ [.exit 7]) (s6 arch) := LRun.step ⟨0, h3⟩ r4
  have r2 : S.Run (s1 arch) ([] ++ [.exit 7]) (s6 arch) := LRun.step ⟨0, h2⟩ r3
  exact LRun.step ⟨0, h1⟩ r2

end Spike.Test.SetupStartSrc
