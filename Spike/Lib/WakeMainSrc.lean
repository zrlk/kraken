/-
**wake.w: main's source path after its `spawn`** (the source half of
`main_closed_wake`'s `hrun`/`hterm`/`hev`/`hval`/`htag`): main's source
control past its `spawn` is at `tail waitLoop [] c []` with `c` bound to the
flag cell's locative; one local step (the tail call) enters `waitLoop`'s
body, the atomic load `let d = load true c in …` of the flag.

- `main_src_load`: from any control at `tail waitLoop [] c []` with `c`
  bound to one word `w` (placed at `A`, a locative at offset 0), a local run
  to a control at `let x = load true a in e` with `a` evaluating to `[w]`.
- `main_src_load_spawn`: the same at the spawn's parent
  (`TermSpawnStep.spawnPar`, `x := t`), from the parent's `c` binding before
  the spawn (as `WakePreA.ClonePre` states it).
-/
import Spike.Lib.Seg
import Spike.Lib.WakeA64

namespace Spike.Lib.WakeMainSrc

open CoreLang CoreTerm
open Scc.Sem (ValRep)
open Spike.Lib.WakeT1 (wakeSrc)

/-- `waitLoop`'s body in wake.w: the flag's atomic load, then the test. -/
def waitBody : Expr :=
  .let_ "d" (.load true (.var "c"))
    (.ifeq (.var "d") (.lit 1) (.ret (.lit 0))
      (.let_ "p" (.ext .park .unit) (.tail "waitLoop" [] (.var "c") [])))

/-- The test after the flag load in `waitLoop`'s body. -/
def waitRest : Expr :=
  .ifeq (.var "d") (.lit 1) (.ret (.lit 0)) (.let_ "p" (.ext .park .unit) (.tail "waitLoop" [] (.var "c") []))

/-- **main's control at the flag load**: `waitLoop`'s body with `c` bound to
`w`. -/
def waitC (w : TermRun.Word) : Spike.Lib.Ctl :=
  ⟨waitBody, [("c", .ptr .pub .int, [w])], none⟩

theorem waitC_term (w : TermRun.Word) : (waitC w).term = .let_ "d" (.load true (.var "c")) waitRest := rfl

theorem waitC_ev (w : TermRun.Word) :
    TermRun.evalAt (waitC w).env (.var "c") = some (.ptr .pub .int, [w]) := by
  simp [waitC, TermRun.evalAt, TermRun.lookupE]

/-- **The tail call into `waitLoop`**, concretely: to `waitC w`. -/
theorem main_src_run {cP : Spike.Lib.Ctl} {ty : Ty} {w : TermRun.Word}
    (ht : cP.term = .tail "waitLoop" [] (.var "c") [])
    (hc : TermRun.evalAt cP.env (.var "c") = some (ty, [w])) :
    Spike.Lib.LocalRun wakeSrc cP (waitC w) := by
  refine .single ⟨rfl, ?_⟩
  intro g mem pairs th hg ht' he hσ _
  simp [TermRun.tstep, ht', ht, TermRun.enter, hg, he, hc, hσ, TermRun.ol, wakeSrc, waitC, waitBody]
  rfl

/-- **main's source from its tail call to the flag load**: from a control
at `tail waitLoop [] c []` with `c` bound to the word `w` at type `ty`, one
local step (the tail call) to `waitLoop`'s body, the load on `c`, at `[w]`. -/
theorem main_src_load {lbl : WeakMem.AllocLabel → Option Nat} {A : BitVec 64} {cP : Spike.Lib.Ctl}
    {ty : Ty} {w : TermRun.Word} (ht : cP.term = .tail "waitLoop" [] (.var "c") [])
    (hc : TermRun.evalAt cP.env (.var "c") = some (ty, [w])) (hval : ValRep lbl w.val A.toNat)
    (htag : ∃ sa, w.val = .loc sa 0) :
    ∃ (c0 : Spike.Lib.Ctl) (x : String) (a : CoreTerm.At) (e : Expr) (ty' : Ty) (w' : TermRun.Word),
      Spike.Lib.LocalRun wakeSrc cP c0 ∧ c0.term = .let_ x (.load true a) e ∧
      TermRun.evalAt c0.env a = some (ty', [w']) ∧ ValRep lbl w'.val A.toNat ∧ ∃ sa, w'.val = .loc sa 0 := by
  refine ⟨⟨waitBody, [("c", TermRun.close [] (.ptr .pub .int), [w])], none⟩, "d", .var "c", _, TermRun.close [] (.ptr .pub .int), w,
    .single ⟨rfl, ?_⟩, rfl, ?_, hval, htag⟩
  · intro g mem pairs th hg ht' he hσ _
    simp [TermRun.tstep, ht', ht, TermRun.enter, hg, he, hc, hσ, TermRun.ol, wakeSrc, waitBody]
  · simp [TermRun.evalAt, TermRun.lookupE]

/-- **At the spawn's parent**: main past its `spawn` (`TermSpawnStep.spawnPar`
of a thread at `let t = spawn … in tail waitLoop [] c []`, wake's
`WakePreA.spawnTerm`) with `c` bound before the spawn to the locative of a
label `l` placed at `A` (`WakePreA.ClonePre`). -/
theorem main_src_load_spawn {lbl : WeakMem.AllocLabel → Option Nat} {A : BitVec 64} {c : TermRun.Cfg}
    {i : Nat} {th0 : TermRun.TTh} {l : WeakMem.AllocLabel}
    (hc : TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hval : ValRep lbl (.loc ⟨l, 0⟩ 0) A.toNat) :
    ∃ (c0 : Spike.Lib.Ctl) (x : String) (a : CoreTerm.At) (e : Expr) (ty : Ty) (w : TermRun.Word),
      Spike.Lib.LocalRun wakeSrc
        (Spike.Lib.Ctl.of (TermSpawnStep.spawnPar c i th0 "t" (.tail "waitLoop" [] (.var "c") []))) c0 ∧
      c0.term = .let_ x (.load true a) e ∧ TermRun.evalAt c0.env a = some (ty, [w]) ∧
      ValRep lbl w.val A.toNat ∧ ∃ sa, w.val = .loc sa 0 := by
  refine main_src_load (ty := .ptr .pub .int) (w := TermRun.cst (.loc ⟨l, 0⟩ 0)) rfl ?_ hval ⟨⟨l, 0⟩, rfl⟩
  have : TermRun.evalAt (Spike.Lib.Ctl.of (TermSpawnStep.spawnPar c i th0 "t"
      (.tail "waitLoop" [] (.var "c") []))).env (.var "c") = TermRun.evalAt th0.env (.var "c") := by
    simp [Spike.Lib.Ctl.of, TermSpawnStep.spawnPar, TermRun.evalAt, TermRun.lookupE]
  rw [this, hc]

/-- info: 'Spike.Lib.WakeMainSrc.main_src_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_src_load

/-- info: 'Spike.Lib.WakeMainSrc.main_src_load_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_src_load_spawn

end Spike.Lib.WakeMainSrc
