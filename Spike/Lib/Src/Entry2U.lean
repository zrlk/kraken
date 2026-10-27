/-
**A unit-parameter callee's entry, at the source** (ISA-neutral): the
body's entry node's source facts of an `Accepted2` code block with a `Unit`
parameter (the setup function `rodata(u)`) at its entry control, the
parameter bound to no words; the unit twin of `Spike/Lib/Src/Entry2.lean`.

- `entry2U_rep`: the entry environment represented at the parameter's
  (empty) placement (`ofEnv2 (env2 d 0)`);
- `entry2U_njB`: `NJB` at the entry's layouts (`params2`, empty at `Unit`),
  no known values, buffers or labels;
- `entry2U_slotRep`: `SlotRepAt` at the walk's facts at the entry.
-/
import Spike.Lib.Src.Entry2

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv lookupS SRep)
open Scc.Lower (shapeOf params2)

/-- **The entry environment at the parameter's placement**: the parameter
`d.arg` (a `Unit`) bound to no words. -/
theorem entry2U_rep {lbl : WeakMem.AllocLabel → Option Nat} {d : Decl} (hu : d.argTy = .unit)
    {env : TermRun.Env} (henv : env = [(d.arg, d.argTy, [])]) {val : Scc.IR.Operand → Option Nat} :
    SRep lbl val (ofEnv2 (Spike.Lib.LowerShape.env2 d 0)) env := by
  subst henv
  intro y t pls hl
  rw [lookupS_ofEnv2] at hl
  by_cases hy : d.arg = y
  · subst hy
    simp only [Spike.Lib.LowerShape.env2, Spike.Lib.LowerShape.paramsR, List.find?, beq_self_eq_true,
      Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨[], by simp [TermRun.lookupE], ?_⟩
    rw [hu]
    trivial
  · have hy' : (d.arg == y) = false := by simpa using hy
    simp [Spike.Lib.LowerShape.env2, hy'] at hl

/-- **The body's entry node's `NJB`** at the entry control `cE` (the body,
no hold, the parameter bound to no words), at the entry's layouts and no
known values, buffers or labels. -/
theorem entry2U_njB {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {B : Nat} {d : Decl} (hu : d.argTy = .unit) {cE : Ctl}
    (hterm : cE.term = d.body) (hhold : cE.hold = none) (henv : cE.env = [(d.arg, d.argTy, [])])
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} :
    NJB p lbl rs ((params2 d).map (·, shapeOf d.argTy)) [] [] (fun _ => False) #[] lsize B d.body
      (ofEnv2 (Spike.Lib.LowerShape.env2 d 0)) sl cE := by
  refine NJB.of_nodeJ ⟨hterm, hhold, entry2U_rep hu henv⟩ ?_ ?_ (memB_empty B) ?_
  · rw [henv]
    exact EnvLit.entry (by rw [hu]; rfl) (NumL.of_all fun w' hw' => by simp at hw')
  · rw [henv]
    exact EnvB.entry (by rw [hu]; trivial)
  · rw [henv]
    intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro w hw; cases hw

/-- **The body's entry node's `SlotRepAt`** at the entry control `cE`,
from the walk's facts at the entry (its free variables bound, the
immediates `i`'s, the locatives' register bases). -/
theorem entry2U_slotRep {lbl : WeakMem.AllocLabel → Option Nat} {i : Expr → String → Nat → Option Nat}
    {d : Decl} (hu : d.argTy = .unit) {cE : Ctl}
    (hterm : cE.term = d.body) (hhold : cE.hold = none) (henv : cE.env = [(d.arg, d.argTy, [])])
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64}
    (htot : ∀ y ∈ Scc.Sem.exprFv d.body, (lookupS (ofEnv2 (Spike.Lib.LowerShape.env2 d 0)) y).isSome)
    (hb : LocBaseRegAt (ofEnv2 (Spike.Lib.LowerShape.env2 d 0)) d.body)
    (hi : ImmIn i (ofEnv2 (Spike.Lib.LowerShape.env2 d 0)) d.body) :
    SlotRepAt i lbl rs sl cE :=
  SlotRepAt.of_nodeJ (t := d.body) ⟨hterm, hhold, entry2U_rep hu henv⟩ htot hb hi

end Spike.Lib.LowerNode

/-- info: 'Spike.Lib.LowerNode.entry2U_njB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.entry2U_njB

/-- info: 'Spike.Lib.LowerNode.entry2U_slotRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.entry2U_slotRep
