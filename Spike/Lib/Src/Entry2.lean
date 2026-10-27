/-
**A plain callee's entry, at the source** (ISA-neutral): the body's entry
node's source facts of an `Accepted2` code block with an `Int` parameter
(`plain2`) at its entry control, the parameter bound to one number word
represented by the value `v` in the parameter register's cell; the v2
twin of `nj_callee` (`Spike/Lib/LowerA64/CtxC.lean`).

- `entry2_rep`: the entry environment represented at the parameter's
  placement (`ofEnv2 (env2 d 1)`);
- `entry2_njB`: `NJB` at the entry's layouts (`params2`, `shapeOf`), no
  known values, buffers or labels;
- `entry2_slotRep`: `SlotRepAt` at the walk's facts at the entry.
-/
import Spike.Lib.Src.NJLB
import Spike.Lib.SlotRepAt
import Spike.Lib.Src.AbortImm2
import Spike.Lib.LowerShapeC2

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv lookupS SRep)
open Scc.Sem (ValRep)
open Scc.Lower (shapeOf params2)

/-- **The entry environment at the parameter's placement**: the parameter
`d.arg` (an `Int`) bound to the one word `w` that `v`, the value in the
parameter register's cell `k`, represents. -/
theorem entry2_rep {lbl : WeakMem.AllocLabel → Option Nat} {d : Decl} (hint : d.argTy = .int)
    {env : TermRun.Env} {w : TermRun.Word} {v : BitVec 64} (henv : env = [(d.arg, d.argTy, [w])])
    (hv : ValRep lbl w.val v.toNat) {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {k : Int}
    (hk : rs s!"{d.arg}.{0}" = some k) (hsl : sl k = v) :
    SRep lbl (opdVal rs sl) (ofEnv2 (Spike.Lib.LowerShape.env2 d 1)) env := by
  subst henv
  intro y t pls hl
  rw [lookupS_ofEnv2] at hl
  by_cases hy : d.arg = y
  · subst hy
    simp only [Spike.Lib.LowerShape.env2, Spike.Lib.LowerShape.paramsR, List.find?, beq_self_eq_true,
      Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    refine ⟨[w], by simp [TermRun.lookupE], ?_⟩
    rw [hint]
    refine ⟨⟨(sl k).toNat, ?_, ?_⟩, trivial⟩
    · show (rs _).map (fun k => (sl k).toNat) = _
      rw [hk]; rfl
    · rw [hsl]; exact hv
  · have hy' : (d.arg == y) = false := by simpa using hy
    simp [Spike.Lib.LowerShape.env2, hy'] at hl

/-- **The body's entry node's `NJB`** at the entry control `cE` (the body,
no hold, the parameter bound to the number word `w` that `v` represents),
at the entry's layouts and no known values, buffers or labels. -/
theorem entry2_njB {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {B : Nat} {d : Decl} (hint : d.argTy = .int) {cE : Ctl} {w : TermRun.Word} {v : BitVec 64}
    (hterm : cE.term = d.body) (hhold : cE.hold = none) (henv : cE.env = [(d.arg, d.argTy, [w])])
    (hv : ValRep lbl w.val v.toNat) (hn : IsNum w) {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64}
    {k : Int} (hk : rs s!"{d.arg}.{0}" = some k) (hsl : sl k = v) :
    NJB p lbl rs ((params2 d).map (·, shapeOf d.argTy)) [] [] (fun _ => False) #[] lsize B d.body
      (ofEnv2 (Spike.Lib.LowerShape.env2 d 1)) sl cE := by
  refine NJB.of_nodeJ ⟨hterm, hhold, entry2_rep hint henv hv hk hsl⟩ ?_ ?_ (memB_empty B) ?_
  · rw [henv]
    exact EnvLit.entry (by rw [hint]; rfl) (NumL.of_all fun w' hw' => by
      simp only [List.mem_singleton] at hw'; subst hw'; exact hn)
  · rw [henv]
    exact EnvB.entry (by rw [hint]; trivial)
  · rw [henv]
    intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact WordsSmall.isNum hn

/-- **The body's entry node's `SlotRepAt`** at the entry control `cE`,
from the walk's facts at the entry (its free variables bound, the
immediates `i`'s, the locatives' register bases). -/
theorem entry2_slotRep {lbl : WeakMem.AllocLabel → Option Nat} {i : Expr → String → Nat → Option Nat}
    {d : Decl} (hint : d.argTy = .int) {cE : Ctl} {w : TermRun.Word} {v : BitVec 64}
    (hterm : cE.term = d.body) (hhold : cE.hold = none) (henv : cE.env = [(d.arg, d.argTy, [w])])
    (hv : ValRep lbl w.val v.toNat) {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64}
    {k : Int} (hk : rs s!"{d.arg}.{0}" = some k) (hsl : sl k = v)
    (htot : ∀ y ∈ Scc.Sem.exprFv d.body, (lookupS (ofEnv2 (Spike.Lib.LowerShape.env2 d 1)) y).isSome)
    (hb : LocBaseRegAt (ofEnv2 (Spike.Lib.LowerShape.env2 d 1)) d.body)
    (hi : ImmIn i (ofEnv2 (Spike.Lib.LowerShape.env2 d 1)) d.body) :
    SlotRepAt i lbl rs sl cE :=
  SlotRepAt.of_nodeJ (t := d.body) ⟨hterm, hhold, entry2_rep hint henv hv hk hsl⟩ htot hb hi

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.entry2_njB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.entry2_njB

/-- info: 'Spike.Lib.LowerNode.entry2_slotRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.entry2_slotRep
