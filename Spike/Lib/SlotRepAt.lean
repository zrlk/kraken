/-
**A control's words at their placements in a slot file** (ISA-neutral):
the facts a node invariant keeps of its source control `c` itself, so that
the control is placed (`PlacedS`) at every state of a block, even where it
lags the node's term (a code-free `let` the source has not taken yet,
whose binding may shadow a variable `c` still reads).

- `LocBaseRegAt s t`: every locative placement of a free variable of `t`
  has a register base (Scc.Sem's `WordPlace.loc` has no immediate base);
- `SlotRepAt i lbl rs sl c`: some symbolic environment represents `c`'s in
  the slot file `sl` (`SRep`), places every free variable of `c`'s term,
  with register bases, its immediates `i`'s at `c`'s term (`ImmIn`);
- `SlotRepAt.of_nodeJ`, `SlotRepAt.of_nodeJE`: from a node invariant at `c`
  itself (`NodeJ`, or `NodeJE` through `SEnv.retype`: `SlotRepAt.of_srepE`,
  `ImmIn.retype`, `LocBaseRegAt.retype`) and the walk's facts at its term.
-/
import Spike.Lib.LowerEnvImm
import Spike.Lib.FormE

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib.Form (SEnv lookupS WordPl SRep SRepE opdVal NodeJ NodeJE)

/-- **Every locative placement of a free variable of `t` has a register
base** in the symbolic environment `s`. -/
def LocBaseRegAt (s : SEnv) (t : Expr) : Prop :=
  ∀ y ∈ Scc.Sem.exprFv t, ∀ ty pls, lookupS s y = some (ty, pls) → ∀ b o, WordPl.loc b o ∈ pls →
    ∃ r, b = .reg r

/-- **The control `c` placed in the slot file `sl`**: a symbolic
environment representing `c`'s environment with operands valued in `sl`
through the register-slot map `rs`, placing every free variable of `c`'s
term with register bases for its locatives, its immediates the table `i`'s
at `c`'s term. -/
def SlotRepAt (i : Expr → String → Nat → Option Nat) (lbl : WeakMem.AllocLabel → Option Nat)
    (rs : Scc.IR.Reg → Option Int) (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  ∃ s, SRep lbl (opdVal rs sl) s c.env ∧ (∀ y ∈ Scc.Sem.exprFv c.term, (lookupS s y).isSome) ∧
    LocBaseRegAt s c.term ∧ ImmIn i s c.term

/-- **`SlotRepAt` from a node invariant at the control itself** and the
walk's facts at its term `t`: the free variables placed, register bases,
the immediates `i`'s. -/
theorem SlotRepAt.of_nodeJ {i : Expr → String → Nat → Option Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {c : Ctl} {t : Expr} {s : SEnv}
    (h : NodeJ lbl rs t s sl c) (htot : ∀ y ∈ Scc.Sem.exprFv t, (lookupS s y).isSome)
    (hb : LocBaseRegAt s t) (hi : ImmIn i s t) : SlotRepAt i lbl rs sl c := by
  obtain ⟨ht, -, hs⟩ := h
  subst ht
  exact ⟨s, hs, htot, hb, hi⟩

/-- **Retyping keeps the immediates.** -/
theorem ImmIn.retype {i : Expr → String → Nat → Option Nat} {s : SEnv} {t : Expr} (env : TermRun.Env)
    (h : ImmIn i s t) : ImmIn i (s.retype env) t := by
  intro x k v hx
  rw [Spike.Lib.Form.lookupS_retype_word] at hx
  exact h x k v hx

/-- **Retyping keeps the register bases.** -/
theorem LocBaseRegAt.retype {s : SEnv} {t : Expr} (env : TermRun.Env) (h : LocBaseRegAt s t) :
    LocBaseRegAt (s.retype env) t := by
  intro y hy ty pls hl b o hb
  rw [Spike.Lib.Form.lookupS_retype] at hl
  obtain ⟨⟨t0, q⟩, h0, he⟩ := Option.map_eq_some_iff.mp hl
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  exact h y hy t0 q h0 b o hb

/-- **The register bases at a checked `+`** of one-word operands: the
continuation's under the bound variable (the operands place no locative). -/
theorem LocBaseRegAt.let_add {s : SEnv} {x : String} {a b : At} {e : Expr} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {pl : List WordPl} (hsa : Spike.Lib.Form.sevalAt s a = some (ta, [.one pa]))
    (hsb : Spike.Lib.Form.sevalAt s b = some (tb, [.one pb])) (h : LocBaseRegAt ((x, .int, pl) :: s) e) :
    LocBaseRegAt s (.let_ x (.add a b) e) := by
  intro y hy ty pls hl b' o hm
  simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
  rcases hy with (hy | hy) | ⟨hy, hne⟩
  · cases a with
    | var z =>
      simp only [Scc.Sem.atVars, List.mem_singleton] at hy
      subst hy
      rw [Spike.Lib.Form.sevalAt, hl] at hsa
      cases hsa
      simp at hm
    | _ => simp [Scc.Sem.atVars] at hy
  · cases b with
    | var z =>
      simp only [Scc.Sem.atVars, List.mem_singleton] at hy
      subst hy
      rw [Spike.Lib.Form.sevalAt, hl] at hsb
      cases hsb
      simp at hm
    | _ => simp [Scc.Sem.atVars] at hy
  · refine h y hy ty pls ?_ b' o hm
    have hb : (x == y) = false := by simpa [beq_iff_eq] using Ne.symm hne
    simp only [lookupS, List.find?_cons, hb] at hl ⊢
    exact hl

/-- **`SlotRepAt` from a representation up to the buffers' literal
lengths** (`SRepE`): at the symbolic environment retyped at the source's
types (`SEnv.retype`, the placements kept). -/
theorem SlotRepAt.of_srepE {i : Expr → String → Nat → Option Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {c : Ctl} {s : SEnv}
    (hs : SRepE lbl (opdVal rs sl) s c.env) (htot : ∀ y ∈ Scc.Sem.exprFv c.term, (lookupS s y).isSome)
    (hb : LocBaseRegAt s c.term) (hi : ImmIn i s c.term) : SlotRepAt i lbl rs sl c := by
  refine ⟨s.retype c.env, hs.toSRep, fun y hy => ?_, hb.retype _, hi.retype _⟩
  rw [Spike.Lib.Form.lookupS_retype_isSome]; exact htot y hy

/-- **`SlotRepAt` from a node invariant up to the buffers' literal lengths**
(`NodeJE`): `SlotRepAt.of_srepE` at the node's symbolic environment. -/
theorem SlotRepAt.of_nodeJE {i : Expr → String → Nat → Option Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {c : Ctl} {t : Expr} {s : SEnv}
    (h : NodeJE lbl rs t s sl c) (htot : ∀ y ∈ Scc.Sem.exprFv t, (lookupS s y).isSome)
    (hb : LocBaseRegAt s t) (hi : ImmIn i s t) : SlotRepAt i lbl rs sl c := by
  obtain ⟨ht, -, hs⟩ := h
  subst ht
  exact SlotRepAt.of_srepE hs htot hb hi

/-- info: 'Spike.Lib.LowerNode.SlotRepAt.of_nodeJE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SlotRepAt.of_nodeJE

end Spike.Lib.LowerNode
