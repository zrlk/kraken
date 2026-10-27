/-
**A control placed in a slot file at no label** (ISA-neutral): a control
whose term's free variables are bound to words that are not locatives is
placed (`SlotRepAt`) at the placement with no label as soon as it is at
any placement. The symbolic environment is cut to the term's free
variables (`SEnv.onFv`): the representation reads the placement only
through locatives (`ValRep`, `LocRep`), the register bases and immediates
only at the free variables (`LocBaseRegAt`, `ImmIn`).

- `SEnv.onFv`, `lookupS_onFv`: the symbolic environment cut to a list of
  variables;
- `WordsRep.none_of_noLoc`: words that are not locatives at their
  placements at no label;
- `SlotRepAt.none_of_noLoc`: a control placed at no label when its term's
  free variables' words are not locatives;
- `SlotRepAt.none_of_newBuf`: at an allocation `let x = newBuf a τ in e`
  whose free variables are the count's (`exprFv … = atVars a`), the count
  a number (`numOf`).
-/
import Spike.Lib.SlotRepAt

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib.Form (SEnv lookupS WordPl WordRep WordsRep SRep opdVal LocRep)

/-- **The symbolic environment cut to the variables `vs`.** -/
def SEnv.onFv (s : SEnv) (vs : List String) : SEnv := s.filter (fun e => decide (e.1 ∈ vs))

/-- A variable's binding in the cut environment: its own among `vs`, else none. -/
theorem lookupS_onFv (s : SEnv) (vs : List String) (y : String) :
    lookupS (SEnv.onFv s vs) y = if y ∈ vs then lookupS s y else none := by
  induction s with
  | nil => simp [SEnv.onFv, lookupS]
  | cons e s ih =>
    obtain ⟨z, t, pls⟩ := e
    simp only [SEnv.onFv, lookupS] at ih ⊢
    by_cases hz : z ∈ vs
    · by_cases hzy : z = y
      · subst hzy; simp [hz]
      · have hb : (z == y) = false := by simpa [beq_iff_eq] using hzy
        simp only [List.filter_cons, hz, decide_true, ite_true, List.find?_cons, hb]
        exact ih
    · by_cases hzy : z = y
      · subst hzy
        simp only [List.filter_cons, hz, decide_false, ite_false, ite_false] at ih ⊢
        exact ih
      · have hb : (z == y) = false := by simpa [beq_iff_eq] using hzy
        simp only [List.filter_cons, hz, decide_false, List.find?_cons, hb]
        exact ih

/-- **Words that are not locatives at their placements at no label**: the
placement reads the labels only through a locative's value. -/
theorem WordsRep.none_of_noLoc {lbl : WeakMem.AllocLabel → Option Nat} {val : Scc.IR.Operand → Option Nat} :
    ∀ {ws : List TermRun.Word} {pls : List WordPl}, WordsRep lbl val ws pls →
      (∀ w ∈ ws, ∀ a tag, w.val ≠ .loc a tag) → WordsRep (fun _ => none) val ws pls
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | w :: ws, pl :: pls, h, hn => by
    refine ⟨?_, WordsRep.none_of_noLoc h.2 fun w' hw' => hn w' (List.mem_cons_of_mem _ hw')⟩
    have hw := hn w List.mem_cons_self
    obtain ⟨h1, -⟩ := h
    cases pl with
    | one o =>
      obtain ⟨v, hv, hr⟩ := h1
      refine ⟨v, hv, ?_⟩
      revert hw hr
      cases w.val with
      | loc a tag => intro hw _; exact absurd rfl (hw a tag)
      | _ => intro _ hr; exact hr
    | loc b off =>
      obtain ⟨vb, vo, hb, ho, hr⟩ := h1
      refine ⟨vb, vo, hb, ho, ?_⟩
      revert hw hr
      cases w.val with
      | loc a tag => intro hw _; exact absurd rfl (hw a tag)
      | _ => intro _ hr; exact hr

/-- **A control placed at no label** when its term's free variables'
words are not locatives (`noLoc`): the symbolic environment cut to the
term's free variables (`SEnv.onFv`). -/
theorem SlotRepAt.none_of_noLoc {i : Expr → String → Nat → Option Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {c : Ctl} (h : SlotRepAt i lbl rs sl c)
    (hn : ∀ y ∈ Scc.Sem.exprFv c.term, ∀ t ws, TermRun.lookupE c.env y = some (t, ws) →
      ∀ w ∈ ws, ∀ a tag, w.val ≠ .loc a tag) :
    SlotRepAt i (fun _ => none) rs sl c := by
  obtain ⟨s, hs, htot, hb, hi⟩ := h
  refine ⟨SEnv.onFv s (Scc.Sem.exprFv c.term), fun x t pls hx => ?_, fun y hy => ?_, fun y hy => ?_, fun x k v hx => ?_⟩
  · rw [lookupS_onFv] at hx
    by_cases hxf : x ∈ Scc.Sem.exprFv c.term
    · simp only [hxf, ↓reduceIte] at hx
      obtain ⟨ws, he, hw⟩ := hs x t pls hx
      exact ⟨ws, he, WordsRep.none_of_noLoc hw (hn x hxf t ws he)⟩
    · simp only [hxf, ↓reduceIte] at hx; cases hx
  · rw [lookupS_onFv]; simp only [hy, ↓reduceIte]; exact htot y hy
  · intro ty pls hl
    rw [lookupS_onFv] at hl; simp only [hy, ↓reduceIte] at hl
    exact hb y hy ty pls hl
  · rw [lookupS_onFv] at hx
    by_cases hxf : x ∈ Scc.Sem.exprFv c.term
    · simp only [hxf, ↓reduceIte] at hx; exact hi x k v hx
    · simp only [hxf, ↓reduceIte] at hx; cases hx

/-- **An allocation's control placed at no label**: at `let x = newBuf a
τ in e` whose free variables are the count's (`hfv`), the count `a`
evaluating to words of a number (`hev`, `hn`). -/
theorem SlotRepAt.none_of_newBuf {i : Expr → String → Nat → Option Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {rs : Scc.IR.Reg → Option Int} {sl : Int → BitVec 64} {c : Ctl} {x : String} {a : At} {τ : Ty} {e : Expr}
    {ta : Ty} {ws : List TermRun.Word} {n : Nat} (h : SlotRepAt i lbl rs sl c)
    (ht : c.term = .let_ x (.newBuf a τ) e) (hfv : Scc.Sem.exprFv (.let_ x (.newBuf a τ) e) = Scc.Sem.atVars a)
    (hev : TermRun.evalAt c.env a = some (ta, ws)) (hn : TermRun.numOf ws = some n) :
    SlotRepAt i (fun _ => none) rs sl c := by
  refine h.none_of_noLoc fun y hy t ws' he w hw a' tag hl => ?_
  rw [ht, hfv] at hy
  cases a with
  | var z =>
    simp only [Scc.Sem.atVars, List.mem_singleton] at hy
    subst hy
    simp only [TermRun.evalAt, he, Option.some.injEq, Prod.mk.injEq] at hev
    obtain ⟨-, rfl⟩ := hev
    unfold TermRun.numOf at hn
    split at hn
    · rename_i w0
      simp only [List.mem_singleton] at hw
      subst hw
      rw [hl] at hn
      cases hn
    · cases hn
  | _ => simp [Scc.Sem.atVars] at hy

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.SlotRepAt.none_of_newBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.SlotRepAt.none_of_newBuf
