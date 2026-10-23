/-
**Node invariants of a lowered `Accepted0` body** (ISA-neutral).

The node invariant at a point of a lowered body is `NJ`: the source runs
locally to a control at the point's term whose environment the lowering's
environment (`ofEnv`) represents, operands valued in a slot map `rs`.

- `NJ.atom`: `let x = a` emits nothing; the node invariant moves past it.
- `NJ.add`, `NJ.add_ok`: the checked `+`'s operands and its fall-through.
- `OvfRep`: the overflow edge's source (`OvfReady` under the typing guard:
  `OvfRep.ovfReady`).
-/
import Spike.Lib.Form
import Spike.Lib.Src
import Spike.Lib.Typed
import Scc.Lower.Inv
import Spike.Lib.Region

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Scc.Sem (ValRep)

set_option linter.unusedSimpArgs false

/-! ## The lowering's environment as a symbolic one (ISA-neutral) -/

/-- **The lowering's environment as a symbolic environment**: each word one
operand. -/
def ofEnv (env : Scc.Lower.Env) : SEnv := env.map fun b => (b.1, b.2.1, b.2.2.map .one)

theorem lookupS_ofEnv (env : Scc.Lower.Env) (x : String) :
    lookupS (ofEnv env) x = (env.find? (·.1 == x)).map fun b => (b.2.1, b.2.2.map .one) := by
  induction env with
  | nil => rfl
  | cons b env ih =>
    by_cases h : b.1 = x
    · simp [lookupS, ofEnv, List.find?_cons, h]
    · have hb : (b.1 == x) = false := by simp [h]
      simp only [lookupS, ofEnv, List.map_cons, List.find?_cons, hb] at ih ⊢
      exact ih

/-- **An atom's placements are its lowering's words**, each one operand. -/
theorem sevalAt_ofEnv {env : Scc.Lower.Env} {a : At} {t : Ty} {ws : List Scc.IR.Operand}
    (h : Scc.Lower.Inv.atomV env a = some (t, ws)) : sevalAt (ofEnv env) a = some (t, ws.map .one) := by
  cases a with
  | var x =>
    simp only [Scc.Lower.Inv.atomV, Option.map_eq_some_iff] at h
    obtain ⟨⟨y, u, vs⟩, hf, he⟩ := h
    cases he
    simp [sevalAt, lookupS_ofEnv, hf]
  | lit n =>
    simp only [Scc.Lower.Inv.atomV] at h
    split at h
    · cases h
    · rename_i hn
      cases h
      simp [sevalAt, show n < 2 ^ 64 by omega, Scc.Lower.imm]
  | unit =>
    simp only [Scc.Lower.Inv.atomV, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-! ## Node invariants (ISA-neutral) -/

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}

/-- **Every bound word is a number below `2^64`** (an `Accepted0` body binds
only literals and checked sums). -/
def EnvNum (env : TermRun.Env) : Prop := ∀ b ∈ env, ∀ w ∈ b.2.2, ∃ n, w.val = .num n ∧ n < 2 ^ 64

theorem EnvNum.cons {env : TermRun.Env} (h : EnvNum env) {x : String} {t : Ty} {ws : List TermRun.Word}
    (hw : ∀ w ∈ ws, ∃ n, w.val = .num n ∧ n < 2 ^ 64) : EnvNum ((x, t, ws) :: env) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hw
  · exact h b hb

/-- **An atom's words in a numeric environment are numbers**, a literal's
below `2^64` as `sevalAt` places it. -/
theorem EnvNum.evalAt {env : TermRun.Env} (h : EnvNum env) {s : SEnv} {a : At} {t t' : Ty}
    {pls : List WordPl} {ws : List TermRun.Word} (hs : sevalAt s a = some (t', pls))
    (he : TermRun.evalAt env a = some (t, ws)) : ∀ w ∈ ws, ∃ n, w.val = .num n ∧ n < 2 ^ 64 := by
  cases a with
  | var x =>
    simp only [TermRun.evalAt, TermRun.lookupE, Option.map_eq_some_iff] at he
    obtain ⟨⟨y, u, vs⟩, hb, he⟩ := he
    cases he
    exact h _ (List.mem_of_find?_eq_some hb)
  | lit n =>
    simp only [sevalAt] at hs
    split at hs
    · rename_i hn
      simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      simp only [List.mem_singleton, forall_eq]
      exact ⟨n, rfl, hn⟩
    · cases hs
  | unit =>
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    simp

/-- **The node invariant**: the source runs locally to a control at term `t`
that the symbolic environment `s` represents, operands valued in `sl`, every
bound word a number (`EnvNum`). -/
def NJ (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int) (t : Expr) (s : SEnv)
    (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  ∃ c', LocalRun p c c' ∧ NodeJ lbl rs t s sl c' ∧ EnvNum c'.env

theorem NJ.of_nodeJ {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NodeJ lbl rs t s sl c)
    (hn : EnvNum c.env) : NJ p lbl rs t s sl c :=
  ⟨c, .refl c, h, hn⟩

/-- **`let x = a` emits nothing**: the node invariant moves past it, `x`
bound to `a`'s placements. -/
theorem NJ.atom {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t : Ty}
    {pls : List WordPl} (h : NJ p lbl rs (.let_ x (.atom a) e) s sl c) (ha : sevalAt s a = some (t, pls)) :
    NJ p lbl rs e ((x, t, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨hr2, hj2⟩ := hj.step (Spike.Lib.Form.localStep_atom hj.1 he) hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons (hn.evalAt ha he)⟩

/-- A number represented by `v` is `v`. -/
theorem valRep_num {n v : Nat} (h : ValRep lbl (.num n) v) : v = n := h.2

/-- **The checked `+`'s operands**: at a node at `let x = a + b`, each
operand placed at one operand, valued `va`, `vb`, the source reaches a
control at the `+` whose operand words are the numbers `va`, `vb`. -/
theorem NJ.add {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ p lbl rs (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    ∃ c1 wa wb, LocalRun p c c1 ∧ NodeJ lbl rs (.let_ x (.add a b) e) s sl c1 ∧ EnvNum c1.env ∧
      TermRun.evalAt c1.env a = some (ta, [wa]) ∧ TermRun.evalAt c1.env b = some (tb, [wb]) ∧
      ValRep lbl wa.val va ∧ ValRep lbl wb.val vb ∧ wa.val = .num va ∧ wb.val = .num vb := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨wsa, hea, hwa⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨wsb, heb, hwb⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  have hna := hn.evalAt ha hea
  have hnb := hn.evalAt hb heb
  match wsa, wsb, hwa, hwb, hna, hnb with
  | [wa], [wb], ⟨⟨v, hv, hra⟩, _⟩, ⟨⟨u, hu, hrb⟩, _⟩, hna, hnb =>
    rw [hva] at hv; rw [hvb] at hu
    cases hv; cases hu
    obtain ⟨n, hn1, -⟩ := hna wa (by simp)
    obtain ⟨m, hm1, -⟩ := hnb wb (by simp)
    have e1 := hra; rw [hn1] at e1
    have e2 := hrb; rw [hm1] at e2
    rw [valRep_num e1] at hra ⊢; rw [valRep_num e2] at hrb ⊢
    exact ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hn1, hm1⟩

/-- **The source at a `+` whose operands' values sum to at least `2^64`**:
words representing them (the overflow edge's source; `OvfReady` under the
typing guard). -/
def OvfRep (lbl : WeakMem.AllocLabel → Option Nat) (c : Ctl) : Prop :=
  ∃ x a b e ta tb wa wb va vb, c.term = .let_ x (.add a b) e ∧ TermRun.evalAt c.env a = some (ta, [wa]) ∧
    TermRun.evalAt c.env b = some (tb, [wb]) ∧ ValRep lbl wa.val va ∧ ValRep lbl wb.val vb ∧ 2 ^ 64 ≤ va + vb

/-- **Under the typing guard the overflow edge's source is `OvfReady`.** -/
theorem OvfRep.ovfReady {c : Ctl} (h : OvfRep lbl c) (ht : Typed p c) : OvfReady c := by
  obtain ⟨x, a, b, e, ta, tb, wa, wb, va, vb, hte, hea, heb, hra, hrb, hc⟩ := h
  obtain ⟨n, m, hn, hm, hnm⟩ := Scc.Sem.TypedAt.carry_nums ht hte hea heb hra hrb hc
  exact ⟨x, a, b, e, ta, tb, wa, wb, n, m, hte, hea, heb, hn, hm, hnm⟩

/-- **The source at the overflow abort** (the handover to the abort path):
about to overflow, every bound word a number, the environment represented
by `s` (operands valued in `sl`), every free variable of the term placed. -/
def AbSrc (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int) (s : SEnv)
    (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  OvfReady c ∧ EnvNum c.env ∧ SRep lbl (opdVal rs sl) s c.env ∧
    ∀ y ∈ Scc.Sem.exprFv c.term, (lookupS s y).isSome

/-- **The checked `+`, carry**: at a node at `let x = a + b` whose operands'
values sum to at least `2^64` (each free variable placed), the source runs
locally to a control at the `+` that is `AbSrc`. -/
theorem NJ.add_ovf {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ p lbl rs (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hge : 2 ^ 64 ≤ va + vb)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome) :
    ∃ c1, LocalRun p c c1 ∧ AbSrc lbl rs s sl c1 := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, -, -, hna, hnb⟩ := h.add ha hb hva hvb
  refine ⟨c1, hr, ⟨x, a, b, e, ta, tb, wa, wb, va, vb, hj.1, hea, heb, hna, hnb, hge⟩, hn, hj.2.2, ?_⟩
  rw [hj.1]; exact htot

/-- **The checked `+`, fall-through**: without carry the source adds; `x`
bound to the sum, placed at IR register `d` whose cell `k` holds it (the
other placed operands' cells off `k`). -/
theorem NJ.add_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ p lbl rs (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hlt : va + vb < 2 ^ 64)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va + vb) :
    NJ p lbl rs e ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hna, hnb⟩ := h.add ha hb hva hvb
  have hst := localStep_add (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst ?_ ?_).2, hn.cons ?_⟩
  · refine ⟨⟨va + vb, ?_, Scc.Sem.valRep_addW hra hrb hlt⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va + vb, by simp [TermRun.addW, hna, hnb, TermRun.cst]; rfl, hlt⟩

end Spike.Lib.LowerNode
