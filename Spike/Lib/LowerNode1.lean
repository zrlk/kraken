/-
**Node invariants of a lowered call-free `Accepted1` body** (ISA-neutral):
the saturating `-` and the integer `if`, next to `Spike/Lib/LowerNode.lean`'s
`let` of an atom and checked `+`.

- `localStep_ifeq`: `if a = b then yes else no` on two numbers is a local
  step to the branch;
- `NJ.ops`: at a node whose term reads two one-word operands, the source
  reaches a control at the same term whose operand words are the numbers the
  operands value;
- `NJ.sub_ok`: the saturating `-`; `x` bound to the truncated difference,
  placed at IR register `d`;
- `NJ.ifeq`: the `if` moves the node invariant to the branch the operands'
  values select, the symbolic environment unchanged.
-/
import Spike.Lib.LowerNode

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Scc.Sem (ValRep)

set_option linter.unusedSimpArgs false

/-- **`if a = b then yes else no` on two numbers is a local step** to the
branch their equality selects, the environment unchanged. -/
theorem localStep_ifeq {p : Prog} {c : Ctl} {a b : At} {yes no : Expr} {ta tb : Ty} {wa wb : TermRun.Word}
    {n m : Nat} (ht : c.term = .ifeq a b yes no) (ha : TermRun.evalAt c.env a = some (ta, [wa]))
    (hb : TermRun.evalAt c.env b = some (tb, [wb])) (hn : wa.val = .num n) (hm : wb.val = .num m) :
    LocalStep p c ⟨if n = m then yes else no, c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp only [TermRun.tstep, ht', ht, he, ha, hb, hn, hm]
  by_cases h : n = m <;> simp [h]

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}

/-- **Two one-word operands at a node**: each placed at one operand, valued
`va`, `vb`; the source reaches a control at the node's term whose operand
words are the numbers `va`, `vb` (below `2^64`). -/
theorem NJ.ops {t : Expr} {a b : At} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ p lbl rs t s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    ∃ c1 wa wb, LocalRun p c c1 ∧ NodeJ lbl rs t s sl c1 ∧ EnvNum c1.env ∧
      TermRun.evalAt c1.env a = some (ta, [wa]) ∧ TermRun.evalAt c1.env b = some (tb, [wb]) ∧
      ValRep lbl wa.val va ∧ ValRep lbl wb.val vb ∧ wa.val = .num va ∧ wb.val = .num vb ∧
      va < 2 ^ 64 ∧ vb < 2 ^ 64 := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨wsa, hea, hwa⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨wsb, heb, hwb⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  have hna := hn.evalAt ha hea
  have hnb := hn.evalAt hb heb
  match wsa, wsb, hwa, hwb, hna, hnb with
  | [wa], [wb], ⟨⟨v, hv, hra⟩, _⟩, ⟨⟨u, hu, hrb⟩, _⟩, hna, hnb =>
    rw [hva] at hv; rw [hvb] at hu
    cases hv; cases hu
    obtain ⟨n, hn1, hn2⟩ := hna wa (by simp)
    obtain ⟨m, hm1, hm2⟩ := hnb wb (by simp)
    have e1 := hra; rw [hn1] at e1
    have e2 := hrb; rw [hm1] at e2
    rw [valRep_num e1] at hra ⊢; rw [valRep_num e2] at hrb ⊢
    exact ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hn1, hm1, hn2, hm2⟩

/-- **The saturating `-`**: the source subtracts (truncated); `x` bound to
the difference, placed at IR register `d` whose cell `k` holds it (the other
placed operands' cells off `k`). -/
theorem NJ.sub_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ p lbl rs (.let_ x (.sub a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va - vb) :
    NJ p lbl rs e ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hna, hnb, hlta, -⟩ := h.ops ha hb hva hvb
  have hst := localStep_sub (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst ?_ ?_).2, hn.cons ?_⟩
  · refine ⟨⟨va - vb, ?_, Scc.Sem.valRep_subW hra hrb⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va - vb, by simp [TermRun.subW, hna, hnb, TermRun.cst]; rfl, by omega⟩

/-- **The integer `if`**: at a node at `if a = b then yes else no`, the
operands valued `va`, `vb`, the node invariant moves to the branch
`va = vb` selects, the symbolic environment and slots unchanged. -/
theorem NJ.ifeq {a b : At} {yes no : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ p lbl rs (.ifeq a b yes no) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    NJ p lbl rs (if va = vb then yes else no) s sl c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, -, -, hna, hnb, -, -⟩ := h.ops ha hb hva hvb
  have hst := localStep_ifeq (p := p) hj.1 hea heb hna hnb
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, hj.2.2⟩, hn⟩

end Spike.Lib.LowerNode
