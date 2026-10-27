import Spike.Lib.Src.GroupAlg
import Spike.Lib.LowerNode1

/-!
**The node invariant with locatives** (ISA-neutral): `NJ` asks every bound
word to be a number (`EnvNum`), which fails once a locative or a pointer is
bound. `NJ'` asks it only of the words of numeric bindings (`EnvNum'`: of a
type `numTy`, an integer, a fixed-width number or lanes under refinements),
which is all the checked arithmetic, the `if` and a one-word `ret` read.

- `numTy`, `EnvNum'`, `EnvNum.toEnvNum'` (every `EnvNum` environment is
  `EnvNum'`), `EnvNum'.cons`, `EnvNum'.cons_of_not`, `EnvNum'.evalAt`;
- `NJ'`, `NJ.toNJ'`: the lift from `NJ`;
- per construct, as `NJ`'s with the operands numeric (`numTy`):
  `NJ'.atom` (no extra premise), `NJ'.ops`, `NJ'.add_ok`, `NJ'.sub_ok`,
  `NJ'.ifeq`, and `NJ'.add_ovf` into `AbSrc'` (`AbSrc` with `EnvNum'`;
  `AbSrc.toAbSrc'` the lift).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Scc.Sem (ValRep)

/-! ## Numeric bindings -/

/-- **A numeric type**: an integer, a fixed-width number or a lanes word,
under refinements; its one word is a number. -/
def numTy : Ty → Bool
  | .int | .intS _ | .fix _ _ | .lanes _ _ => true
  | .refine t _ => numTy t
  | _ => false

/-- **Every word of a numeric binding is a number below `2^64`.** -/
def EnvNum' (env : TermRun.Env) : Prop :=
  ∀ b ∈ env, numTy b.2.1 = true → ∀ w ∈ b.2.2, ∃ n, w.val = .num n ∧ n < 2 ^ 64

theorem EnvNum.toEnvNum' {env : TermRun.Env} (h : EnvNum env) : EnvNum' env := fun b hb _ => h b hb

theorem EnvNum'.cons {env : TermRun.Env} (h : EnvNum' env) {x : String} {t : Ty} {ws : List TermRun.Word}
    (hw : numTy t = true → ∀ w ∈ ws, ∃ n, w.val = .num n ∧ n < 2 ^ 64) : EnvNum' ((x, t, ws) :: env) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hw
  · exact h b hb

/-- A binding of a type that is not numeric keeps `EnvNum'`. -/
theorem EnvNum'.cons_of_not {env : TermRun.Env} (h : EnvNum' env) {x : String} {t : Ty} (ht : numTy t = false)
    (ws : List TermRun.Word) : EnvNum' ((x, t, ws) :: env) :=
  h.cons fun h' => by rw [ht] at h'; cases h'

/-- **A numeric atom's words are numbers**, a literal's below `2^64` as
`sevalAt` places it. -/
theorem EnvNum'.evalAt {env : TermRun.Env} (h : EnvNum' env) {s : SEnv} {a : At} {t t' : Ty}
    {pls : List WordPl} {ws : List TermRun.Word} (hs : sevalAt s a = some (t', pls))
    (he : TermRun.evalAt env a = some (t, ws)) (ht : numTy t = true) :
    ∀ w ∈ ws, ∃ n, w.val = .num n ∧ n < 2 ^ 64 := by
  cases a with
  | var x =>
    simp only [TermRun.evalAt, TermRun.lookupE, Option.map_eq_some_iff] at he
    obtain ⟨⟨y, u, vs⟩, hb, he⟩ := he
    cases he
    exact h _ (List.mem_of_find?_eq_some hb) ht
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

/-- **A binding's words keep `EnvNum'`** where they come from an atom of
the same type. -/
theorem EnvNum'.cons_evalAt {env : TermRun.Env} (h : EnvNum' env) {s : SEnv} {a : At} {t t' : Ty}
    {pls : List WordPl} {ws : List TermRun.Word} (hs : sevalAt s a = some (t', pls))
    (he : TermRun.evalAt env a = some (t, ws)) (x : String) : EnvNum' ((x, t, ws) :: env) :=
  h.cons fun ht => h.evalAt hs he ht

/-! ## The node invariant -/

section NJ'

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}

/-- **The node invariant with locatives**: the source runs locally to a
control at term `t` that the symbolic environment `s` represents, operands
valued in `sl`, every word of a numeric binding a number (`EnvNum'`). -/
def NJ' (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int) (t : Expr) (s : SEnv)
    (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  ∃ c', LocalRun p c c' ∧ NodeJ lbl rs t s sl c' ∧ EnvNum' c'.env

/-- **`NJ` is `NJ'`.** -/
theorem NJ.toNJ' {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NJ p lbl rs t s sl c) :
    NJ' p lbl rs t s sl c :=
  let ⟨c', hr, hj, hn⟩ := h
  ⟨c', hr, hj, hn.toEnvNum'⟩

theorem NJ'.of_nodeJ {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NodeJ lbl rs t s sl c)
    (hn : EnvNum' c.env) : NJ' p lbl rs t s sl c :=
  ⟨c, .refl c, h, hn⟩

/-- A local run before the node keeps it. -/
theorem NJ'.pre {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c c0 : Ctl} (h0 : LocalRun p c0 c)
    (h : NJ' p lbl rs t s sl c) : NJ' p lbl rs t s sl c0 :=
  let ⟨c', hr, hj, hn⟩ := h
  ⟨c', h0.trans hr, hj, hn⟩

/-- **`let x = a` emits nothing**: the node invariant moves past it, `x`
bound to `a`'s placements. -/
theorem NJ'.atom {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t : Ty}
    {pls : List WordPl} (h : NJ' p lbl rs (.let_ x (.atom a) e) s sl c) (ha : sevalAt s a = some (t, pls)) :
    NJ' p lbl rs e ((x, t, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨hr2, hj2⟩ := hj.step (Spike.Lib.Form.localStep_atom hj.1 he) hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons_evalAt ha he x⟩

/-- **Two numeric one-word operands at a node**: each placed at one
operand, valued `va`, `vb`; the source reaches a control at the node's term
whose operand words are the numbers `va`, `vb` (below `2^64`). -/
theorem NJ'.ops {t : Expr} {a b : At} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ' p lbl rs t s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    ∃ c1 wa wb, LocalRun p c c1 ∧ NodeJ lbl rs t s sl c1 ∧ EnvNum' c1.env ∧
      TermRun.evalAt c1.env a = some (ta, [wa]) ∧ TermRun.evalAt c1.env b = some (tb, [wb]) ∧
      ValRep lbl wa.val va ∧ ValRep lbl wb.val vb ∧ wa.val = .num va ∧ wb.val = .num vb ∧
      va < 2 ^ 64 ∧ vb < 2 ^ 64 := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨wsa, hea, hwa⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨wsb, heb, hwb⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  have hna := hn.evalAt ha hea hta
  have hnb := hn.evalAt hb heb htb
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

/-- **The checked `+`, fall-through**: without carry the source adds; `x`
bound to the sum, placed at IR register `d` whose cell `k` holds it (the
other placed operands' cells off `k`). -/
theorem NJ'.add_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ' p lbl rs (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hlt : va + vb < 2 ^ 64)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va + vb) :
    NJ' p lbl rs e ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hna, hnb, -, -⟩ := h.ops ha hb hta htb hva hvb
  have hst := localStep_add (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst ?_ ?_).2, hn.cons fun _ => ?_⟩
  · refine ⟨⟨va + vb, ?_, Scc.Sem.valRep_addW hra hrb hlt⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va + vb, by simp [TermRun.addW, hna, hnb, TermRun.cst]; rfl, hlt⟩

/-- **The saturating `-`**: the source subtracts (truncated); `x` bound to
the difference, placed at IR register `d` whose cell `k` holds it. -/
theorem NJ'.sub_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ' p lbl rs (.let_ x (.sub a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va - vb) :
    NJ' p lbl rs e ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hna, hnb, hlta, -⟩ := h.ops ha hb hta htb hva hvb
  have hst := localStep_sub (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst ?_ ?_).2, hn.cons fun _ => ?_⟩
  · refine ⟨⟨va - vb, ?_, Scc.Sem.valRep_subW hra hrb⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va - vb, by simp [TermRun.subW, hna, hnb, TermRun.cst]; rfl, by omega⟩

/-- **The integer `if`**: at a node at `if a = b then yes else no`, numeric
operands valued `va`, `vb`, the node invariant moves to the branch `va = vb`
selects, the symbolic environment and slots unchanged. -/
theorem NJ'.ifeq {a b : At} {yes no : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ' p lbl rs (.ifeq a b yes no) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    NJ' p lbl rs (if va = vb then yes else no) s sl c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, -, -, hna, hnb, -, -⟩ := h.ops ha hb hta htb hva hvb
  have hst := localStep_ifeq (p := p) hj.1 hea heb hna hnb
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, hj.2.2⟩, hn⟩

/-- **The source at the overflow abort, with locatives**: `AbSrc` with
`EnvNum'` for `EnvNum`. -/
def AbSrc' (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int) (s : SEnv)
    (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  OvfReady c ∧ EnvNum' c.env ∧ SRep lbl (opdVal rs sl) s c.env ∧
    ∀ y ∈ Scc.Sem.exprFv c.term, (lookupS s y).isSome

theorem AbSrc.toAbSrc' {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : AbSrc lbl rs s sl c) :
    AbSrc' lbl rs s sl c :=
  ⟨h.1, h.2.1.toEnvNum', h.2.2⟩

/-- **The checked `+`, carry**: at a node at `let x = a + b` whose numeric
operands' values sum to at least `2^64` (each free variable placed), the
source runs locally to a control at the `+` that is `AbSrc'`. -/
theorem NJ'.add_ovf {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ' p lbl rs (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hge : 2 ^ 64 ≤ va + vb)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome) :
    ∃ c1, LocalRun p c c1 ∧ AbSrc' lbl rs s sl c1 := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, -, -, hna, hnb, -, -⟩ := h.ops ha hb hta htb hva hvb
  refine ⟨c1, hr, ⟨x, a, b, e, ta, tb, wa, wb, va, vb, hj.1, hea, heb, hna, hnb, hge⟩, hn, hj.2.2, ?_⟩
  rw [hj.1]; exact htot

end NJ'

end Spike.Lib.LowerNode
