/-
**The two immediate tables agree on an `Accepted0` program** (ISA-neutral):
every entry of `Accepted1`'s table `Scc.Lower.imms1Of [d]` (keyed by the
remaining term's `termKey`) is the lowering's table `immsOf d`'s (keyed by
the term's number of leading `let`s, `chainLen`).

- `imms1Of_sub_immsOf`: for `Accepted0 [d]`, `imms1Of [d] t x k = some n`
  gives `immsOf d t x k = some n`.

The converse fails off the walk: `immsOf` answers at every term with a
walk point's `chainLen` (at `ret z` for the body `let x = 1; ret x`, `x`'s
word 0 is `1`), `imms1Of` only at a walk point's `termKey`. The layout's
table enters `Scc.Sem.Correct` only through `Components.env_imm`, where a
larger table is a weaker requirement, so this inclusion is the direction
that carries a statement at `imms1Of [d]` to one at `immsOf d`.

The proof walks both tables' walks together (`walk_agree`): the source's
literal bindings (`Scc.Lower.litWalk`) and the lowering's environments
(`lowerEnvs`) visit the same terms, and a variable bound to a literal `n` in
the first is bound to the immediate `n` in the second (`LitImm`).
-/
import Spike.Lib.LowerEnvImm
import Scc.Lower.Spec1

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower.Inv (atomV)

/-- **Literal bindings as the environment's immediates**: a variable bound to
the literal `n` in `lits` has word 0 the immediate `n` in `env`. -/
def LitImm (lits : List (String × Option Nat)) (env : Scc.Lower.Env) : Prop :=
  ∀ y n, (lits.lookup y).join = some n → immOfEnv env y 0 = some n

/-- Every variable in `scope` is bound in `env`. -/
def ScopeBound (scope : List String) (env : Scc.Lower.Env) : Prop :=
  ∀ z ∈ scope, (env.find? (·.1 == z)).isSome

theorem atKey_single (a : At) : ∃ p, Scc.Lower.atKey a = [p] := by
  cases a <;> simp [Scc.Lower.atKey]

/-- **Equal keys, equal `let` counts**: a term with the `termKey` of an
`Accepted0` body has that body's number of leading `let`s. -/
theorem chainLen_of_termKey : ∀ (s : Expr) (scope : List String), Scc.Lower.body0 scope s = true →
    ∀ t : Expr, Scc.Lower.termKey t = Scc.Lower.termKey s → chainLen t = chainLen s := by
  intro s
  induction s with
  | let_ x op e ih =>
    intro scope hb t ht
    cases op with
    | atom a =>
      simp only [Scc.Lower.body0, Bool.and_eq_true] at hb
      obtain ⟨pa, hpa⟩ := atKey_single a
      cases t with
      | let_ y op' e' =>
        cases op' with
        | atom b =>
          obtain ⟨pb, hpb⟩ := atKey_single b
          simp only [Scc.Lower.termKey, hpa, hpb, List.cons_append, List.nil_append, List.cons.injEq] at ht
          simp only [chainLen, ih _ hb.2 e' ht.2.2]
        | _ => simp [Scc.Lower.termKey] at ht
      | _ => simp [Scc.Lower.termKey] at ht
    | add a b =>
      simp only [Scc.Lower.body0, Bool.and_eq_true] at hb
      obtain ⟨pa, hpa⟩ := atKey_single a
      obtain ⟨pb, hpb⟩ := atKey_single b
      cases t with
      | let_ y op' e' =>
        cases op' with
        | add a' b' =>
          obtain ⟨pa', hpa'⟩ := atKey_single a'
          obtain ⟨pb', hpb'⟩ := atKey_single b'
          simp only [Scc.Lower.termKey, hpa, hpb, hpa', hpb', List.cons_append, List.nil_append,
            List.cons.injEq] at ht
          simp only [chainLen, ih _ hb.2 e' ht.2.2.2]
        | _ => simp [Scc.Lower.termKey] at ht
      | _ => simp [Scc.Lower.termKey] at ht
    | _ => simp [Scc.Lower.body0] at hb
  | ret a =>
    intro _ _ t ht
    cases t with
    | let_ y op' e' => cases op' <;> simp [Scc.Lower.termKey] at ht
    | _ => rfl
  | _ => intro _ hb; simp [Scc.Lower.body0] at hb

/-- The environment's word 0 of `y`, past a binding of another name. -/
theorem immOfEnv_cons_ne {env : Scc.Lower.Env} {x y : String} {t : Ty} {ws : List Scc.IR.Operand}
    (hne : x ≠ y) : immOfEnv ((x, t, ws) :: env) y 0 = immOfEnv env y 0 := by
  have : (x == y) = false := by simp [hne]
  simp [immOfEnv, this]

/-- An atom's literal is word 0 of its words, bound to `x`. -/
theorem atomV_lit {scope : List String} {lits : List (String × Option Nat)} {env : Scc.Lower.Env}
    (hR : LitImm lits env) {a : At} (ha0 : Scc.Lower.atom0 scope a = true) {t : Ty} {ws : List Scc.IR.Operand}
    (ha : atomV env a = some (t, ws)) {n : Nat} (hn : Scc.Lower.litOf lits a = some n) (x : String) :
    immOfEnv ((x, t, ws) :: env) x 0 = some n := by
  cases a with
  | var z =>
    have h := hR z n hn
    simp only [atomV, Option.map_eq_some_iff] at ha
    obtain ⟨b, hb, he⟩ := ha
    cases he
    simpa [immOfEnv, hb] using h
  | lit m =>
    simp only [Scc.Lower.litOf, Option.some.injEq] at hn
    subst hn
    simp only [Scc.Lower.atom0, decide_eq_true_eq] at ha0
    have h64 : ¬ m ≥ 2 ^ 64 := by omega
    simp only [atomV, h64, ite_false, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨-, rfl⟩ := ha
    simp only [immOfEnv, List.find?_cons, beq_self_eq_true, Option.bind_some, Scc.Lower.imm,
      List.getElem?_cons_zero, Option.some.injEq]
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  | unit => simp [Scc.Lower.litOf] at hn

/-- **The two walks agree**: at each point of the source's literal walk of
an `Accepted0` body there is a point of the lowering's walk at the same
term, whose environment has the literal bindings as immediates; a term with
that point's key has its number of leading `let`s. -/
theorem walk_agree : ∀ (e : Expr) (scope : List String) (lits : List (String × Option Nat))
    (env : Scc.Lower.Env) (m : Nat), Scc.Lower.body0 scope e = true → LitImm lits env → ScopeBound scope env →
    ∀ q ∈ Scc.Lower.litWalk lits e, ∃ p ∈ lowerEnvs env m e, p.1 = q.1 ∧ LitImm q.2 p.2.1 ∧
      ∀ t : Expr, Scc.Lower.termKey t = Scc.Lower.termKey q.1 → chainLen t = chainLen q.1 := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope lits env m hb hR hS q hq
    have hkey := chainLen_of_termKey _ scope hb
    cases op with
    | atom a =>
      have hb' := hb
      simp only [Scc.Lower.body0, Bool.and_eq_true] at hb'
      simp only [Scc.Lower.litWalk, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨(_, env, m), by simp [lowerEnvs], rfl, hR, hkey⟩
      · have hv : ∃ v, atomV env a = some v := by
          cases a with
          | var z =>
            simp only [Scc.Lower.atom0, List.contains_iff_mem] at hb'
            obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hS z hb'.1)
            exact ⟨(b.2.1, b.2.2), by simp [atomV, hb]⟩
          | lit n =>
            simp only [Scc.Lower.atom0, decide_eq_true_eq] at hb'
            have h64 : ¬ n ≥ 2 ^ 64 := by omega
            exact ⟨(.intS (.lit n), [Scc.Lower.imm n]), by simp [atomV, h64]⟩
          | unit => simp [Scc.Lower.atom0] at hb'
        obtain ⟨⟨t, ws⟩, ha⟩ := hv
        have hR' : LitImm ((x, Scc.Lower.litOf lits a) :: lits) ((x, t, ws) :: env) := by
          intro y n hy
          by_cases hxy : x = y
          · subst hxy
            simp only [List.lookup_cons, beq_self_eq_true, Option.join_some] at hy
            exact atomV_lit hR hb'.1 ha hy x
          · rw [immOfEnv_cons_ne hxy]
            have : (y == x) = false := by simp [Ne.symm hxy]
            simp only [List.lookup_cons, this] at hy
            exact hR y n hy
        have hS' : ScopeBound (x :: scope) ((x, t, ws) :: env) := by
          intro z hz
          by_cases hxz : x = z
          · subst hxz; simp
          · have : (x == z) = false := by simp [hxz]
            simp only [List.find?_cons, this]
            exact hS z (by simpa [Ne.symm hxz] using hz)
        obtain ⟨p, hp, h1, h2, h3⟩ := ih (x :: scope) _ ((x, t, ws) :: env) m hb'.2 hR' hS' q hq
        exact ⟨p, by simp [lowerEnvs, ha, hp], h1, h2, h3⟩
    | add a b =>
      have hb' := hb
      simp only [Scc.Lower.body0, Bool.and_eq_true] at hb'
      simp only [Scc.Lower.litWalk, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨(_, env, m), by simp [lowerEnvs], rfl, hR, hkey⟩
      · have hR' : LitImm ((x, none) :: lits) ((x, .int, [.reg (Scc.Lower.Inv.regName x m)]) :: env) := by
          intro y n hy
          by_cases hxy : x = y
          · subst hxy; simp at hy
          · rw [immOfEnv_cons_ne hxy]
            have : (y == x) = false := by simp [Ne.symm hxy]
            simp only [List.lookup_cons, this] at hy
            exact hR y n hy
        have hS' : ScopeBound (x :: scope) ((x, .int, [.reg (Scc.Lower.Inv.regName x m)]) :: env) := by
          intro z hz
          by_cases hxz : x = z
          · subst hxz; simp
          · have : (x == z) = false := by simp [hxz]
            simp only [List.find?_cons, this]
            exact hS z (by simpa [Ne.symm hxz] using hz)
        obtain ⟨p, hp, h1, h2, h3⟩ := ih (x :: scope) _ _ (m + 1) hb'.2 hR' hS' q hq
        exact ⟨p, by simp [lowerEnvs, hp], h1, h2, h3⟩
    | _ => simp [Scc.Lower.body0] at hb
  | ret a =>
    intro scope lits env m hb hR _ q hq
    simp only [Scc.Lower.litWalk, List.mem_singleton] at hq
    subst hq
    exact ⟨(_, env, m), by simp [lowerEnvs], rfl, hR, chainLen_of_termKey _ scope hb⟩
  | _ => intro _ _ _ _ hb; simp [Scc.Lower.body0] at hb

/-- **`Accepted1`'s immediate table is inside the lowering's** on an
`Accepted0` program: every entry of `imms1Of [d]` is `immsOf d`'s. -/
theorem imms1Of_sub_immsOf {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {t : Expr} {x : String}
    {k n : Nat} (h : Scc.Lower.imms1Of [d] t x k = some n) : immsOf d t x k = some n := by
  simp only [Scc.Lower.Accepted0, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, ha⟩, -⟩, hb⟩, -⟩ := hd
  have hp : Scc.Lower.params1 d = [] := by simp [Scc.Lower.params1, ha]
  unfold Scc.Lower.imms1Of at h
  split at h
  · rename_i hk
    subst hk
    simp only [Scc.Lower.litWalks, List.flatMap_cons, List.flatMap_nil, List.append_nil, hp,
      List.map_nil] at h
    obtain ⟨q, hq, hf⟩ := List.exists_of_findSome?_eq_some h
    split at hf
    · rename_i hkey
      have hkey' : Scc.Lower.termKey t = Scc.Lower.termKey q.1 := (beq_iff_eq.mp hkey).symm
      have hR0 : LitImm [] [(d.arg, .unit, [])] := by intro y n hy; simp at hy
      have hS0 : ScopeBound [] [(d.arg, .unit, [])] := by intro z hz; simp at hz
      obtain ⟨p, hpm, h1, h2, h3⟩ := walk_agree d.body [] [] _ 0 hb hR0 hS0 q hq
      have hc : chainLen t = chainLen p.1 := by rw [h1]; exact h3 t hkey'
      unfold immsOf
      rw [hc, lowerEnvs_find hpm]
      exact h2 x n hf
    · simp at hf
  · simp at h

/-- The table on a two-literal body: `imms1Of` at the `ret`, `immsOf` there
too (evaluation). -/
private def agreeEx : Decl :=
  { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
    body := .let_ "x" (.atom (.lit 1)) (.let_ "y" (.add (.var "x") (.lit 2)) (.ret (.var "y"))) }

#guard Scc.Lower.Accepted0 [agreeEx]
#guard Scc.Lower.imms1Of [agreeEx] (.let_ "y" (.add (.var "x") (.lit 2)) (.ret (.var "y"))) "x" 0 == some 1
#guard immsOf agreeEx (.let_ "y" (.add (.var "x") (.lit 2)) (.ret (.var "y"))) "x" 0 == some 1
-- Off the walk the tables differ: `immsOf` answers at `ret z` (same `chainLen` as `ret y`).
#guard immsOf agreeEx (.ret (.var "z")) "x" 0 == some 1
#guard Scc.Lower.imms1Of [agreeEx] (.ret (.var "z")) "x" 0 == none

end Spike.Lib.LowerNode
