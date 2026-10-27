/-
**The lowering's walk over a call-free `Accepted1` body** (ISA-neutral),
next to `Spike/Lib/LowerEnvImm.lean`'s walk over `Accepted0` bodies.

- `cnt1 e`: the fresh names lowering `e` consumes (`let` of `+`/`-`: one;
  `if`: its two labels and its branches'); `lower1_next`: the closed form's
  final counter is `n + cnt1 e`.
- `lowerEnvs1 env n e`: the points the lowering passes, with their
  environment and counter, both branches of an `if` (the `then` branch from
  `n + 2`, the `else` branch after it).
- `immIn_tail1_*`, `immIn_head1`: the walk's points after a construct are
  among the walk's points (for an induction along the body).
- `lower1_fv`: every free variable of a lowered body is bound in the
  lowering's environment.
-/
import Spike.Lib.LowerEnvImm
import Scc.Lower.Inv1

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Scc.Lower.Inv (lower1 atomV Res1)

/-- **The fresh names lowering `e` consumes** (`lower1`'s counter). -/
def cnt1 : Expr → Nat
  | .let_ _ (.add _ _) e => cnt1 e + 1
  | .let_ _ (.sub _ _) e => cnt1 e + 1
  | .let_ _ _ e => cnt1 e
  | .ifeq _ _ yes no => cnt1 yes + cnt1 no + 2
  | _ => 0

/-- **The closed form's final counter** is the start plus `cnt1`. -/
theorem lower1_next : ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Res1), lower1 env n e = some r →
    r.next = n + cnt1 e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r hr
    cases op with
    | atom a =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [w], hr =>
        cases hr' : lower1 ((x, t, [w]) :: env) n e with
        | none => cases ht : Scc.Lower.Inv.scalar1 t <;> simp [ht, hr'] at hr
        | some r' =>
          cases ht : Scc.Lower.Inv.scalar1 t <;> simp [ht, hr'] at hr
          subst hr
          simp [ih _ _ _ hr', cnt1]
    | add a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [p], hr =>
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          match us, hr with
          | [q], hr =>
          cases hr' : lower1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            simp [ih _ _ _ hr', cnt1]; omega
    | sub a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [p], hr =>
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          match us, hr with
          | [q], hr =>
          cases hr' : lower1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            simp [ih _ _ _ hr', cnt1]; omega
    | _ => simp [lower1] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n r hr
    simp only [lower1] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      rw [ha] at hr
      match ws, hr with
      | [p], hr =>
      cases hb : atomV env b with
      | none => simp [hb] at hr
      | some u =>
        obtain ⟨t', us⟩ := u
        rw [hb] at hr
        match us, hr with
        | [q], hr =>
        cases hy : lower1 env (n + 2) yes with
        | none => simp [hy] at hr
        | some ry =>
          cases hn : lower1 env ry.next no with
          | none => simp [hy, hn] at hr
          | some rn =>
            simp [hy, hn] at hr
            subst hr
            simp only [ihn _ _ _ hn, ihy _ _ _ hy, cnt1]; omega
  | ret a =>
    intro env n r hr
    simp only [lower1] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v => simp [ha] at hr; subst hr; simp [cnt1]
  | _ => intro env n r hr; simp [lower1] at hr

/-- **The lowering's walk** over a call-free `Accepted1` body `e` from `env`
and `n`: at each point, the term still to lower, the environment and the
counter (as `lower1`); an `if`'s `then` branch from `n + 2`, its `else`
branch after it. -/
def lowerEnvs1 (env : Scc.Lower.Env) (n : Nat) : Expr → List (Expr × Scc.Lower.Env × Nat)
  | .let_ x (.atom a) e =>
      (.let_ x (.atom a) e, env, n) ::
        match atomV env a with
        | some (t, ws) => lowerEnvs1 ((x, t, ws) :: env) n e
        | none => []
  | .let_ x (.add a b) e =>
      (.let_ x (.add a b) e, env, n) ::
        lowerEnvs1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e
  | .let_ x (.sub a b) e =>
      (.let_ x (.sub a b) e, env, n) ::
        lowerEnvs1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e
  | .ifeq a b yes no =>
      (.ifeq a b yes no, env, n) :: (lowerEnvs1 env (n + 2) yes ++ lowerEnvs1 env (n + 2 + cnt1 yes) no)
  | e => [(e, env, n)]

/-- The walk starts at its term. -/
theorem immIn_head1 {P : Expr × Scc.Lower.Env × Nat → Prop} {env : Scc.Lower.Env} {n : Nat} {e : Expr}
    (h : ∀ q ∈ lowerEnvs1 env n e, P q) : P (e, env, n) := by
  apply h
  cases e with
  | let_ x op e => cases op <;> simp [lowerEnvs1]
  | _ => simp [lowerEnvs1]

/-- The walk after `let x = a` is part of the walk at it. -/
theorem immIn_tail1_atom {P : Expr × Scc.Lower.Env × Nat → Prop} {env : Scc.Lower.Env} {n : Nat} {x : String}
    {a : At} {e : Expr} {t : Ty} {ws : List Scc.IR.Operand} (ha : atomV env a = some (t, ws))
    (h : ∀ q ∈ lowerEnvs1 env n (.let_ x (.atom a) e), P q) : ∀ q ∈ lowerEnvs1 ((x, t, ws) :: env) n e, P q :=
  fun q hq => h q (by simp [lowerEnvs1, ha, hq])

/-- The walk after `let x = a + b` is part of the walk at it. -/
theorem immIn_tail1_add {P : Expr × Scc.Lower.Env × Nat → Prop} {env : Scc.Lower.Env} {n : Nat} {x : String}
    {a b : At} {e : Expr} (h : ∀ q ∈ lowerEnvs1 env n (.let_ x (.add a b) e), P q) :
    ∀ q ∈ lowerEnvs1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e, P q :=
  fun q hq => h q (by simp [lowerEnvs1, hq])

/-- The walk after `let x = a - b` is part of the walk at it. -/
theorem immIn_tail1_sub {P : Expr × Scc.Lower.Env × Nat → Prop} {env : Scc.Lower.Env} {n : Nat} {x : String}
    {a b : At} {e : Expr} (h : ∀ q ∈ lowerEnvs1 env n (.let_ x (.sub a b) e), P q) :
    ∀ q ∈ lowerEnvs1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e, P q :=
  fun q hq => h q (by simp [lowerEnvs1, hq])

/-- The walk of an `if`'s `then` branch is part of the walk at it. -/
theorem immIn_tail1_yes {P : Expr × Scc.Lower.Env × Nat → Prop} {env : Scc.Lower.Env} {n : Nat}
    {a b : At} {yes no : Expr} (h : ∀ q ∈ lowerEnvs1 env n (.ifeq a b yes no), P q) :
    ∀ q ∈ lowerEnvs1 env (n + 2) yes, P q :=
  fun q hq => h q (by simp [lowerEnvs1, hq])

/-- The walk of an `if`'s `else` branch is part of the walk at it. -/
theorem immIn_tail1_no {P : Expr × Scc.Lower.Env × Nat → Prop} {env : Scc.Lower.Env} {n : Nat}
    {a b : At} {yes no : Expr} (h : ∀ q ∈ lowerEnvs1 env n (.ifeq a b yes no), P q) :
    ∀ q ∈ lowerEnvs1 env (n + 2 + cnt1 yes) no, P q :=
  fun q hq => h q (by simp [lowerEnvs1, hq])

/-- **Every free variable of a lowered body is bound** in the lowering's
environment. -/
theorem lower1_fv :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Res1), lower1 env n e = some r →
      ∀ y ∈ Scc.Sem.exprFv e, (env.find? (·.1 == y)).isSome := by
  have hat : ∀ (env : Scc.Lower.Env) (a : At) v, atomV env a = some v →
      ∀ y ∈ Scc.Sem.atVars a, (env.find? (·.1 == y)).isSome := by
    intro env a v ha y hy
    cases a with
    | var x =>
      simp only [Scc.Sem.atVars, List.mem_singleton] at hy
      subst hy
      simp only [atomV, Option.map_eq_some_iff] at ha
      obtain ⟨b, hb, -⟩ := ha
      simp [hb]
    | _ => simp [Scc.Sem.atVars] at hy
  have hcons : ∀ (env : Scc.Lower.Env) (b : String × Ty × List Scc.IR.Operand) (y : String), b.1 ≠ y →
      ((b :: env).find? (·.1 == y)).isSome → (env.find? (·.1 == y)).isSome := by
    intro env b y hne h
    have : (b.1 == y) = false := by simp [hne]
    simpa [List.find?_cons, this] using h
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r hr y hy
    cases op with
    | atom a =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [w], hr =>
        cases hr' : lower1 ((x, t, [w]) :: env) n e with
        | none => cases ht : Scc.Lower.Inv.scalar1 t <;> simp [ht, hr'] at hr
        | some r' =>
          simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
          rcases hy with hy | ⟨hy, hne⟩
          · exact hat env a _ ha y hy
          · exact hcons env (x, t, [w]) y (fun e => hne e.symm) (ih _ n r' hr' y hy)
    | add a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [p], hr =>
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          match us, hr with
          | [q], hr =>
          cases hr' : lower1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
            rcases hy with (hy | hy) | ⟨hy, hne⟩
            · exact hat env a _ ha y hy
            · exact hat env b _ hb y hy
            · exact hcons env _ y (fun e => hne e.symm) (ih _ (n + 1) r' hr' y hy)
    | sub a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [p], hr =>
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          match us, hr with
          | [q], hr =>
          cases hr' : lower1 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
            rcases hy with (hy | hy) | ⟨hy, hne⟩
            · exact hat env a _ ha y hy
            · exact hat env b _ hb y hy
            · exact hcons env _ y (fun e => hne e.symm) (ih _ (n + 1) r' hr' y hy)
    | _ => simp [lower1] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n r hr y hy
    simp only [lower1] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      rw [ha] at hr
      match ws, hr with
      | [p], hr =>
      cases hb : atomV env b with
      | none => simp [hb] at hr
      | some u =>
        obtain ⟨t', us⟩ := u
        rw [hb] at hr
        match us, hr with
        | [q], hr =>
        cases hy' : lower1 env (n + 2) yes with
        | none => simp [hy'] at hr
        | some ry =>
          cases hn : lower1 env ry.next no with
          | none => simp [hy', hn] at hr
          | some rn =>
            simp only [Scc.Sem.exprFv, List.mem_append] at hy
            rcases hy with ((hy | hy) | hy) | hy
            · exact hat env a _ ha y hy
            · exact hat env b _ hb y hy
            · exact ihy env _ ry hy' y hy
            · exact ihn env _ rn hn y hy
  | ret a =>
    intro env n r hr y hy
    simp only [lower1] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v => exact hat env a v ha y hy
  | _ => intro env n r hr; simp [lower1] at hr

end Spike.Lib.LowerNode
