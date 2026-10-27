/-
**The lowering's environment** (ISA-neutral): facts about
`Scc.Lower.Inv.lower0` that both ISAs' body segments use.

- `lower0_fv`: every free variable of a lowered body is bound in the
  lowering's environment;
- `Fresh`: the environment's registers are none of the rest of the
  lowering's destinations (`Fresh.atom`, `Fresh.add`, `Fresh.ofEnv`,
  `Fresh.mono`);
- `ofEnv_cons`, `isSome_lookupS_ofEnv`: `ofEnv` on a cons and on a bound
  name.

Shared by `Spike/Lib/LowerA64/Body.lean` (and `Body1.lean`) and
`Spike/Lib/LowerX64/Body.lean`: kept free of either ISA's syntax modules,
which do not load together.
-/
import Spike.Lib.LowerNode

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl)
open Scc.Lower.Inv (lower0 atomV Res scalar1)

set_option linter.unusedSimpArgs false

/-! ## The lowering's environment -/

/-- **Every free variable of a lowered body is bound** in the lowering's
environment. -/
theorem lower0_fv :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Res), lower0 env n e = some r →
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
      simp only [lower0] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [w], hr =>
        cases hr' : lower0 ((x, t, [w]) :: env) n e with
        | none => simp [hr'] at hr
        | some r' =>
          simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
          rcases hy with hy | ⟨hy, hne⟩
          · exact hat env a _ ha y hy
          · exact hcons env (x, t, [w]) y (fun e => hne e.symm) (ih _ n r' hr' y hy)
    | add a b =>
      simp only [lower0] at hr
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
          cases hr' : lower0 ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
            rcases hy with (hy | hy) | ⟨hy, hne⟩
            · exact hat env a _ ha y hy
            · exact hat env b _ hb y hy
            · exact hcons env _ y (fun e => hne e.symm) (ih _ (n + 1) r' hr' y hy)
    | _ => simp [lower0] at hr
  | ret a =>
    intro env n r hr y hy
    simp only [lower0] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v => exact hat env a v ha y hy
  | _ => intro env n r hr; simp [lower0] at hr

/-- **The environment's registers are fresh from counter `n` on**: none is
a destination `regName y k`, `k ≥ n`, of the rest of the lowering. -/
def Fresh (env : Scc.Lower.Env) (n : Nat) : Prop :=
  ∀ v ∈ env, ∀ o ∈ v.2.2, ∀ r, o = .reg r → ∀ y k, n ≤ k → r ≠ Scc.Lower.Inv.regName y k

/-- Freshness from a counter holds from any later one. -/
theorem Fresh.mono {env : Scc.Lower.Env} {n m : Nat} (h : Fresh env n) (hm : n ≤ m) : Fresh env m :=
  fun v hv o ho r hr y k hk => h v hv o ho r hr y k (by omega)

theorem Fresh.atom {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) {a : At} {t : Ty} {ws : List Scc.IR.Operand}
    (ha : atomV env a = some (t, ws)) (x : String) : Fresh ((x, t, ws) :: env) n := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · cases a with
    | var z =>
      simp only [atomV, Option.map_eq_some_iff] at ha
      obtain ⟨⟨z', u, vs⟩, hb, he⟩ := ha
      cases he
      exact h (z', u, vs) (List.mem_of_find?_eq_some hb)
    | lit m =>
      simp only [atomV] at ha
      split at ha
      · cases ha
      · cases ha
        intro o ho r hr
        simp only [List.mem_singleton] at ho
        subst ho; cases hr
    | unit =>
      simp only [atomV, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨-, rfl⟩ := ha
      intro o ho; cases ho
  · exact h v hv

theorem Fresh.add {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) (x : String) :
    Fresh ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · intro o ho r hr y k hk
    simp only [List.mem_singleton] at ho
    subst ho; cases hr
    exact Scc.Lower.Inv.regName_ne (by omega)
  · intro o ho r hr y k hk
    exact h v hv o ho r hr y k (by omega)

/-- **The symbolic environment's placed registers are off `regName x n`.** -/
theorem Fresh.ofEnv {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) (x : String) :
    ∀ q ∈ ofEnv env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ Scc.Lower.Inv.regName x n := by
  intro q hq pl hpl o ho r hr
  simp only [Spike.Lib.LowerNode.ofEnv, List.mem_map] at hq
  obtain ⟨b, hb, rfl⟩ := hq
  simp only [List.mem_map] at hpl
  obtain ⟨o', ho', rfl⟩ := hpl
  simp only [WordPl.opds, List.mem_singleton] at ho
  subst ho
  exact h b hb _ ho' r hr x n (Nat.le_refl n)

theorem ofEnv_cons (env : Scc.Lower.Env) (x : String) (t : Ty) (ws : List Scc.IR.Operand) :
    ofEnv ((x, t, ws) :: env) = (x, t, ws.map .one) :: ofEnv env := rfl

theorem isSome_lookupS_ofEnv {env : Scc.Lower.Env} {y : String} (h : (env.find? (·.1 == y)).isSome) :
    (lookupS (ofEnv env) y).isSome := by
  rw [lookupS_ofEnv]; simpa using h

end Spike.Lib.LowerNode
