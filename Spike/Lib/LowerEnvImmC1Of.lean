/-
**The lowering's walk over an `Accepted1` body with calls** (ISA-neutral),
next to `Spike/Lib/LowerEnvImm1.lean`'s `lowerEnvs1` for call-free bodies,
and its immediates (as `Spike/Lib/LowerEnvImm1Of.lean`).

- `lowerEnvsC frames env n e`: the points `lowerC` passes, with their
  environment and counter: a call binds its result to `r%n` and takes one
  name, seven with the depth counter (`frames`, `cntC`); both branches of an
  `if` (the `then` branch from `n + 2`, the `else` branch after it).
- `immIn_headC`, `immIn_tailC_*`: the walk's points after a construct are
  among the walk's points (for an induction along the body).
- `walkC_lits`, `immIn_imms1OfC`: at each point of the walk of an
  `Accepted1` program's code block, the lowering's environment has its
  immediates in `imms1Of`.
-/
import Spike.Lib.LowerEnvImm1Of
import Scc.Lower.InvC1

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (SEnv lookupS WordPl)
open Scc.Lower (litWalk litWalks litOf imms1Of immsCoherent Accepted1)
open Scc.Lower.Inv (atomV env1 cntC regName)

/-- **The lowering's walk with calls** over `e` from `env` and `n`, with
depth limit `frames`: at each point, the term still to lower, the
environment and the counter (as `lowerC`). -/
def lowerEnvsC (frames : Option Nat) (env : Scc.Lower.Env) (n : Nat) : Expr → List (Expr × Scc.Lower.Env × Nat)
  | .let_ x (.atom a) e =>
      (.let_ x (.atom a) e, env, n) ::
        match atomV env a with
        | some (t, ws) => lowerEnvsC frames ((x, t, ws) :: env) n e
        | none => []
  | .let_ x (.add a b) e =>
      (.let_ x (.add a b) e, env, n) :: lowerEnvsC frames ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e
  | .let_ x (.sub a b) e =>
      (.let_ x (.sub a b) e, env, n) :: lowerEnvsC frames ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e
  | .let_ x (.call g is a ts) e =>
      (.let_ x (.call g is a ts) e, env, n) ::
        lowerEnvsC frames ((x, .int, [.reg (regName "r" n)]) :: env) (n + if frames.isSome then 7 else 1) e
  | .ifeq a b yes no =>
      (.ifeq a b yes no, env, n) ::
        (lowerEnvsC frames env (n + 2) yes ++ lowerEnvsC frames env (n + 2 + cntC frames yes) no)
  | e => [(e, env, n)]

/-- The walk starts at its term. -/
theorem immIn_headC {P : Expr × Scc.Lower.Env × Nat → Prop} {frames : Option Nat} {env : Scc.Lower.Env}
    {n : Nat} {e : Expr} (h : ∀ q ∈ lowerEnvsC frames env n e, P q) : P (e, env, n) := by
  apply h
  cases e with
  | let_ x op e => cases op <;> simp [lowerEnvsC]
  | _ => simp [lowerEnvsC]

/-- The walk after `let x = a` is part of the walk at it. -/
theorem immIn_tailC_atom {P : Expr × Scc.Lower.Env × Nat → Prop} {frames : Option Nat} {env : Scc.Lower.Env}
    {n : Nat} {x : String} {a : At} {e : Expr} {t : Ty} {ws : List Scc.IR.Operand} (ha : atomV env a = some (t, ws))
    (h : ∀ q ∈ lowerEnvsC frames env n (.let_ x (.atom a) e), P q) :
    ∀ q ∈ lowerEnvsC frames ((x, t, ws) :: env) n e, P q :=
  fun q hq => h q (by simp [lowerEnvsC, ha, hq])

/-- The walk after `let x = a + b` is part of the walk at it. -/
theorem immIn_tailC_add {P : Expr × Scc.Lower.Env × Nat → Prop} {frames : Option Nat} {env : Scc.Lower.Env}
    {n : Nat} {x : String} {a b : At} {e : Expr} (h : ∀ q ∈ lowerEnvsC frames env n (.let_ x (.add a b) e), P q) :
    ∀ q ∈ lowerEnvsC frames ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e, P q :=
  fun q hq => h q (by simp [lowerEnvsC, hq])

/-- The walk after `let x = a - b` is part of the walk at it. -/
theorem immIn_tailC_sub {P : Expr × Scc.Lower.Env × Nat → Prop} {frames : Option Nat} {env : Scc.Lower.Env}
    {n : Nat} {x : String} {a b : At} {e : Expr} (h : ∀ q ∈ lowerEnvsC frames env n (.let_ x (.sub a b) e), P q) :
    ∀ q ∈ lowerEnvsC frames ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e, P q :=
  fun q hq => h q (by simp [lowerEnvsC, hq])

/-- The walk after `let x = g(a)` is part of the walk at it. -/
theorem immIn_tailC_call {P : Expr × Scc.Lower.Env × Nat → Prop} {frames : Option Nat} {env : Scc.Lower.Env}
    {n : Nat} {x g : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    (h : ∀ q ∈ lowerEnvsC frames env n (.let_ x (.call g is a ts) e), P q) :
    ∀ q ∈ lowerEnvsC frames ((x, .int, [.reg (regName "r" n)]) :: env) (n + if frames.isSome then 7 else 1) e,
      P q :=
  fun q hq => h q (by simp [lowerEnvsC, hq])

/-- The walk of an `if`'s `then` branch is part of the walk at it. -/
theorem immIn_tailC_yes {P : Expr × Scc.Lower.Env × Nat → Prop} {frames : Option Nat} {env : Scc.Lower.Env}
    {n : Nat} {a b : At} {yes no : Expr} (h : ∀ q ∈ lowerEnvsC frames env n (.ifeq a b yes no), P q) :
    ∀ q ∈ lowerEnvsC frames env (n + 2) yes, P q :=
  fun q hq => h q (by simp [lowerEnvsC, hq])

/-- The walk of an `if`'s `else` branch is part of the walk at it. -/
theorem immIn_tailC_no {P : Expr × Scc.Lower.Env × Nat → Prop} {frames : Option Nat} {env : Scc.Lower.Env}
    {n : Nat} {a b : At} {yes no : Expr} (h : ∀ q ∈ lowerEnvsC frames env n (.ifeq a b yes no), P q) :
    ∀ q ∈ lowerEnvsC frames env (n + 2 + cntC frames yes) no, P q :=
  fun q hq => h q (by simp [lowerEnvsC, hq])

/-- **Each point of the lowering's walk with calls is a point of the literal
walk**, with related literal bindings (`LitRel`). -/
theorem walkC_lits (frames : Option Nat) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Option Nat)),
      LitRel env lits → ∀ q ∈ lowerEnvsC frames env n e,
        ∃ lits', (q.1, lits') ∈ litWalk lits e ∧ LitRel q.2.1 lits' := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n lits h q hq
    cases op with
    | atom a =>
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨lits, litWalk_head _ _, h⟩
      · cases ha : atomV env a with
        | none => simp [ha] at hq
        | some v =>
          obtain ⟨t, ws⟩ := v
          simp only [ha] at hq
          obtain ⟨l', hl', hr'⟩ :=
            ih _ n _ (litRel_cons h x t ws (litOf lits a) (atom_lits h ha)) q hq
          exact ⟨l', by simp [litWalk, hl'], hr'⟩
    | add a b | sub a b | call g is a ts =>
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨lits, litWalk_head _ _, h⟩
      · obtain ⟨l', hl', hr'⟩ := ih _ _ _ (litRel_cons h x .int _ none (reg_noImm _ _)) q hq
        exact ⟨l', by simp [litWalk, hl'], hr'⟩
    | _ =>
      simp only [lowerEnvsC, List.mem_singleton] at hq
      subst hq
      exact ⟨lits, litWalk_head _ _, h⟩
  | ifeq a b yes no ihy ihn =>
    intro env n lits h q hq
    simp only [lowerEnvsC, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact ⟨lits, litWalk_head _ _, h⟩
    · obtain ⟨l', hl', hr'⟩ := ihy env _ lits h q hq
      exact ⟨l', by simp [litWalk, hl'], hr'⟩
    · obtain ⟨l', hl', hr'⟩ := ihn env _ lits h q hq
      exact ⟨l', by simp [litWalk, hl'], hr'⟩
  | _ =>
    intro env n lits h q hq
    simp only [lowerEnvsC, List.mem_singleton] at hq
    subst hq
    exact ⟨lits, litWalk_head _ _, h⟩

/-- **A literal binding at a point of an `Accepted1` program's literal walk
is `imms1Of`'s entry** (`immsCoherent`). -/
theorem imms1Of_of_lits {p : CoreTerm.Prog} (hp : Accepted1 p = true) {d : Decl} (hd : d ∈ p) {t : Expr}
    {lits : List (String × Option Nat)} (hl : (t, lits) ∈ litWalk ((Scc.Lower.params1 d).map (·, none)) d.body)
    {x : String} {v : Nat} (hn : (lits.lookup x).join = some v) : imms1Of p t x 0 = some v := by
  have hc : immsCoherent p = true := by
    simp only [Accepted1, Bool.and_eq_true] at hp
    exact hp.2
  have hw : (t, lits) ∈ litWalks p := by
    simp only [litWalks, List.mem_flatMap]
    exact ⟨d, hd, hl⟩
  have hq' := List.all_eq_true.mp (List.all_eq_true.mp hc _ hw)
  have ho : lits.lookup x = some (some v) := by
    cases hlk : lits.lookup x with
    | none => simp [hlk] at hn
    | some o => simp only [hlk, Option.join_some] at hn; rw [hn]
  obtain ⟨b, hb, rfl⟩ := lookup_mem ho
  have := hq' b hb
  simp only [hn] at this
  simpa using this

/-- An environment's immediate placement (`ofEnv`) is an immediate word. -/
theorem imm_of_ofEnv {env : Scc.Lower.Env} {x : String} {k : Nat} {v : UInt64}
    (h : (lookupS (ofEnv env) x).bind (·.2[k]?) = some (.one (.imm v))) :
    (env.find? (·.1 == x)).bind (·.2.2[k]?) = some (.imm v) := by
  rw [lookupS_ofEnv] at h
  cases hf : env.find? (·.1 == x) with
  | none => simp [hf] at h
  | some b =>
    simp only [hf, Option.map_some, Option.bind_some, List.getElem?_map] at h ⊢
    cases hk : b.2.2[k]? with
    | none => simp [hk] at h
    | some o => simp only [hk, Option.map_some, Option.some.injEq, WordPl.one.injEq] at h; rw [h]

/-- **At each point of the walk with calls of an `Accepted1` program's code
block, the lowering's environment has its immediates in `imms1Of`** (any
depth limit). -/
theorem immIn_imms1OfC {p : CoreTerm.Prog} (hp : Accepted1 p = true) {d : Decl} (hd : d ∈ p)
    (frames : Option Nat) :
    ∀ q ∈ lowerEnvsC frames (env1 d) 0 d.body, ImmIn (imms1Of p) (ofEnv q.2.1) q.1 := by
  intro q hq x k v h
  obtain ⟨lits, hl, hr⟩ := walkC_lits frames d.body (env1 d) 0 _ (litRel_env1 d _) q hq
  obtain ⟨rfl, hn⟩ := hr x k v (imm_of_ofEnv h)
  exact imms1Of_of_lits hp hd hl hn

end Spike.Lib.LowerNode
