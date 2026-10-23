/-
**The lowering's immediates** (ISA-neutral): which words of a lowered
`Accepted0` body's environment are immediates, as a table keyed by the
remaining source term (`Layout.imms`'s shape).

- `lowerEnvs env n e`: the lowering's walk (`lower0`) over `e` from the
  environment `env` and counter `n`, as the list of its points: the term
  still to lower, the environment and the counter there. A `let x = a` binds
  `x` to `a`'s words, a `let x = a + b` binds `x` to a fresh register.
- `immsOf d`: the immediate table of `d`'s body. At a remaining term `t`
  (found among the walk's points by its number of leading `let`s,
  `chainLen`, which strictly decreases along the walk), word `k` of `x` is
  the immediate the lowering's environment binds there, else nothing. An
  immediate comes from a literal `let` or a copy of one (`let y = x`).
- `ImmIn i s t`: every immediate placement of the symbolic environment `s`
  is the table `i`'s entry at `t`.
- `immIn_immsOf`: at each point of `d`'s body's walk, the lowering's
  environment (`ofEnv`) has its immediates in `immsOf d`.
- `immIn_tail_atom`, `immIn_tail_add`: the walk's points after a `let`
  are among the walk's points (for an induction along the body).
- `InWalk d t`, `walk_immsOf`: `t` is a point of `d`'s body's walk;
  `insts_ne_of_add_suffix`: a checked `+` in the walk makes `main`'s
  lowered instructions non-empty.
- `NJ.add_ovf_term`: `NJ.add_ovf` with the source's term at the `+` (the
  key `ImmIn` is stated at).
-/
import Spike.Lib.LowerNode
import Scc.Lower.InvBody

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (SEnv lookupS WordPl)
open Scc.Lower.Inv (lower0 atomV)

/-- The number of leading `let`s of a term. -/
def chainLen : Expr → Nat
  | .let_ _ _ e => chainLen e + 1
  | _ => 0

/-- **The lowering's walk** over `e` from `env` and `n`: at each point, the
term still to lower, the environment and the counter (as `lower0`). -/
def lowerEnvs (env : Scc.Lower.Env) (n : Nat) : Expr → List (Expr × Scc.Lower.Env × Nat)
  | .let_ x (.atom a) e =>
      (.let_ x (.atom a) e, env, n) ::
        match atomV env a with
        | some (t, ws) => lowerEnvs ((x, t, ws) :: env) n e
        | none => []
  | .let_ x (.add a b) e =>
      (.let_ x (.add a b) e, env, n) :: lowerEnvs ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e
  | e => [(e, env, n)]

/-- **Every immediate placement of `s` is `i`'s entry at `t`.** -/
def ImmIn (i : Expr → String → Nat → Option Nat) (s : SEnv) (t : Expr) : Prop :=
  ∀ x k v, (lookupS s x).bind (·.2[k]?) = some (.one (.imm v)) → i t x k = some v.toNat

/-- An environment's word as an immediate's value. -/
def immOfEnv (env : Scc.Lower.Env) (x : String) (k : Nat) : Option Nat :=
  match (env.find? (·.1 == x)).bind (·.2.2[k]?) with
  | some (.imm v) => some v.toNat
  | _ => none

/-- **The immediate table of `d`'s body**: at a remaining term `t`, the
lowering's environment at the walk's point with `t`'s number of leading
`let`s, its immediates. -/
def immsOf (d : Decl) (t : Expr) (x : String) (k : Nat) : Option Nat :=
  match (lowerEnvs [(d.arg, .unit, [])] 0 d.body).find? (fun q => chainLen q.1 == chainLen t) with
  | some (_, env, _) => immOfEnv env x k
  | none => none

/-! ## The walk -/

/-- The walk starts at its term. -/
theorem lowerEnvs_head (env : Scc.Lower.Env) (n : Nat) (e : Expr) :
    ∃ rest, lowerEnvs env n e = (e, env, n) :: rest := by
  cases e with
  | let_ x op e => cases op <;> simp [lowerEnvs]
  | _ => simp [lowerEnvs]

/-- Past its head, the walk's points have fewer leading `let`s. -/
theorem lowerEnvs_lt : ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (rest : List (Expr × Scc.Lower.Env × Nat)),
    lowerEnvs env n e = (e, env, n) :: rest → ∀ q ∈ rest, chainLen q.1 < chainLen e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n rest h q hq
    cases op with
    | atom a =>
      simp only [lowerEnvs, List.cons.injEq, true_and] at h
      subst h
      cases ha : atomV env a with
      | none => simp [ha] at hq
      | some v =>
        obtain ⟨t, ws⟩ := v
        simp only [ha] at hq
        obtain ⟨rest', hr'⟩ := lowerEnvs_head ((x, t, ws) :: env) n e
        rw [hr'] at hq
        simp only [chainLen]
        rcases List.mem_cons.mp hq with rfl | hq
        · simp
        · have := ih _ _ _ hr' q hq; omega
    | add a b =>
      simp only [lowerEnvs, List.cons.injEq, true_and] at h
      subst h
      obtain ⟨rest', hr'⟩ := lowerEnvs_head ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e
      rw [hr'] at hq
      simp only [chainLen]
      rcases List.mem_cons.mp hq with rfl | hq
      · simp
      · have := ih _ _ _ hr' q hq; omega
    | _ => simp [lowerEnvs] at h; subst h; simp at hq
  | _ => intro env n rest h q hq; simp [lowerEnvs] at h; subst h; simp at hq

/-- **A point of the walk is the first with its number of leading `let`s.** -/
theorem lowerEnvs_find {env0 : Scc.Lower.Env} {n0 : Nat} {e0 : Expr} {q : Expr × Scc.Lower.Env × Nat}
    (hq : q ∈ lowerEnvs env0 n0 e0) :
    (lowerEnvs env0 n0 e0).find? (fun q' => chainLen q'.1 == chainLen q.1) = some q := by
  induction e0 generalizing env0 n0 with
  | let_ x op e ih =>
    cases op with
    | atom a =>
      simp only [lowerEnvs] at hq ⊢
      rcases List.mem_cons.mp hq with rfl | hq
      · simp
      · have hne : chainLen q.1 ≠ chainLen (.let_ x (.atom a) e) := by
          obtain ⟨rest, hr⟩ := lowerEnvs_head env0 n0 (.let_ x (.atom a) e)
          have := lowerEnvs_lt _ _ _ rest hr q
          simp only [lowerEnvs, List.cons.injEq, true_and] at hr
          rw [← hr] at this
          have := this hq; omega
        rw [List.find?_cons_of_neg (by simp only [beq_iff_eq]; exact fun h => hne h.symm)]
        cases ha : atomV env0 a with
        | none => simp [ha] at hq
        | some v =>
          obtain ⟨t, ws⟩ := v
          simp only [ha] at hq ⊢
          exact ih hq
    | add a b =>
      simp only [lowerEnvs] at hq ⊢
      rcases List.mem_cons.mp hq with rfl | hq
      · simp
      · have hne : chainLen q.1 ≠ chainLen (.let_ x (.add a b) e) := by
          obtain ⟨rest, hr⟩ := lowerEnvs_head env0 n0 (.let_ x (.add a b) e)
          have := lowerEnvs_lt _ _ _ rest hr q
          simp only [lowerEnvs, List.cons.injEq, true_and] at hr
          rw [← hr] at this
          have := this hq; omega
        rw [List.find?_cons_of_neg (by simp only [beq_iff_eq]; exact fun h => hne h.symm)]
        exact ih hq
    | _ => simp only [lowerEnvs, List.mem_singleton] at hq; subst hq; simp [lowerEnvs]
  | _ => simp only [lowerEnvs, List.mem_singleton] at hq; subst hq; simp [lowerEnvs]

/-! ## The table -/

/-- **The lowering's environment has its immediates in `immOfEnv`.** -/
theorem immIn_immOfEnv {env : Scc.Lower.Env} {x : String} {k : Nat} {v : UInt64}
    (h : (lookupS (ofEnv env) x).bind (·.2[k]?) = some (.one (.imm v))) : immOfEnv env x k = some v.toNat := by
  rw [lookupS_ofEnv] at h
  unfold immOfEnv
  cases hf : env.find? (·.1 == x) with
  | none => simp [hf] at h
  | some b =>
    simp only [hf, Option.map_some, Option.bind_some, List.getElem?_map] at h
    cases hk : b.2.2[k]? with
    | none => simp [hk] at h
    | some o =>
      simp only [hk, Option.map_some, Option.some.injEq, WordPl.one.injEq] at h
      subst h
      simp [hk]

/-- **At each point of `d`'s body's walk, the lowering's environment has
its immediates in `immsOf d`.** -/
theorem immIn_immsOf (d : Decl) :
    ∀ q ∈ lowerEnvs [(d.arg, .unit, [])] 0 d.body, ImmIn (immsOf d) (ofEnv q.2.1) q.1 := by
  intro q hq x k v h
  unfold immsOf
  rw [lowerEnvs_find hq]
  exact immIn_immOfEnv h

/-- The walk after `let x = a` is part of the walk at it. -/
theorem immIn_tail_atom {P : Expr × Scc.Lower.Env × Nat → Prop} {env : Scc.Lower.Env} {n : Nat} {x : String}
    {a : At} {e : Expr} {t : Ty} {ws : List Scc.IR.Operand} (ha : atomV env a = some (t, ws))
    (h : ∀ q ∈ lowerEnvs env n (.let_ x (.atom a) e), P q) : ∀ q ∈ lowerEnvs ((x, t, ws) :: env) n e, P q :=
  fun q hq => h q (by simp [lowerEnvs, ha, hq])

/-- The walk after `let x = a + b` is part of the walk at it. -/
theorem immIn_tail_add {P : Expr × Scc.Lower.Env × Nat → Prop} {env : Scc.Lower.Env} {n : Nat} {x : String}
    {a b : At} {e : Expr}
    (h : ∀ q ∈ lowerEnvs env n (.let_ x (.add a b) e), P q) :
    ∀ q ∈ lowerEnvs ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) e, P q :=
  fun q hq => h q (by simp [lowerEnvs, hq])

/-- The walk's head is its term at its environment. -/
theorem immIn_head {P : Expr × Scc.Lower.Env × Nat → Prop} {env : Scc.Lower.Env} {n : Nat} {e : Expr}
    (h : ∀ q ∈ lowerEnvs env n e, P q) : P (e, env, n) := by
  obtain ⟨rest, hr⟩ := lowerEnvs_head env n e
  exact h _ (by rw [hr]; simp)

/-! ## The walk's terms -/

/-- **`t` is a point of `d`'s body's walk** (a remaining term the lowering
reaches). -/
def InWalk (d : Decl) (t : Expr) : Prop :=
  ∃ q ∈ lowerEnvs [(d.arg, .unit, [])] 0 d.body, q.1 = t

/-- **At each point of `d`'s body's walk**, the lowering's environment has
its immediates in `immsOf d`, and the point is in the walk. -/
theorem walk_immsOf (d : Decl) :
    ∀ q ∈ lowerEnvs [(d.arg, .unit, [])] 0 d.body, ImmIn (immsOf d) (ofEnv q.2.1) q.1 ∧ InWalk d q.1 :=
  fun q hq => ⟨immIn_immsOf d q hq, q, hq, rfl⟩

/-- **A checked `+` in the walk is an instruction**: if lowering `e` from
`env`, `n` succeeds and its walk reaches a `let x = a + b`, the lowered
instructions are not empty. -/
theorem lower0_insts_ne_of_mem :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Scc.Lower.Inv.Res), lower0 env n e = some r →
      ∀ (x : String) (a b : At) (e' : Expr), (∃ q ∈ lowerEnvs env n e, q.1 = .let_ x (.add a b) e') →
        r.insts ≠ [] := by
  intro e
  induction e with
  | let_ y op e ih =>
    intro env n r hr x a b e' ⟨q, hq, hqt⟩
    cases op with
    | atom c =>
      obtain ⟨t, w, r', ha, -, hr', rfl⟩ := Scc.Lower.Inv.lower0_atom_inv hr
      simp only [lowerEnvs, ha, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqt
      · exact ih _ n r' hr' x a b e' ⟨q, hq, hqt⟩
    | add c c' =>
      obtain ⟨-, -, -, -, r', -, -, -, rfl⟩ := Scc.Lower.Inv.lower0_add_inv hr
      simp
    | _ => simp [lower0] at hr
  | _ =>
    intro env n r hr x a b e' ⟨q, hq, hqt⟩
    simp only [lowerEnvs, List.mem_singleton] at hq
    subst hq
    cases hqt

/-- **A checked `+` in `d`'s body's walk is an instruction of `main`'s
lowered body.** -/
theorem insts_ne_of_add_suffix {d : Decl} {r : Scc.Lower.Inv.Res} {x : String} {a b : At} {e : Expr}
    (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r) (h : InWalk d (.let_ x (.add a b) e)) :
    r.insts ≠ [] :=
  lower0_insts_ne_of_mem _ _ _ _ hr x a b e h

/-! ## The overflow abort's source term -/

/-- `NJ.add_ovf`, with the source's term at the `+`. -/
theorem NJ.add_ovf_term {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}
    {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ p lbl rs (.let_ x (.add a b) e) s sl c)
    (ha : Spike.Lib.Form.sevalAt s a = some (ta, [.one pa])) (hb : Spike.Lib.Form.sevalAt s b = some (tb, [.one pb]))
    (hva : Spike.Lib.Form.opdVal rs sl pa = some va) (hvb : Spike.Lib.Form.opdVal rs sl pb = some vb)
    (hge : 2 ^ 64 ≤ va + vb)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome) :
    ∃ c1, LocalRun p c c1 ∧ AbSrc lbl rs s sl c1 ∧ c1.term = .let_ x (.add a b) e := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, -, -, hna, hnb⟩ := h.add ha hb hva hvb
  refine ⟨c1, hr, ⟨⟨x, a, b, e, ta, tb, wa, wb, va, vb, hj.1, hea, heb, hna, hnb, hge⟩, hn, hj.2.2, ?_⟩, hj.1⟩
  rw [hj.1]; exact htot

/-! ## Example -/

/-- `let a = 5; let b = a; let c = b + a; ret c`. -/
private def immEx : Decl :=
  { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int,
    body := .let_ "a" (.atom (.lit 5)) (.let_ "b" (.atom (.var "a"))
      (.let_ "c" (.add (.var "b") (.var "a")) (.ret (.var "c")))) }

-- At the `+`, `a` and its copy `b` are the immediate 5; `c` is a register, so nothing at the `ret`.
#guard immsOf immEx (.let_ "c" (.add (.var "b") (.var "a")) (.ret (.var "c"))) "b" 0 == some 5
#guard immsOf immEx (.let_ "c" (.add (.var "b") (.var "a")) (.ret (.var "c"))) "a" 0 == some 5
#guard immsOf immEx (.let_ "c" (.add (.var "b") (.var "a")) (.ret (.var "c"))) "c" 0 == none
#guard immsOf immEx (.ret (.var "c")) "c" 0 == none
#guard immsOf immEx (.ret (.var "c")) "a" 1 == none

end Spike.Lib.LowerNode
