import Spike.Lib.Src.ExternUnit

/-!
# The overflow abort label's immediates past `Accepted1`

The abort label's invariant (`abortN i T`, A64 and X64) is generic in the
immediates' table `i` and the term predicate `T`; it states the table at a
symbolic environment (`ImmIn`, `SEnv` form). Past `Accepted1` a variable's
runtime words are regrouped per source word (`Form.group`: a locative's two
words are one placement), so the symbolic environment of a lowering
environment is `ofEnv2` (not `ofEnv`, one placement per runtime word).

- `ofEnv2 env`: each binding's words grouped by `Form.group` (`[]` off the
  layout fragment).
- `immIn_ofEnv2`: `ImmIn2 i env t → ImmIn i (ofEnv2 env) t`, unconditionally.
- `ofEnv2_eq_ofEnv`: on one-word bindings `ofEnv2` is `ofEnv`.
- `InWalk2 cx env0 n body t`: `t` is a point of the lowering's walk
  (`lowerEnvs2`); the overflow abort's term (a `let x = a + b`) is a walk
  point but not a trace mark (an `addChk` is no call and opens no block).
- `walk_imms2Of`: every walk point of a compiled block of an `Accepted2`
  program has its immediates in `imms2Of p` (at `ofEnv2`) and is in the walk:
  the `hImm` premise of the body's segment at `abortN (imms2Of p) (InWalk2 ..)`.
- `walk2_head`, `walk2_let`, `walk2_split`, `walk2_unpack`, `walk2_unpackT`,
  `walk2_yes`, `walk2_no`: a walk property passes from a term to the walk
  after its prefix (the per-construct steps of the body's induction).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (Env)
open Spike.Lib.Form (SEnv lookupS WordPl)

/-! ## The symbolic environment, words grouped -/

/-- **The lowering's environment as a symbolic environment, words grouped
per source word** (`Form.group`; `[]` off the layout fragment). -/
def ofEnv2 (env : Env) : SEnv := env.map fun b => (b.1, b.2.1, (Spike.Lib.Form.group b.2.1 b.2.2).getD [])

theorem lookupS_ofEnv2 (env : Env) (x : String) :
    lookupS (ofEnv2 env) x =
      (env.find? (·.1 == x)).map fun b => (b.2.1, (Spike.Lib.Form.group b.2.1 b.2.2).getD []) := by
  induction env with
  | nil => rfl
  | cons b env ih =>
    by_cases h : b.1 = x
    · simp [lookupS, ofEnv2, h]
    · have hb : (b.1 == x) = false := by simp [h]
      simp only [lookupS, ofEnv2, List.map_cons, List.find?_cons, hb] at ih ⊢
      exact ih

/-- **`ImmIn2` is `ImmIn` at `ofEnv2`.** -/
theorem immIn_ofEnv2 {i : Expr → String → Nat → Option Nat} {env : Env} {t : Expr} (h : ImmIn2 i env t) :
    ImmIn i (ofEnv2 env) t := by
  intro x k v hx
  rw [lookupS_ofEnv2] at hx
  rcases hb : env.find? (·.1 == x) with _ | b
  · rw [hb] at hx; cases hx
  rw [hb] at hx
  simp only [Option.map_some, Option.bind_some] at hx
  rcases hg : Spike.Lib.Form.group b.2.1 b.2.2 with _ | pls
  · rw [hg] at hx; simp at hx
  rw [hg] at hx
  exact h x b pls k v hb hg hx

/-- **On one-word bindings `ofEnv2` is `ofEnv`.** -/
theorem ofEnv2_eq_ofEnv {env : Env}
    (h : ∀ b ∈ env, Spike.Lib.Form.group b.2.1 b.2.2 = some (b.2.2.map .one)) : ofEnv2 env = ofEnv env := by
  induction env with
  | nil => rfl
  | cons b env ih =>
    simp only [ofEnv2, ofEnv, List.map_cons] at ih ⊢
    rw [h b (List.mem_cons_self ..), ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')]
    rfl

/-! ## The walk's points -/

/-- **`t` is a point of the lowering's walk** from `env0`, `n` over `body`. -/
def InWalk2 (cx : Scc.Lower.Ctx) (env0 : Env) (n : Nat) (body : Expr) (t : Expr) : Prop :=
  ∃ q ∈ lowerEnvs2 cx env0 n body, q.1 = t

/-- **At each point of a compiled block's walk** (`Accepted2`, not the
output extern or its loop) the lowering's environment has its immediates in
`imms2Of p` (at `ofEnv2`), and the point is in the walk. -/
theorem walk_imms2Of {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cx : Scc.Lower.Ctx} (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body,
      ImmIn (Scc.Lower.imms2Of p) (ofEnv2 q.2.1) q.1 ∧ InWalk2 cx [(d.arg, d.argTy, ps)] n d.body q.1 :=
  fun q hq => ⟨immIn_ofEnv2 (immIn_imms2Of (p := p) hp hprog hext hd hne hnl hps hpl n q hq), q, hq, rfl⟩

/-! ## The walk, construct by construct -/

section Steps

variable {P : Expr × Env × Nat → Prop} {cx : Scc.Lower.Ctx} {env : Env} {n : Nat}

/-- The walk starts at its term. -/
theorem walk2_head {e : Expr} (h : ∀ q ∈ lowerEnvs2 cx env n e, P q) : P (e, env, n) :=
  h _ (mem_lowerEnvs2_head cx env n e)

/-- The walk after `let x = op` is part of the walk at it. -/
theorem walk2_let {x : String} {op : Op} {e : Expr} {t : Ty} {ws : List Operand} {n' : Nat}
    (hs : runB (letStep cx env x op e) n = some ((t, ws), n'))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.let_ x op e), P q) : ∀ q ∈ lowerEnvs2 cx ((x, t, ws) :: env) n' e, P q :=
  fun q hq => h q (by simp [lowerEnvs2, hs, hq])

/-- The walk after `let (x, y) = a` is part of the walk at it. -/
theorem walk2_split {a : At} {x y : String} {e : Expr} {u w : Ty} {ws : List Operand} {k n' : Nat}
    (hs : runB (splitStep env a) n = some ((u, w, ws, k), n'))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.split a x y e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((y, w, ws.drop k) :: (x, u, ws.take k) :: env) n' e, P q :=
  fun q hq => h q (by simp [lowerEnvs2, hs, hq])

/-- The walk after an index unpack is part of the walk at it. -/
theorem walk2_unpack {a : At} {i x : String} {e : Expr} {b : Ty} {ws : List Operand} {n' : Nat}
    (hs : runB (Scc.Lower.evalAt env a) n = some ((.iex b, ws), n'))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.unpack a i x e), P q) : ∀ q ∈ lowerEnvs2 cx ((x, b, ws) :: env) n' e, P q :=
  fun q hq => h q (by simp [lowerEnvs2, hs, hq])

/-- The walk after a type unpack is part of the walk at it. -/
theorem walk2_unpackT {a : At} {α x : String} {e : Expr} {k : Kind} {b : Ty} {ws : List Operand} {n' : Nat}
    (hs : runB (Scc.Lower.evalAt env a) n = some ((.tex k b, ws), n'))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.unpackT a α x e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((x, Ty.substT 0 .unit b, ws) :: env) n' e, P q :=
  fun q hq => h q (by simp [lowerEnvs2, hs, hq])

/-- The walk of an `if`'s `then` branch is part of the walk at it. -/
theorem walk2_yes {a b : At} {yes no : Expr} {n' : Nat} (hs : runB (ifStep env a b) n = some ((), n'))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.ifeq a b yes no), P q) : ∀ q ∈ lowerEnvs2 cx env n' yes, P q :=
  fun q hq => h q (by simp [lowerEnvs2, hs, hq])

/-- The walk of an `if`'s `else` branch is part of the walk at it, from the
counter the `then` branch's lowering leaves. -/
theorem walk2_no {a b : At} {yes no : Expr} {n' m : Nat} (hs : runB (ifStep env a b) n = some ((), n'))
    (hy : runB (Scc.Lower.lowerExpr cx env yes) n' = some ((), m))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.ifeq a b yes no), P q) : ∀ q ∈ lowerEnvs2 cx env m no, P q :=
  fun q hq => h q (by simp [lowerEnvs2, hs, hy, hq])

end Steps

end Spike.Lib.LowerNode

