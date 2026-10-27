/-
**The closed form `lowerC2` and the lowering's walk** (ISA-neutral): the
facts an induction over `lowerC2` (`body2_segS`) reads at each construct,
next to `Spike/Lib/LowerShapeC2.lean`.

- `runB_letStep_newBuf`, `runB_letStep_xchg`, `runB_letStep_print`,
  `runB_letStep_pure`, `runB_splitStep`, `runB_unpack`,
  `runB_lowerExpr_lowerC2`: the lowering's steps run from counter `n`
  (`Spike/Lib/Src/LowerEnvImm2Of.lean`'s `runB`) on the constructs
  `lowerC2` covers, with `lowerC2`'s environments and counters.
- `walk2_tail_let` (any `let` whose step runs; `Spike/Lib/Src/AbortImm2.lean`'s
  `walk2_head`, `walk2_let` are the head and the step's form), and per
  construct `walk2_tail_add`, `_sub`, `_call`, `_print`, `_newBuf`, `_xchg`,
  `_pure`, `_split`, `_unpack`, `_yes`, `_no`: the walk `lowerEnvs2` at the
  continuation (at an `if`'s branches) is part of the walk at the construct.
- `lowerC2_fv`: every free variable of a body `lowerC2` lowers is bound in
  its environment.
- `lowerC2_term_ne`: `lowerC2`'s terminator is never `unreachable`.
- `Fresh.pure`, `Fresh.newBuf`, `Fresh.xchg`, `Fresh.print`, `Fresh.split`,
  `Fresh.unpack`: the environment past each construct is fresh from the
  counter past it.
-/
import Spike.Lib.LowerShapeC2
import Spike.Lib.Src.LowerEnvImm2Of
import Spike.Lib.LowerEnv

namespace Spike.Lib.LowerShape

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Spike.Lib.LowerNode (runB letStep splitStep ifStep lowerEnvs2 runB_letStep_add runB_letStep_sub
  runB_letStep_call runB_ifStep resp_lowerExpr runB_some_iff Fresh)

set_option linter.unusedSimpArgs false

/-! ## The lowering's steps from a counter -/

section Steps

variable {cx : Scc.Lower.Ctx} {env : Env} {x : String} {e : Expr}

theorem runB_letStep_newBuf {c : At} {τ : Ty} {tk : Ty} {kv : UInt64} {en em h : Nat} {sc hq : List Reg}
    (ha : atomV env c = some (tk, [.imm kv])) (hc : countsO cx.obj τ = some (en, em))
    (hh : Scc.Obj.header0 cx.obj .array en em = some h)
    (hw : en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em))
    (n : Nat) (hm : markR (newBufTy τ) [.reg (regName x n), imm 0] = some (sc, hq)) :
    runB (letStep cx env x (.newBuf c τ) e) n = some ((newBufTy τ, [.reg (regName x n), imm 0]), n + 1) := by
  unfold runB
  simp only [letStep, setHere]
  rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_newBuf cx env x ha hc hh hw rfl rfl), bind_ok (markWords_eq hm _)]
  rfl

theorem runB_letStep_xchg {b i v : At} {t : Ty} {bw : List Operand} {rb : Reg} {o : UInt64} {tj : Ty}
    {iv : UInt64} {μ : Mode} {u : Ty} {nu mu : Nat} {tv : Ty} {w : Operand} {s1 : Bool × Nat} {sc hq : List Reg}
    (hb : atomV env b = some (t, bw)) (hrf : refO bw = some (.reg rb, .imm o))
    (hi : atomV env i = some (tj, [.imm iv])) (he : bufElem t = some (μ, u))
    (hg : Scc.Obj.regOf u = some (nu, mu)) (hv : atomV env v = some (tv, [w]))
    (hs : Scc.Obj.slots u 0 0 = some [s1]) (n : Nat)
    (hm : markR u [.reg (regName x n)] = some (sc, hq)) :
    runB (letStep cx env x (.xchgAt b i v) e) n = some ((u, [.reg (regName x n)]), n + 1) := by
  unfold runB
  simp only [letStep, setHere]
  rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_xchg cx env x hb hrf hi he hg hv hs rfl),
    bind_ok (markWords_eq hm _)]
  rfl

theorem runB_letStep_print {g : String} {is' : List String} {a : At} {ts : List Ty}
    {xe : String × Scc.Frontend.Extern} {dg : Decl} {t : Ty} {b m c : Operand} {o : Reg}
    (hx : cx.externs.find? (·.1 == g) = some xe) (hd : cx.prog.find? (·.name == g) = some dg)
    (hrt : dg.retTy = .unit) (ha : atomV env a = some (t, [b, .reg o, m, c])) (n : Nat) :
    runB (letStep cx env x (.call g is' a ts) e) n = some ((.unit, []), n + 4) := by
  unfold runB
  simp only [letStep, setHere]
  rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_print cx env x g is' ts hx hd hrt ha rfl rfl)]
  rfl

theorem runB_letStep_pure {op : Op} {t : Ty} {ws : List Operand} {sc hq : List Reg} (hp : isPure op = true)
    (hpo : pureOp env op = some (t, ws)) (hm : markR t ws = some (sc, hq)) (n : Nat) :
    runB (letStep cx env x op e) n = some ((t, ws), n) := by
  unfold runB
  simp only [letStep, setHere]
  rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_pure cx env x hp hpo _), bind_ok (markWords_eq hm _)]
  rfl

theorem runB_splitStep {a : At} {t : Ty} {ws : List Operand} {u w : Ty} {nu : Nat}
    (ha : atomV env a = some (t, ws)) (hp : prodOf t = some (u, w)) (hv : Scc.Obj.valWords u = some nu) (n : Nat) :
    runB (splitStep env a) n = some ((u, w, ws, nu), n) := by
  unfold runB
  simp only [splitStep]
  rw [bind_ok (evalAt_eq ha _), bind_ok (needSome_eq hp _ _), bind_ok (words_eq hv _)]
  rfl

theorem runB_unpack {a : At} {b : Ty} {ws : List Operand} (ha : atomV env a = some (.iex b, ws)) (n : Nat) :
    runB (evalAt env a) n = some ((.iex b, ws), n) := by
  unfold runB
  rw [evalAt_eq ha]

/-- **The lowering of a branch runs to `lowerC2`'s counter.** -/
theorem runB_lowerExpr_lowerC2 (hf : cx.frames = none) {n : Nat} {l : Label} {r : Res2}
    (hr : lowerC2 cx env n l 0 e = some r) : runB (lowerExpr cx env e) n = some ((), r.next) := by
  have hs := lowerExpr_lowerC2 cx hf e env ({ next := n, cur := some (l, #[]) } : BState) l #[] r rfl hr
  exact (runB_some_iff (resp_lowerExpr cx e env) (s := ({ next := n, cur := some (l, #[]) } : BState)) rfl).2
    ⟨_, hs, rfl⟩

end Steps

/-! ## The walk at each construct -/

section Walk

variable {P : Expr × Env × Nat → Prop} {cx : Scc.Lower.Ctx} {env : Env} {n : Nat}

/-- **The walk past a `let` whose step runs** is part of the walk at it. -/
theorem walk2_tail_let {x : String} {op : Op} {e : Expr} {t : Ty} {ws : List Operand} {n' : Nat}
    (hs : runB (letStep cx env x op e) n = some ((t, ws), n'))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.let_ x op e), P q) : ∀ q ∈ lowerEnvs2 cx ((x, t, ws) :: env) n' e, P q :=
  fun q hq => h q (by simp [lowerEnvs2, hs, hq])

theorem walk2_tail_add {x : String} {a b : At} {e : Expr} {t t' : Ty} {p q : Operand}
    (ha : atomV env a = some (t, [p])) (hb : atomV env b = some (t', [q]))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.let_ x (.add a b) e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e, P q :=
  walk2_tail_let (runB_letStep_add ha hb n) h

theorem walk2_tail_sub {x : String} {a b : At} {e : Expr} {t t' : Ty} {p q : Operand}
    (ha : atomV env a = some (t, [p])) (hb : atomV env b = some (t', [q]))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.let_ x (.sub a b) e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e, P q :=
  walk2_tail_let (runB_letStep_sub ha hb n) h

theorem walk2_tail_call (hf : cx.frames = none) {x g : String} {is : List String} {a : At} {ts : List Ty}
    {e : Expr} {d : Decl} {t : Ty} {w : Operand} (hx : cx.externs.find? (·.1 == g) = none)
    (hd : cx.prog.find? (·.name == g) = some d) (hr : d.retTy = .int) (ha : atomV env a = some (t, [w]))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.let_ x (.call g is a ts) e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1) e, P q := by
  have hs := runB_letStep_call (e := e) (x := x) (is := is) (ts := ts) hx hd hr ha n
  simp only [hf, Option.isSome_none, Bool.false_eq_true, ite_false] at hs
  exact walk2_tail_let hs h

theorem walk2_tail_print {x g : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    {xe : String × Scc.Frontend.Extern} {dg : Decl} {t : Ty} {b m c : Operand} {o : Reg}
    (hx : cx.externs.find? (·.1 == g) = some xe) (hd : cx.prog.find? (·.name == g) = some dg)
    (hrt : dg.retTy = .unit) (ha : atomV env a = some (t, [b, .reg o, m, c]))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.let_ x (.call g is a ts) e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((x, .unit, []) :: env) (n + 4) e, P q :=
  walk2_tail_let (runB_letStep_print hx hd hrt ha n) h

theorem walk2_tail_newBuf {x : String} {c : At} {τ : Ty} {e : Expr} {tk : Ty} {kv : UInt64} {en em hh : Nat}
    {sc hq : List Reg} (ha : atomV env c = some (tk, [.imm kv])) (hc : countsO cx.obj τ = some (en, em))
    (hh' : Scc.Obj.header0 cx.obj .array en em = some hh)
    (hw : en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em))
    (hm : markR (newBufTy τ) [.reg (regName x n), imm 0] = some (sc, hq))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.let_ x (.newBuf c τ) e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((x, newBufTy τ, [.reg (regName x n), imm 0]) :: env) (n + 1) e, P q :=
  walk2_tail_let (runB_letStep_newBuf ha hc hh' hw n hm) h

theorem walk2_tail_xchg {x : String} {b i v : At} {e : Expr} {t : Ty} {bw : List Operand} {rb : Reg} {o : UInt64}
    {tj : Ty} {iv : UInt64} {μ : Mode} {u : Ty} {nu mu : Nat} {tv : Ty} {w : Operand} {s1 : Bool × Nat}
    {sc hq : List Reg} (hb : atomV env b = some (t, bw)) (hrf : refO bw = some (.reg rb, .imm o))
    (hi : atomV env i = some (tj, [.imm iv])) (he : bufElem t = some (μ, u))
    (hg : Scc.Obj.regOf u = some (nu, mu)) (hv : atomV env v = some (tv, [w]))
    (hs : Scc.Obj.slots u 0 0 = some [s1]) (hm : markR u [.reg (regName x n)] = some (sc, hq))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.let_ x (.xchgAt b i v) e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((x, u, [.reg (regName x n)]) :: env) (n + 1) e, P q :=
  walk2_tail_let (runB_letStep_xchg hb hrf hi he hg hv hs n hm) h

theorem walk2_tail_pure {x : String} {op : Op} {e : Expr} {t : Ty} {ws : List Operand} {sc hq : List Reg}
    (hp : isPure op = true) (hpo : pureOp env op = some (t, ws)) (hm : markR t ws = some (sc, hq))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.let_ x op e), P q) : ∀ q ∈ lowerEnvs2 cx ((x, t, ws) :: env) n e, P q :=
  walk2_tail_let (runB_letStep_pure hp hpo hm n) h

theorem walk2_tail_split {a : At} {x y : String} {e : Expr} {t : Ty} {ws : List Operand} {u w : Ty} {nu : Nat}
    (ha : atomV env a = some (t, ws)) (hp : prodOf t = some (u, w)) (hv : Scc.Obj.valWords u = some nu)
    (h : ∀ q ∈ lowerEnvs2 cx env n (.split a x y e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((y, w, ws.drop nu) :: (x, u, ws.take nu) :: env) n e, P q :=
  fun q hq => h q (by simp [lowerEnvs2, runB_splitStep ha hp hv, hq])

theorem walk2_tail_unpack {a : At} {i x : String} {e : Expr} {b : Ty} {ws : List Operand}
    (ha : atomV env a = some (.iex b, ws)) (h : ∀ q ∈ lowerEnvs2 cx env n (.unpack a i x e), P q) :
    ∀ q ∈ lowerEnvs2 cx ((x, b, ws) :: env) n e, P q :=
  fun q hq => h q (by simp [lowerEnvs2, runB_unpack ha, hq])

theorem walk2_tail_yes {a b : At} {yes no : Expr} {t t' : Ty} {p q : Operand}
    (ha : atomV env a = some (t, [p])) (hb : atomV env b = some (t', [q]))
    (h : ∀ q ∈ lowerEnvs2 cx env n (.ifeq a b yes no), P q) : ∀ q ∈ lowerEnvs2 cx env (n + 2) yes, P q :=
  fun q' hq => h q' (by simp [lowerEnvs2, runB_ifStep ha hb, hq])

theorem walk2_tail_no (hf : cx.frames = none) {a b : At} {yes no : Expr} {t t' : Ty} {p q : Operand}
    {ry : Res2} (ha : atomV env a = some (t, [p])) (hb : atomV env b = some (t', [q]))
    (hy : lowerC2 cx env (n + 2) (labName "then" n) 0 yes = some ry)
    (h : ∀ q ∈ lowerEnvs2 cx env n (.ifeq a b yes no), P q) : ∀ q ∈ lowerEnvs2 cx env ry.next no, P q :=
  fun q' hq => h q' (by simp [lowerEnvs2, runB_ifStep ha hb, runB_lowerExpr_lowerC2 hf hy, hq])

end Walk

/-! ## Free variables -/

/-- An atom's variables are bound where it has a value. -/
theorem atomV_bound {env : Env} {a : At} {v : Ty × List Operand} (ha : atomV env a = some v) :
    ∀ y ∈ Scc.Sem.atVars a, (env.find? (·.1 == y)).isSome := by
  intro y hy
  cases a with
  | var z =>
    simp only [Scc.Sem.atVars, List.mem_singleton] at hy
    subst hy
    simp only [atomV, Option.map_eq_some_iff] at ha
    obtain ⟨b, hb, -⟩ := ha
    simp [hb]
  | _ => simp [Scc.Sem.atVars] at hy

theorem find_cons_isSome {env : Env} {b : String × Ty × List Operand} {y : String} (hne : b.1 ≠ y)
    (h : ((b :: env).find? (·.1 == y)).isSome) : (env.find? (·.1 == y)).isSome := by
  have : (b.1 == y) = false := by simp [hne]
  simpa [List.find?_cons, this] using h

/-- **A pure operation's atoms have values** where it has one. -/
theorem pureOp_bound {env : Env} {op : Op} {v : Ty × List Operand} (h : pureOp env op = some v) :
    ∀ y ∈ Scc.Sem.opVars op, (env.find? (·.1 == y)).isSome := by
  intro y hy
  cases op with
  | atom a | nameI a =>
    simp only [Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy
    exact atomV_bound h y hy
  | pack a i τ =>
    simp only [pureOp, Option.map_eq_some_iff] at h
    obtain ⟨_, ha, -⟩ := h
    simp only [Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy
    exact atomV_bound ha y hy
  | pair a b =>
    simp only [pureOp] at h
    cases ha : atomV env a with
    | none => simp [ha] at h
    | some qa =>
    cases hb : atomV env b with
    | none => simp [ha, hb] at h
    | some qb =>
    simp only [Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hy
    rcases hy with hy | hy
    · exact atomV_bound ha y hy
    · exact atomV_bound hb y hy
  | asLanes sg w a =>
    simp only [pureOp] at h
    cases ha : atomV env a with
    | none => simp [ha] at h
    | some qa =>
    simp only [Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy
    exact atomV_bound ha y hy
  | _ => simp [pureOp] at h

/-- The free variables of `let x = op; e`: `op`'s, or `e`'s but `x`. -/
theorem mem_fv_let {x y : String} {op : Op} {e : Expr} (hy : y ∈ Scc.Sem.exprFv (.let_ x op e)) :
    y ∈ Scc.Sem.opVars op ∨ (y ∈ Scc.Sem.exprFv e ∧ x ≠ y) := by
  simp only [Scc.Sem.exprFv, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
  rcases hy with hy | ⟨hy, hne⟩
  · exact .inl hy
  · exact .inr ⟨hy, fun h => hne h.symm⟩

/-- **Every free variable of a body `lowerC2` lowers is bound** in its
environment. -/
theorem lowerC2_fv (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res2),
      lowerC2 cx env n l k e = some r → ∀ y ∈ Scc.Sem.exprFv e, (env.find? (·.1 == y)).isSome := by
  -- the step at a `let`: its operation's atoms bound, the continuation bound past one binding
  have hlet : ∀ {env : Env} {x : String} {op : Op} {e : Expr} {b : String × Ty × List Operand},
      b.1 = x → (∀ y ∈ Scc.Sem.opVars op, (env.find? (·.1 == y)).isSome) →
      (∀ y ∈ Scc.Sem.exprFv e, ((b :: env).find? (·.1 == y)).isSome) →
      ∀ y ∈ Scc.Sem.exprFv (.let_ x op e), (env.find? (·.1 == y)).isSome := by
    intro env x op e b hb hop he y hy
    rcases mem_fv_let hy with hy | ⟨hy, hne⟩
    · exact hop y hy
    · exact find_cons_isSome (hb ▸ hne) (he y hy)
  have h1 : ∀ {env : Env} {a : At} {v : Ty × List Operand} {op : Op}, Scc.Sem.opAts op = [a] →
      atomV env a = some v → ∀ y ∈ Scc.Sem.opVars op, (env.find? (·.1 == y)).isSome := by
    intro env a v op hop ha y hy
    simp only [Scc.Sem.opVars, hop, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hy
    rcases hy with hy | hy
    · exact atomV_bound ha y hy
    · split at hy
      · simp [Scc.Sem.opAts] at hop
      · simp at hy
  have h2 : ∀ {env : Env} {a b : At} {va vb : Ty × List Operand} {op : Op}, Scc.Sem.opAts op = [a, b] →
      atomV env a = some va → atomV env b = some vb →
      ∀ y ∈ Scc.Sem.opVars op, (env.find? (·.1 == y)).isSome := by
    intro env a b va vb op hop ha hb y hy
    simp only [Scc.Sem.opVars, hop, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · exact atomV_bound ha y hy
    · exact atomV_bound hb y hy
    · split at hy
      · simp [Scc.Sem.opAts] at hop
      · simp at hy
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | add a b =>
      obtain ⟨_, _, _, _, r', ha, hb, hr', -⟩ := lowerC2_add_inv hr
      exact hlet rfl (h2 rfl ha hb) (ih _ _ _ _ _ hr')
    | sub a b =>
      obtain ⟨_, _, _, _, r', ha, hb, hr', -⟩ := lowerC2_sub_inv hr
      exact hlet rfl (h2 rfl ha hb) (ih _ _ _ _ _ hr')
    | call g is a ts =>
      rcases lowerC2_call_inv hr with ⟨_, _, _, r', -, -, -, ha, hr', -⟩
          | ⟨_, _, _, _, _, _, _, r', -, -, -, ha, hr', -⟩
      · exact hlet rfl (h1 rfl ha) (ih _ _ _ _ _ hr')
      · exact hlet rfl (h1 rfl ha) (ih _ _ _ _ _ hr')
    | newBuf c τ =>
      obtain ⟨_, _, _, _, _, _, _, r', ha, -, -, -, -, hr', -⟩ := lowerC2_newBuf_inv hr
      exact hlet rfl (h1 rfl ha) (ih _ _ _ _ _ hr')
    | xchgAt b i v =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r', hb, -, hi, -, -, hv, -, -, hr', -⟩ :=
        lowerC2_xchg_inv hr
      refine hlet rfl ?_ (ih _ _ _ _ _ hr')
      intro y hy
      simp only [Scc.Sem.opVars, Scc.Sem.opAts, List.append_nil, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      obtain ⟨a', ha', hy⟩ := hy
      rcases ha' with rfl | rfl | rfl
      · exact atomV_bound hb y hy
      · exact atomV_bound hi y hy
      · exact atomV_bound hv y hy
    | _ =>
      first
      | (obtain ⟨_, _, _, _, r', hpo, -, hr', -⟩ := lowerC2_pure_inv rfl hr
         exact hlet rfl (pureOp_bound hpo) (ih _ _ _ _ _ hr'))
      | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r hr z hz
    obtain ⟨_, _, _, _, _, ha, -, -, hr'⟩ := lowerC2_split_inv hr
    simp only [Scc.Sem.exprFv, List.mem_append, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at hz
    rcases hz with hz | ⟨hz, hx, hy⟩
    · exact atomV_bound ha z hz
    · exact find_cons_isSome (fun h => hx h.symm) (find_cons_isSome (fun h => hy h.symm) (ih _ _ _ _ _ hr' z hz))
  | unpack a i x e ih =>
    intro env n l k r hr z hz
    obtain ⟨_, _, ha, hr'⟩ := lowerC2_unpack_inv hr
    simp only [Scc.Sem.exprFv, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hz
    rcases hz with hz | ⟨hz, hx⟩
    · exact atomV_bound ha z hz
    · exact find_cons_isSome (fun h => hx h.symm) (ih _ _ _ _ _ hr' z hz)
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr z hz
    obtain ⟨_, _, _, _, ry, rn, ha, hb, hy, hn, -⟩ := lowerC2_ifeq_inv hr
    simp only [Scc.Sem.exprFv, List.mem_append] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · exact atomV_bound ha z hz
    · exact atomV_bound hb z hz
    · exact ihy _ _ _ _ _ hy z hz
    · exact ihn _ _ _ _ _ hn z hz
  | ret a =>
    intro env n l k r hr z hz
    obtain ⟨_, _, ha, -⟩ := lowerC2_ret_inv hr
    exact atomV_bound ha z hz
  | _ => intro env n l k r hr; simp [lowerC2] at hr

/-! ## The terminator -/

/-- **`lowerC2`'s terminator is never `unreachable`.** -/
theorem lowerC2_term_ne (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res2),
      lowerC2 cx env n l k e = some r → r.term ≠ .unreachable := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | add a b => obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_add_inv hr; exact ih _ _ _ _ r' hr'
    | sub a b => obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_sub_inv hr; exact ih _ _ _ _ r' hr'
    | call g is a ts =>
      rcases lowerC2_call_inv hr with ⟨_, _, _, r', -, -, -, -, hr', rfl⟩
          | ⟨_, _, _, _, _, _, _, r', -, -, -, -, hr', rfl⟩
      · exact ih _ _ _ _ r' hr'
      · exact ih _ _ _ _ r' hr'
    | newBuf c τ =>
      obtain ⟨_, _, _, _, _, _, _, r', -, -, -, -, -, hr', rfl⟩ := lowerC2_newBuf_inv hr
      exact ih _ _ _ _ r' hr'
    | xchgAt b i v =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r', -, -, -, -, -, -, -, -, hr', rfl⟩ :=
        lowerC2_xchg_inv hr
      exact ih _ _ _ _ r' hr'
    | _ =>
      first
      | (obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_pure_inv rfl hr
         exact ih _ _ _ _ r' hr')
      | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, _, -, -, -, hr'⟩ := lowerC2_split_inv hr
    exact ih _ _ _ _ _ hr'
  | unpack a i x e ih =>
    intro env n l k r hr
    obtain ⟨_, _, -, hr'⟩ := lowerC2_unpack_inv hr
    exact ih _ _ _ _ _ hr'
  | ifeq a b yes no _ _ =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, _, _, -, -, -, -, rfl⟩ := lowerC2_ifeq_inv hr
    simp
  | ret a =>
    intro env n l k r hr
    obtain ⟨_, _, -, rfl⟩ := lowerC2_ret_inv hr
    simp
  | _ => intro env n l k r hr; simp [lowerC2] at hr

/-! ## Fresh registers -/

section Fresh

variable {env : Env} {n : Nat}

/-- An atom's words are the environment's or immediates. -/
theorem atomV_words {a : At} {t : Ty} {ws : List Operand} (ha : atomV env a = some (t, ws)) :
    ∀ o ∈ ws, ∀ r, o = .reg r → ∃ v ∈ env, o ∈ v.2.2 := by
  intro o ho r hr
  cases a with
  | var z =>
    simp only [atomV, Option.map_eq_some_iff] at ha
    obtain ⟨⟨z', u, vs⟩, hb, he⟩ := ha
    cases he
    exact ⟨_, List.mem_of_find?_eq_some hb, ho⟩
  | lit m =>
    simp only [atomV] at ha
    split at ha <;> cases ha <;> simp at ho <;> subst ho <;> cases hr
  | unit =>
    simp only [atomV, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨-, rfl⟩ := ha
    cases ho

/-- Words drawn from the environment's (or immediates) are fresh with it. -/
theorem _root_.Spike.Lib.LowerNode.Fresh.ofWords (h : Fresh env n) {x : String} {t : Ty} {ws : List Operand}
    (hw : ∀ o ∈ ws, ∀ r, o = .reg r → ∃ v ∈ env, o ∈ v.2.2) : Fresh ((x, t, ws) :: env) n := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · intro o ho r hr
    obtain ⟨v', hv', ho'⟩ := hw o ho r hr
    exact h v' hv' o ho' r hr
  · exact h v hv

theorem pureOp_words {op : Op} {t : Ty} {ws : List Operand} (h : pureOp env op = some (t, ws)) :
    ∀ o ∈ ws, ∀ r, o = .reg r → ∃ v ∈ env, o ∈ v.2.2 := by
  cases op with
  | atom a | nameI a => exact atomV_words h
  | pack a i τ =>
    simp only [pureOp, Option.map_eq_some_iff] at h
    obtain ⟨⟨t', ws'⟩, ha, he⟩ := h
    cases he
    exact atomV_words ha
  | pair a b =>
    simp only [pureOp] at h
    cases ha : atomV env a with
    | none => simp [ha] at h
    | some qa =>
    obtain ⟨ta, wa⟩ := qa
    cases hb : atomV env b with
    | none => simp [ha, hb] at h
    | some qb =>
    obtain ⟨tb, wb⟩ := qb
    simp [ha, hb] at h
    obtain ⟨-, rfl⟩ := h
    intro o ho r hr
    rcases List.mem_append.mp ho with ho | ho
    · exact atomV_words ha o ho r hr
    · exact atomV_words hb o ho r hr
  | asLanes sg w a =>
    simp only [pureOp] at h
    cases ha : atomV env a with
    | none => simp [ha] at h
    | some qa =>
    obtain ⟨ta, wa⟩ := qa
    rcases wa with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> simp [ha] at h
    obtain ⟨-, rfl⟩ := h
    intro o ho r hr
    exact atomV_words ha o ho r hr
  | _ => simp [pureOp] at h

theorem _root_.Spike.Lib.LowerNode.Fresh.pure (h : Fresh env n)
    {op : Op} {t : Ty} {ws : List Operand} (hpo : pureOp env op = some (t, ws))
    (x : String) : Fresh ((x, t, ws) :: env) n :=
  h.ofWords (pureOp_words hpo)

/-- A fresh register `regName x n` with immediates, fresh past itself. -/
theorem _root_.Spike.Lib.LowerNode.Fresh.reg (h : Fresh env n) (x : String) (t : Ty) (rest : List Operand)
    (hr : ∀ o ∈ rest, ∀ r, o ≠ .reg r) : Fresh ((x, t, .reg (regName x n) :: rest) :: env) (n + 1) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · intro o ho r ho' y k hk
    rcases List.mem_cons.mp ho with rfl | ho
    · cases ho'
      exact regName_ne (by omega)
    · exact absurd ho' (hr o ho r)
  · intro o ho r hr' y k hk
    exact h v hv o ho r hr' y k (by omega)

theorem _root_.Spike.Lib.LowerNode.Fresh.newBuf (h : Fresh env n) (x : String) (τ : Ty) :
    Fresh ((x, newBufTy τ, [.reg (regName x n), imm 0]) :: env) (n + 1) :=
  h.reg x _ [imm 0] (by simp [imm])

theorem _root_.Spike.Lib.LowerNode.Fresh.xchg (h : Fresh env n)
    (x : String) (u : Ty) : Fresh ((x, u, [.reg (regName x n)]) :: env) (n + 1) :=
  h.reg x u [] (by simp)

theorem _root_.Spike.Lib.LowerNode.Fresh.print (h : Fresh env n)
    (x : String) : Fresh ((x, .unit, []) :: env) (n + 4) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · intro o ho; cases ho
  · intro o ho r hr y k hk
    exact h v hv o ho r hr y k (by omega)

theorem _root_.Spike.Lib.LowerNode.Fresh.split (h : Fresh env n)
    {a : At} {t : Ty} {ws : List Operand} (ha : atomV env a = some (t, ws))
    (x y : String) (u w : Ty) (k : Nat) : Fresh ((y, w, ws.drop k) :: (x, u, ws.take k) :: env) n := by
  have hw := atomV_words ha
  refine (h.ofWords fun o ho r hr => hw o (List.mem_of_mem_take ho) r hr).ofWords fun o ho r hr => ?_
  obtain ⟨v, hv, ho'⟩ := hw o (List.mem_of_mem_drop ho) r hr
  exact ⟨v, List.mem_cons_of_mem _ hv, ho'⟩

theorem _root_.Spike.Lib.LowerNode.Fresh.unpack (h : Fresh env n)
    {a : At} {b : Ty} {ws : List Operand} (ha : atomV env a = some (.iex b, ws))
    (x : String) : Fresh ((x, b, ws) :: env) n :=
  h.ofWords (atomV_words ha)

end Fresh

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerShape.lowerC2_fv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lowerC2_fv

/-- info: 'Spike.Lib.LowerShape.walk2_tail_no' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms walk2_tail_no

end Spike.Lib.LowerShape
