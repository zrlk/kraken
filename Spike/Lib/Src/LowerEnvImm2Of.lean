/-
**The lowering's walk, from the lowering's own helpers** (ISA-neutral), for
bodies past `Accepted1` (`Accepted2`: pairs, packages, buffers, externs).

- `runB m n`: run builder `m` from counter `n` (an open block, nothing built
  yet): its result and final counter.
- `lowerEnvs2 cx env n e`: the points `lowerExpr cx` passes on `e` from `env`
  and counter `n`, with their environment and counter. Every environment and
  counter comes from running the lowering's own steps (`lowerOp` and
  `markWords` for a `let`, `evalAt`/`prodOf`/`words` for a pair split,
  `evalAt` for an unpack, `evalOne` and the two `freshLabel`s for an `if`,
  whose `else` branch starts at the counter `lowerExpr` leaves after the
  `then` branch).
- `lowerEnvs2_eq`: on an `Accepted1` body (`body1`, callees code blocks
  returning an `Int`, not externs) it is `lowerEnvsC cx.frames`.

- `Resp m`: `m`'s result, success and final counter depend only on the
  counter and on whether a block is open (`SR`), not on the blocks, marks,
  source point or register kinds built so far. Proved for every builder step
  of the lowering, `lowerOp` and `lowerExpr` included (`resp_lowerOp`,
  `resp_lowerExpr`), by the `resp` tactic.
- `KC m`: from an open block, a successful `m` ends with an open block
  (`terminate` is always followed by `startBlock`); `kc_lowerOp`,
  `kc_letStep`, `kc_splitStep`, `kc_ifStep`. Not true of `lowerExpr`.
- `runB_congr`, `runB_some_iff`, `runB_none_iff`, `runB_some_iff_kc`: for a
  `Resp` step, a run from any state with an open block agrees with `runB`
  from its counter (same success, result and counter).

That every placement-trace point `lowerExpr` records is a point of
`lowerEnvs2` (an induction over `e` from `runB_some_iff` for the prefixes and
`resp_lowerExpr` for the `then` branch) is `lowerExpr_marks`
(`LowerMarks2.lean`); with `immIn_imms2Of`, every trace point of an
`Accepted2` block has its immediates (`lowerDeclMarks_immIn2`,
`LowerMarksImm2.lean`).
-/
import Spike.Lib.LowerEnvImmC1Of

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (B BState Env lowerOp markWords evalAt evalOne needSome prodOf words lowerExpr setHere
  freshLabel body1)
open Scc.Lower.Inv (atomV cntC regName bind_ok modify_eq evalAt_eq evalOne_eq markWords_scalar1 lowerOp_add
  lowerOp_sub lowerOp_call callBlock_none callBlock_some freshLabel_eq lowerExpr_lowerC lowerC_isSome
  lowerC_next CalleesC EnvScalar envScalar_cons atomV_of_atom0)

/-- **Run a builder from counter `n`**, with an open block and nothing built
yet: its result and final counter; `none` if it fails. -/
def runB {α : Type} (m : B α) (n : Nat) : Option (α × Nat) :=
  match m { next := n } with
  | .ok (a, s) => some (a, s.next)
  | .error _ => none

theorem runB_eq {α : Type} {m : B α} {n : Nat} {a : α} {s : BState}
    (h : m { next := n } = .ok (a, s)) : runB m n = some (a, s.next) := by
  simp [runB, h]

/-- The steps of `lowerExpr` on `let x = op; e` before lowering `e`: the
source point, `op`'s lowering and the marking of its words. -/
def letStep (cx : Scc.Lower.Ctx) (env : Env) (x : String) (op : Op) (e : Expr) : B (Ty × List Scc.IR.Operand) := do
  setHere (env, .let_ x op e)
  let r ← lowerOp cx env x op
  markWords r.1 r.2
  pure r

/-- The steps of `lowerExpr` on `let (x, y) = a; e` before lowering `e`:
`a`'s type and words and the first component's type and word count. -/
def splitStep (env : Env) (a : At) : B (Ty × Ty × List Scc.IR.Operand × Nat) := do
  let (t, ws) ← evalAt env a
  let (u, w) ← needSome (prodOf t) "let (x, y): not a pair"
  let k ← words u
  pure (u, w, ws, k)

/-- The steps of `lowerExpr` on `if a = b` before its `then` branch: the
operands and the two labels. -/
def ifStep (env : Env) (a b : At) : B Unit := do
  let _ ← evalOne env a "if"
  let _ ← evalOne env b "if"
  let _ ← freshLabel "then"
  let _ ← freshLabel "else"
  pure ()

/-- **The lowering's walk** over `e` from `env` and `n`, from the
lowering's own steps: at each point, the term still to lower, the
environment and the counter (`lowerExpr cx`). -/
def lowerEnvs2 (cx : Scc.Lower.Ctx) (env : Env) (n : Nat) : Expr → List (Expr × Env × Nat)
  | .let_ x op e =>
      (.let_ x op e, env, n) ::
        match runB (letStep cx env x op e) n with
        | some ((t, ws), n') => lowerEnvs2 cx ((x, t, ws) :: env) n' e
        | none => []
  | .split a x y e =>
      (.split a x y e, env, n) ::
        match runB (splitStep env a) n with
        | some ((u, w, ws, k), n') => lowerEnvs2 cx ((y, w, ws.drop k) :: (x, u, ws.take k) :: env) n' e
        | none => []
  | .unpack a i x e =>
      (.unpack a i x e, env, n) ::
        match runB (evalAt env a) n with
        | some ((.iex b, ws), n') => lowerEnvs2 cx ((x, b, ws) :: env) n' e
        | _ => []
  | .unpackT a α x e =>
      (.unpackT a α x e, env, n) ::
        match runB (evalAt env a) n with
        | some ((.tex _ b, ws), n') => lowerEnvs2 cx ((x, Ty.substT 0 .unit b, ws) :: env) n' e
        | _ => []
  | .ifeq a b yes no =>
      (.ifeq a b yes no, env, n) ::
        match runB (ifStep env a b) n with
        | some (_, n') =>
            lowerEnvs2 cx env n' yes ++
              match runB (lowerExpr cx env yes) n' with
              | some (_, m) => lowerEnvs2 cx env m no
              | none => []
        | none => []
  | e => [(e, env, n)]

/-! ## On `Accepted1` bodies: `lowerEnvsC` -/

theorem runB_letStep_scalar {cx : Scc.Lower.Ctx} {env : Env} {x : String} {a : At} {e : Expr} {t : Ty}
    {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) (ht : Scc.Lower.Inv.scalar1 t = true) (n : Nat) :
    runB (letStep cx env x (.atom a) e) n = some ((t, [w]), n) := by
  unfold runB
  simp only [letStep, setHere, lowerOp]
  rw [bind_ok (modify_eq _ _), bind_ok (evalAt_eq ha _), bind_ok (markWords_scalar1 ht _)]
  rfl

theorem runB_letStep_add {cx : Scc.Lower.Ctx} {env : Env} {x : String} {a b : At} {e : Expr} {t t' : Ty}
    {p q : Scc.IR.Operand} (ha : atomV env a = some (t, [p])) (hb : atomV env b = some (t', [q])) (n : Nat) :
    runB (letStep cx env x (.add a b) e) n = some ((.int, [.reg (regName x n)]), n + 1) := by
  unfold runB
  simp only [letStep, setHere]
  rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_add cx env x ha hb rfl),
    bind_ok (markWords_scalar1 rfl _)]
  rfl

theorem runB_letStep_sub {cx : Scc.Lower.Ctx} {env : Env} {x : String} {a b : At} {e : Expr} {t t' : Ty}
    {p q : Scc.IR.Operand} (ha : atomV env a = some (t, [p])) (hb : atomV env b = some (t', [q])) (n : Nat) :
    runB (letStep cx env x (.sub a b) e) n = some ((.int, [.reg (regName x n)]), n + 1) := by
  unfold runB
  simp only [letStep, setHere]
  rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_sub cx env x ha hb rfl),
    bind_ok (markWords_scalar1 rfl _)]
  rfl

theorem runB_letStep_call {cx : Scc.Lower.Ctx} {env : Env} {x g : String} {is : List String} {a : At} {ts : List Ty}
    {e : Expr} {d : Decl} {t : Ty} {w : Scc.IR.Operand} (hx : cx.externs.find? (·.1 == g) = none)
    (hd : cx.prog.find? (·.name == g) = some d) (hr : d.retTy = .int) (ha : atomV env a = some (t, [w]))
    (n : Nat) :
    runB (letStep cx env x (.call g is a ts) e) n =
      some ((.int, [.reg (regName "r" n)]), n + if cx.frames.isSome then 7 else 1) := by
  unfold runB
  simp only [letStep, setHere]
  rw [bind_ok (modify_eq _ _)]
  cases hf : cx.frames with
  | none =>
    rw [bind_ok (lowerOp_call env x g hd hr ha (callBlock_none g w hf hx rfl rfl)),
      bind_ok (markWords_scalar1 rfl _)]
    rfl
  | some fr =>
    rw [bind_ok (lowerOp_call env x g hd hr ha (callBlock_some g w hf hx rfl rfl)),
      bind_ok (markWords_scalar1 rfl _)]
    rfl

theorem runB_ifStep {env : Env} {a b : At} {t t' : Ty} {p q : Scc.IR.Operand}
    (ha : atomV env a = some (t, [p])) (hb : atomV env b = some (t', [q])) (n : Nat) :
    runB (ifStep env a b) n = some ((), n + 2) := by
  unfold runB
  simp only [ifStep]
  rw [bind_ok (evalOne_eq ha _ _), bind_ok (evalOne_eq hb _ _), bind_ok (freshLabel_eq _ _),
    bind_ok (freshLabel_eq _ _)]
  rfl

/-- **The lowering's counter after an `Accepted1` branch** is `cntC`'s. -/
theorem runB_lowerExpr {cx : Scc.Lower.Ctx} {earlier : List String} (hcx : CalleesC cx.prog cx.externs earlier)
    {e : Expr} {scope : List String} {env : Env} (hb : body1 earlier scope e = true) (h : EnvScalar scope env)
    (n : Nat) : runB (lowerExpr cx env e) n = some ((), n + cntC cx.frames e) := by
  obtain ⟨r, hr⟩ := lowerC_isSome cx hcx e scope env n "entry" 0 hb h
  have hl := lowerExpr_lowerC cx e env { next := n } "entry" #[] r rfl hr
  rw [runB_eq hl]
  simp [lowerC_next cx e env n "entry" 0 r hr]

/-- **On an `Accepted1` body the walk is `lowerEnvsC`**: same points,
environments and counters. -/
theorem lowerEnvs2_eq (cx : Scc.Lower.Ctx) {earlier : List String} (hcx : CalleesC cx.prog cx.externs earlier) :
    ∀ (e : Expr) (scope : List String) (env : Env) (n : Nat),
      body1 earlier scope e = true → EnvScalar scope env → lowerEnvs2 cx env n e = lowerEnvsC cx.frames env n e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n hb h
    cases op with
    | atom a =>
      simp only [body1, Scc.Lower.atom1, Bool.and_eq_true] at hb
      obtain ⟨t, w, ha, ht⟩ := atomV_of_atom0 hb.1 h
      simp only [lowerEnvs2, lowerEnvsC, runB_letStep_scalar ha ht, ha]
      rw [ih (x :: scope) _ n hb.2 (envScalar_cons h x w ht)]
    | add a b =>
      simp only [body1, Scc.Lower.atom1, Bool.and_eq_true] at hb
      obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 hb.1.1 h
      obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb.1.2 h
      simp only [lowerEnvs2, lowerEnvsC, runB_letStep_add ha hb']
      rw [ih (x :: scope) _ (n + 1) hb.2 (envScalar_cons h x _ rfl)]
    | sub a b =>
      simp only [body1, Scc.Lower.atom1, Bool.and_eq_true] at hb
      obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 hb.1.1 h
      obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb.1.2 h
      simp only [lowerEnvs2, lowerEnvsC, runB_letStep_sub ha hb']
      rw [ih (x :: scope) _ (n + 1) hb.2 (envScalar_cons h x _ rfl)]
    | call g is a ts =>
      simp only [body1, Scc.Lower.callee1, Scc.Lower.atom1, Bool.and_eq_true] at hb
      obtain ⟨⟨⟨⟨⟨hg, -⟩, -⟩, -⟩, ha0⟩, he⟩ := hb
      obtain ⟨hx, dg, hd, hrt⟩ := hcx g (by simpa using hg)
      obtain ⟨t, w, ha, -⟩ := atomV_of_atom0 ha0 h
      simp only [lowerEnvs2, lowerEnvsC, runB_letStep_call hx hd hrt ha]
      rw [ih (x :: scope) _ _ he (envScalar_cons h x (t := .int) _ rfl)]
    | _ => simp [body1] at hb
  | ifeq a b yes no ihy ihn =>
    intro scope env n hb h
    simp only [body1, Scc.Lower.atom1, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨ha0, hb0⟩, hy0⟩, hn0⟩ := hb
    obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 ha0 h
    obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb0 h
    simp only [lowerEnvs2, lowerEnvsC, runB_ifStep ha hb', runB_lowerExpr hcx hy0 h]
    rw [ihy scope env (n + 2) hy0 h, ihn scope env _ hn0 h]
  | ret a => intro _ _ _ _ _; simp [lowerEnvs2, lowerEnvsC]
  | _ => intro scope env n hb; simp [body1] at hb

/-- **On an `Accepted1` body every point of the walk is `lowerEnvsC`'s.** -/
theorem lowerEnvs2_sub (cx : Scc.Lower.Ctx) {earlier : List String} (hcx : CalleesC cx.prog cx.externs earlier)
    {e : Expr} {scope : List String} {env : Env} {n : Nat} (hb : body1 earlier scope e = true)
    (h : EnvScalar scope env) {q : Expr × Env × Nat} (hq : q ∈ lowerEnvs2 cx env n e) :
    q ∈ lowerEnvsC cx.frames env n e := by
  rwa [← lowerEnvs2_eq cx hcx e scope env n hb h]

/-! ## Results depend only on the counter and the open block -/

section Congr
open Scc.IR
open Scc.Lower

/-- Two builder states agree on what the lowering's results and counter
depend on: the counter and whether a block is open. -/
def SR (s t : BState) : Prop := s.next = t.next ∧ s.cur.isSome = t.cur.isSome

/-- Two runs agree: both fail, or both succeed with the same result in
agreeing states. -/
def ResRel {α : Type} : Except String (α × BState) → Except String (α × BState) → Prop
  | .ok (a, s), .ok (b, t) => a = b ∧ SR s t
  | .error _, .error _ => True
  | _, _ => False

/-- **A builder step whose result and counter depend only on the counter
and whether a block is open** (not on the blocks, labels, trace or register
kinds built so far). -/
def Resp {α : Type} (m : B α) : Prop := ∀ s t, SR s t → ResRel (m s) (m t)

theorem bind_error {α β : Type} {m : B α} {f : α → B β} {s : BState} {e : String}
    (h : m s = .error e) : (m >>= f) s = .error e := by
  show (do let (a, s) ← m s; f a s : Except String _) = _
  rw [h]; rfl

theorem Resp.bind {α β : Type} {m : B α} {f : α → B β} (hm : Resp m) (hf : ∀ a, Resp (f a)) :
    Resp (m >>= f) := by
  intro s t h
  have hr := hm s t h
  rcases hs : m s with e | ⟨a, s'⟩ <;> rcases ht : m t with e' | ⟨b, t'⟩ <;>
    rw [hs, ht] at hr <;> simp only [ResRel] at hr
  · rw [bind_error hs, bind_error ht]; trivial
  · obtain ⟨rfl, h'⟩ := hr
    rw [Scc.Lower.Inv.bind_ok hs, Scc.Lower.Inv.bind_ok ht]
    exact hf a s' t' h'

theorem Resp.pure {α : Type} (a : α) : Resp (Pure.pure a : B α) := fun _ _ h => ⟨rfl, h⟩

theorem Resp.throw {α : Type} (e : String) : Resp (throw e : B α) := fun _ _ _ => trivial

/-- A step whose result, counter and open-block flag are functions of the
counter and the open-block flag. -/
theorem resp_of_fn {α : Type} {m : B α} (a : Nat → Bool → α) (N : Nat → Bool → Nat) (C : Nat → Bool → Bool)
    (h : ∀ s, ∃ s', m s = .ok (a s.next s.cur.isSome, s') ∧ s'.next = N s.next s.cur.isSome ∧
      s'.cur.isSome = C s.next s.cur.isSome) : Resp m := by
  intro s t hst
  obtain ⟨s', hs, hs1, hs2⟩ := h s
  obtain ⟨t', ht, ht1, ht2⟩ := h t
  rw [hs, ht]
  obtain ⟨h1, h2⟩ := hst
  refine ⟨by rw [h1, h2], ?_, ?_⟩
  · rw [hs1, ht1, h1, h2]
  · rw [hs2, ht2, h1, h2]

/-- A step that keeps the counter and the open block. -/
theorem resp_keep {α : Type} {m : B α} (a : α) (h : ∀ s, ∃ s', m s = .ok (a, s') ∧ s'.next = s.next ∧
    s'.cur = s.cur) : Resp m :=
  resp_of_fn (fun _ _ => a) (fun n _ => n) (fun _ c => c) fun s => by
    obtain ⟨s', h1, h2, h3⟩ := h s
    exact ⟨s', h1, h2, by rw [h3]⟩

theorem resp_markAt (n : Node) (p : Point) : Resp (markAt n p) :=
  resp_keep () fun _ => ⟨_, rfl, rfl, rfl⟩

theorem resp_setHere (p : Point) : Resp (setHere p) :=
  resp_keep () fun _ => ⟨_, rfl, rfl, rfl⟩

theorem resp_markHeap (r : Reg) : Resp (markHeap r) :=
  resp_keep () fun s => by
    unfold markHeap; rw [Scc.Lower.Inv.modify_eq]; split <;> exact ⟨_, rfl, rfl, rfl⟩

theorem resp_markScalar (r : Reg) : Resp (markScalar r) :=
  resp_keep () fun s => by
    unfold markScalar; rw [Scc.Lower.Inv.modify_eq]; split <;> exact ⟨_, rfl, rfl, rfl⟩

theorem resp_fresh (hint : String) : Resp (fresh hint) :=
  resp_of_fn (fun n _ => Scc.Lower.Inv.regName hint n) (fun n _ => n + 1) (fun _ c => c) fun s =>
    ⟨_, Scc.Lower.Inv.fresh_eq hint s, rfl, rfl⟩

theorem resp_freshLabel (hint : String) : Resp (freshLabel hint) :=
  resp_of_fn (fun n _ => Scc.Lower.Inv.labName hint n) (fun n _ => n + 1) (fun _ c => c) fun s =>
    ⟨_, Scc.Lower.Inv.freshLabel_eq hint s, rfl, rfl⟩

theorem resp_terminate (t : Term) : Resp (terminate t) :=
  resp_of_fn (fun _ _ => ()) (fun n _ => n) (fun _ _ => false) fun s => by
    unfold terminate; rw [Scc.Lower.Inv.modify_eq]
    rcases hc : s.cur with _ | ⟨l, is⟩ <;> simp [hc]

-- `hc`/`hh` are used in only some of the `all_goals` cases.
set_option linter.unusedSimpArgs false in
/-- The marking part of `emit` keeps the counter and the open block. -/
theorem emit_shape (i : Inst) (s : BState) : ∃ s', emit i s = .ok ((), s') ∧
    s'.next = s.next + (if s.cur.isSome then 0 else 1) ∧ s'.cur.isSome = true := by
  unfold emit
  rw [Scc.Lower.Inv.bind_ok (Scc.Lower.Inv.modify_eq _ _)]
  rcases hc : s.cur with _ | ⟨l, is⟩
  all_goals
    simp only [hc]
    cases i
    all_goals first
      | exact ⟨_, rfl, by simp, by simp⟩
      | (simp only [↓reduceIte]; rw [Scc.Lower.Inv.get_bind]
         rcases hh : s.here with _ | p <;> simp only [hh] <;> exact ⟨_, rfl, by simp, by simp⟩)

theorem resp_emit (i : Inst) : Resp (emit i) :=
  resp_of_fn (fun _ _ => ()) (fun n c => n + if c then 0 else 1) (fun _ _ => true) (emit_shape i)

theorem resp_startBlock (l : Label) : Resp (startBlock l) :=
  resp_of_fn (fun _ _ => ()) (fun n _ => n) (fun _ _ => true) fun s => by
    unfold startBlock
    rcases hc : s.cur with _ | ⟨l', is⟩ <;> rcases hh : s.here with _ | p <;>
      simp [hc, hh, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, Except.bind, terminate,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.pure, StateT.pure, pure, markAt]

/-- A read of the state followed by a step that only marks. -/
theorem resp_get_unit {g : BState → B Unit}
    (h : ∀ s0 s, ∃ s', g s0 s = .ok ((), s') ∧ s'.next = s.next ∧ s'.cur = s.cur) : Resp (get >>= g) := by
  intro s t hst
  show ResRel (g s s) (g t t)
  obtain ⟨s', hs, hs1, hs2⟩ := h s s
  obtain ⟨t', ht, ht1, ht2⟩ := h t t
  rw [hs, ht]
  exact ⟨rfl, by rw [hs1, ht1]; exact hst.1, by rw [hs2, ht2]; exact hst.2⟩

/-- A read of the state followed by a step that only marks, then `k`. -/
theorem resp_get_k {α : Type} {g : BState → B α} {k : B α}
    (h : ∀ s0 s, ∃ s', g s0 s = k s' ∧ s'.next = s.next ∧ s'.cur = s.cur) (hk : Resp k) : Resp (get >>= g) := by
  intro s t hst
  show ResRel (g s s) (g t t)
  obtain ⟨s', hs, hs1, hs2⟩ := h s s
  obtain ⟨t', ht, ht1, ht2⟩ := h t t
  rw [hs, ht]
  exact hk s' t' ⟨by rw [hs1, ht1]; exact hst.1, by rw [hs2, ht2]; exact hst.2⟩

theorem Resp.forIn {α β : Type} (xs : List α) (b : β) {f : α → β → B (ForInStep β)}
    (hf : ∀ a b, Resp (f a b)) : Resp (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact Resp.pure b
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine Resp.bind (hf x b) fun r => ?_
    cases r with
    | done b' => exact Resp.pure b'
    | yield b' => exact ih b'

theorem Resp.mapM {α β : Type} (xs : List α) {f : α → B β} (hf : ∀ a, Resp (f a)) : Resp (xs.mapM f) := by
  induction xs with
  | nil => exact Resp.pure []
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact Resp.bind (hf x) fun a => Resp.bind ih fun as => Resp.pure _

/-- The steps proved `Resp` so far (extended after each lemma). -/
syntax "resp_leaf" : tactic
macro_rules | `(tactic| resp_leaf) => `(tactic| fail "no leaf")

syntax "resp_core" : tactic
macro_rules
  | `(tactic| resp_core) => `(tactic| first
      | (with_reducible apply resp_get_unit
         intro _ _; split <;> exact ⟨_, rfl, rfl, rfl⟩)
      | (with_reducible apply resp_get_k
         · intro s0 _
           generalize s0.marks.back? = o
           rcases o with _ | ⟨_ | _, _⟩ <;>
             first | exact ⟨_, rfl, rfl, rfl⟩ | exact ⟨_, Scc.Lower.Inv.bind_ok rfl, rfl, rfl⟩)
      | with_reducible (first
        | resp_leaf
        | exact Resp.pure _
        | exact Resp.throw _
        | exact resp_markAt _ _
        | exact resp_setHere _
        | exact resp_markHeap _
        | exact resp_markScalar _
        | exact resp_fresh _
        | exact resp_freshLabel _
        | exact resp_terminate _
        | exact resp_emit _
        | exact resp_startBlock _
        | apply Resp.bind
        | apply Resp.forIn
        | apply Resp.mapM
        | split))

/-- Decompose a builder program into its steps. -/
macro "resp" : tactic => `(tactic| repeat' (first | with_reducible intro _ | resp_core))

theorem resp_binR (op : BinOp) (a b : Operand) (hint : String) : Resp (binR op a b hint) := by
  unfold binR; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_binR)

theorem resp_needSome {α : Type} (o : Option α) (msg : String) : Resp (needSome o msg) := by
  unfold needSome; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_needSome)

theorem resp_words (t : Ty) : Resp (words t) := by unfold words; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_words)

theorem resp_regOf (t : Ty) : Resp (regOf t) := by unfold regOf; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_regOf)

theorem resp_countsOf (o : Scc.ObjLayout) (t : Ty) : Resp (countsOf o t) := by unfold countsOf; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_countsOf)

theorem resp_header (o : Scc.ObjLayout) (k : Scc.Obj.HeaderKind) (n m : Nat) : Resp (header o k n m) := by
  unfold header; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_header)

theorem resp_evalAt (env : Env) (a : At) : Resp (evalAt env a) := by
  cases a <;> simp only [evalAt, lookupV] <;> resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_evalAt)

theorem resp_one (ws : List Operand) (what : String) : Resp (one ws what) := by unfold one; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_one)

theorem resp_evalOne (env : Env) (a : At) (what : String) : Resp (evalOne env a what) := by
  unfold evalOne; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_evalOne)

theorem resp_inReg (o : Operand) (hint : String) : Resp (inReg o hint) := by unfold inReg; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_inReg)

theorem resp_markWords (t : Ty) (ws : List Operand) : Resp (markWords t ws) := by unfold markWords; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_markWords)

theorem resp_refOf (ws : List Operand) (what : String) : Resp (refOf ws what) := by unfold refOf; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_refOf)

theorem resp_offAdd (a b : Operand) : Resp (offAdd a b) := by unfold offAdd; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_offAdd)

theorem resp_offMul (i : Operand) (c : Nat) : Resp (offMul i c) := by unfold offMul; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_offMul)

theorem resp_cellAddrs (o : Scc.ObjLayout) (base off : Operand) (u : Ty) : Resp (cellAddrs o base off u) := by
  unfold cellAddrs; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_cellAddrs)

theorem resp_loadAt (o : Order) (as : List Addr) (hint : String) : Resp (loadAt o as hint) := by
  unfold loadAt; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_loadAt)

theorem resp_storeAt (o : Order) (as : List Addr) (ws : List Operand) : Resp (storeAt o as ws) := by
  unfold storeAt; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_storeAt)

theorem resp_slotLoc (base off i : Operand) (u : Ty) : Resp (slotLoc base off i u) := by
  unfold slotLoc; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_slotLoc)

theorem resp_mask (w : Wd) (a : Operand) : Resp (mask w a) := by
  unfold mask; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_mask)

theorem resp_sext (w : Wd) (a : Operand) : Resp (sext w a) := by
  unfold sext; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_sext)

theorem resp_fval (sg : Bool) (w : Wd) (a : Operand) : Resp (fval sg w a) := by
  unfold fval; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_fval)

theorem resp_fop (sg : Bool) (w : Wd) (o : FOp) (x y : Operand) : Resp (fop sg w o x y) := by
  unfold fop; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_fop)

theorem resp_fcmp (sg : Bool) (w : Wd) (o : FCmp) (x y : Operand) : Resp (fcmp sg w o x y) := by
  unfold fcmp; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_fcmp)

theorem resp_fop1 (w : Wd) (o : FOp1) (x : Operand) : Resp (fop1 w o x) := by
  unfold fop1; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_fop1)

theorem resp_cvt (src : Ty) (w : Wd) (x : Operand) : Resp (cvt src w x) := by
  unfold cvt; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_cvt)

theorem resp_laneShift (w : Wd) (j : Operand) : Resp (laneShift w j) := by
  unfold laneShift; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_laneShift)

theorem resp_lane (w : Wd) (x j : Operand) : Resp (lane w x j) := by
  unfold lane; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_lane)

theorem resp_setLane (w : Wd) (x j v : Operand) : Resp (setLane w x j v) := by
  unfold setLane; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_setLane)

theorem resp_bitOp (o : BitOp) : Resp (bitOp o) := by
  unfold bitOp; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_bitOp)

theorem resp_callBlock (cx : Scc.Lower.Ctx) (f : String) (args : List Operand) (nres : Nat) :
    Resp (callBlock cx f args nres) := by
  unfold callBlock; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_callBlock)

theorem resp_tcbLayout (o : Scc.ObjLayout) (T : Ty) : Resp (tcbLayout o T) := by
  unfold tcbLayout; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_tcbLayout)

theorem resp_spawn (o : Scc.ObjLayout) (f : String) (T : Ty) (args : List Operand) : Resp (spawn o f T args) := by
  unfold spawn; resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_spawn)

set_option maxHeartbeats 1000000 in
theorem resp_lowerOp (cx : Scc.Lower.Ctx) (env : Env) (x : String) (op : Op) : Resp (lowerOp cx env x op) := by
  cases op <;> simp only [lowerOp] <;> resp
macro_rules | `(tactic| resp_leaf) => `(tactic| apply resp_lowerOp)

theorem resp_lowerExpr (cx : Scc.Lower.Ctx) (ex : Expr) : ∀ env, Resp (lowerExpr cx env ex) := by
  induction ex <;> intro env <;> rw [lowerExpr] <;> (try dsimp only) <;> resp <;>
    first | (exact ‹∀ env, Resp (lowerExpr cx env _)› _) | contradiction | skip


/-! ## An open block stays open

`KC m`: from a state with an open block, a successful run of `m` ends with an
open block. `AKC m`: from any state. `terminate` is the only step that closes
the block; the lowering of an operation reopens one (`startBlock`) after
each `terminate`. -/

/-- From an open block, `m` ends with an open block. -/
def KC {α : Type} (m : B α) : Prop :=
  ∀ s a s', s.cur.isSome = true → m s = .ok (a, s') → s'.cur.isSome = true

/-- From any state, `m` ends with an open block. -/
def AKC {α : Type} (m : B α) : Prop := ∀ s a s', m s = .ok (a, s') → s'.cur.isSome = true

theorem KC.bind {α β : Type} {m : B α} {f : α → B β} (hm : KC m) (hf : ∀ a, KC (f a)) : KC (m >>= f) := by
  intro s b s'' hs h
  rcases hms : m s with e | ⟨a, s'⟩
  · rw [bind_error hms] at h; cases h
  · rw [Scc.Lower.Inv.bind_ok hms] at h; exact hf a s' b s'' (hm s a s' hs hms) h

theorem AKC.bind {α β : Type} {m : B α} {f : α → B β} (hf : ∀ a, AKC (f a)) : AKC (m >>= f) := by
  intro s b s'' h
  rcases hms : m s with e | ⟨a, s'⟩
  · rw [bind_error hms] at h; cases h
  · rw [Scc.Lower.Inv.bind_ok hms] at h; exact hf a s' b s'' h

theorem KC.of_akc {α : Type} {m : B α} (h : AKC m) : KC m := fun s a s' _ hm => h s a s' hm

theorem KC.pure {α : Type} (a : α) : KC (Pure.pure a : B α) := by
  intro s b s' hs h
  have e : (Pure.pure a : B α) s = .ok (a, s) := rfl
  rw [e] at h; cases h; exact hs

theorem KC.throw {α : Type} (e : String) : KC (throw e : B α) := by
  intro s b s' _ h; cases h

theorem KC.get {α : Type} {g : BState → B α} (hg : ∀ s0, KC (g s0)) : KC (get >>= g) :=
  fun s a s' hs h => hg s s a s' hs h

/-- A `terminate` followed by steps that end with an open block. -/
theorem KC.terminate_bind {α : Type} (t : Term) {f : Unit → B α} (hf : ∀ a, AKC (f a)) :
    KC (terminate t >>= f) :=
  KC.of_akc (AKC.bind hf)

theorem kc_keep {α : Type} {m : B α} (a : α) (h : ∀ s, ∃ s', m s = .ok (a, s') ∧ s'.next = s.next ∧
    s'.cur = s.cur) : KC m := by
  intro s b s' hs hm
  obtain ⟨s1, h1, -, h3⟩ := h s
  rw [h1] at hm; cases hm; rw [h3]; exact hs

theorem startBlock_shape (l : Label) (s : BState) :
    ∃ s', startBlock l s = .ok ((), s') ∧ s'.next = s.next ∧ s'.cur.isSome = true := by
  unfold startBlock
  rcases hc : s.cur with _ | ⟨l', is⟩ <;> rcases hh : s.here with _ | p <;>
    simp [hc, hh, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, Except.bind, terminate,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.pure, StateT.pure, pure, markAt]

/-- `startBlock` opens a block, from any state. -/
theorem AKC.startBlock_bind {α : Type} (l : Label) {f : Unit → B α} (hf : ∀ a, KC (f a)) :
    AKC (startBlock l >>= f) := by
  intro s b s'' h
  obtain ⟨s', h1, -, h3⟩ := startBlock_shape l s
  rw [Scc.Lower.Inv.bind_ok h1] at h
  exact hf () s' b s'' h3 h

theorem kc_markAt (n : Node) (p : Point) : KC (markAt n p) := kc_keep () fun _ => ⟨_, rfl, rfl, rfl⟩

theorem kc_setHere (p : Point) : KC (setHere p) := kc_keep () fun _ => ⟨_, rfl, rfl, rfl⟩

theorem kc_markHeap (r : Reg) : KC (markHeap r) :=
  kc_keep () fun s => by
    unfold markHeap; rw [Scc.Lower.Inv.modify_eq]; split <;> exact ⟨_, rfl, rfl, rfl⟩

theorem kc_markScalar (r : Reg) : KC (markScalar r) :=
  kc_keep () fun s => by
    unfold markScalar; rw [Scc.Lower.Inv.modify_eq]; split <;> exact ⟨_, rfl, rfl, rfl⟩

theorem kc_fresh (hint : String) : KC (fresh hint) := by
  intro s a s' hs h; rw [Scc.Lower.Inv.fresh_eq] at h; cases h; exact hs

theorem kc_freshLabel (hint : String) : KC (freshLabel hint) := by
  intro s a s' hs h; rw [Scc.Lower.Inv.freshLabel_eq] at h; cases h; exact hs

theorem kc_emit (i : Inst) : KC (emit i) := by
  intro s a s' _ h
  obtain ⟨s1, h1, -, h3⟩ := emit_shape i s
  rw [h1] at h; cases h; exact h3

theorem kc_startBlock (l : Label) : KC (startBlock l) := by
  intro s a s' _ h
  obtain ⟨s1, h1, -, h3⟩ := startBlock_shape l s
  rw [h1] at h; cases h; exact h3

theorem KC.forIn {α β : Type} (xs : List α) (b : β) {f : α → β → B (ForInStep β)}
    (hf : ∀ a b, KC (f a b)) : KC (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact KC.pure b
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine KC.bind (hf x b) fun r => ?_
    cases r with
    | done b' => exact KC.pure b'
    | yield b' => exact ih b'

theorem KC.mapM {α β : Type} (xs : List α) {f : α → B β} (hf : ∀ a, KC (f a)) : KC (xs.mapM f) := by
  induction xs with
  | nil => exact KC.pure []
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact KC.bind (hf x) fun a => KC.bind ih fun as => KC.pure _

/-- The steps proved `KC` so far (extended after each lemma). -/
syntax "kc_leaf" : tactic
macro_rules | `(tactic| kc_leaf) => `(tactic| fail "no leaf")

syntax "kc_core" : tactic
macro_rules
  | `(tactic| kc_core) => `(tactic| first
      | with_reducible apply KC.terminate_bind
      | with_reducible apply AKC.startBlock_bind
      | with_reducible apply KC.get
      | with_reducible (first
        | kc_leaf
        | exact KC.pure _
        | exact KC.throw _
        | exact kc_markAt _ _
        | exact kc_setHere _
        | exact kc_markHeap _
        | exact kc_markScalar _
        | exact kc_fresh _
        | exact kc_freshLabel _
        | exact kc_emit _
        | exact kc_startBlock _
        | apply KC.bind
        | apply KC.forIn
        | apply KC.mapM
        | split))

/-- Decompose a builder program into its steps, for `KC`. -/
macro "kc" : tactic => `(tactic| repeat' (first | with_reducible intro _ | kc_core))

theorem kc_binR (op : BinOp) (a b : Operand) (hint : String) : KC (binR op a b hint) := by
  unfold binR; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_binR)

theorem kc_needSome {α : Type} (o : Option α) (msg : String) : KC (needSome o msg) := by
  unfold needSome; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_needSome)

theorem kc_words (t : Ty) : KC (words t) := by unfold words; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_words)

theorem kc_regOf (t : Ty) : KC (regOf t) := by unfold regOf; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_regOf)

theorem kc_countsOf (o : Scc.ObjLayout) (t : Ty) : KC (countsOf o t) := by unfold countsOf; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_countsOf)

theorem kc_header (o : Scc.ObjLayout) (k : Scc.Obj.HeaderKind) (n m : Nat) : KC (header o k n m) := by
  unfold header; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_header)

theorem kc_evalAt (env : Env) (a : At) : KC (evalAt env a) := by
  cases a <;> simp only [evalAt, lookupV] <;> kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_evalAt)

theorem kc_one (ws : List Operand) (what : String) : KC (one ws what) := by unfold one; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_one)

theorem kc_evalOne (env : Env) (a : At) (what : String) : KC (evalOne env a what) := by
  unfold evalOne; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_evalOne)

theorem kc_inReg (o : Operand) (hint : String) : KC (inReg o hint) := by unfold inReg; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_inReg)

theorem kc_markWords (t : Ty) (ws : List Operand) : KC (markWords t ws) := by unfold markWords; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_markWords)

theorem kc_refOf (ws : List Operand) (what : String) : KC (refOf ws what) := by unfold refOf; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_refOf)

theorem kc_offAdd (a b : Operand) : KC (offAdd a b) := by unfold offAdd; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_offAdd)

theorem kc_offMul (i : Operand) (c : Nat) : KC (offMul i c) := by unfold offMul; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_offMul)

theorem kc_cellAddrs (o : Scc.ObjLayout) (base off : Operand) (u : Ty) : KC (cellAddrs o base off u) := by
  unfold cellAddrs; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_cellAddrs)

theorem kc_loadAt (o : Order) (as : List Addr) (hint : String) : KC (loadAt o as hint) := by
  unfold loadAt; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_loadAt)

theorem kc_storeAt (o : Order) (as : List Addr) (ws : List Operand) : KC (storeAt o as ws) := by
  unfold storeAt; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_storeAt)

theorem kc_slotLoc (base off i : Operand) (u : Ty) : KC (slotLoc base off i u) := by
  unfold slotLoc; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_slotLoc)

theorem kc_mask (w : Wd) (a : Operand) : KC (mask w a) := by
  unfold mask; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_mask)

theorem kc_sext (w : Wd) (a : Operand) : KC (sext w a) := by
  unfold sext; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_sext)

theorem kc_fval (sg : Bool) (w : Wd) (a : Operand) : KC (fval sg w a) := by
  unfold fval; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_fval)

theorem kc_fop (sg : Bool) (w : Wd) (o : FOp) (x y : Operand) : KC (fop sg w o x y) := by
  unfold fop; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_fop)

theorem kc_fcmp (sg : Bool) (w : Wd) (o : FCmp) (x y : Operand) : KC (fcmp sg w o x y) := by
  unfold fcmp; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_fcmp)

theorem kc_fop1 (w : Wd) (o : FOp1) (x : Operand) : KC (fop1 w o x) := by
  unfold fop1; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_fop1)

theorem kc_cvt (src : Ty) (w : Wd) (x : Operand) : KC (cvt src w x) := by
  unfold cvt; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_cvt)

theorem kc_laneShift (w : Wd) (j : Operand) : KC (laneShift w j) := by
  unfold laneShift; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_laneShift)

theorem kc_lane (w : Wd) (x j : Operand) : KC (lane w x j) := by
  unfold lane; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_lane)

theorem kc_setLane (w : Wd) (x j v : Operand) : KC (setLane w x j v) := by
  unfold setLane; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_setLane)

theorem kc_bitOp (o : BitOp) : KC (bitOp o) := by
  unfold bitOp; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_bitOp)

theorem kc_callBlock (cx : Scc.Lower.Ctx) (f : String) (args : List Operand) (nres : Nat) :
    KC (callBlock cx f args nres) := by
  unfold callBlock; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_callBlock)

theorem kc_tcbLayout (o : Scc.ObjLayout) (T : Ty) : KC (tcbLayout o T) := by
  unfold tcbLayout; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_tcbLayout)

theorem kc_spawn (o : Scc.ObjLayout) (f : String) (T : Ty) (args : List Operand) : KC (spawn o f T args) := by
  unfold spawn; kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_spawn)

theorem kc_lowerOp (cx : Scc.Lower.Ctx) (env : Env) (x : String) (op : Op) : KC (lowerOp cx env x op) := by
  cases op <;> simp only [lowerOp] <;> kc
macro_rules | `(tactic| kc_leaf) => `(tactic| apply kc_lowerOp)


/-! ## The prefixes -/

theorem resp_letStep (cx : Scc.Lower.Ctx) (env : Env) (x : String) (op : Op) (e : Expr) :
    Resp (letStep cx env x op e) := by
  unfold letStep; resp

theorem resp_splitStep (env : Env) (a : At) : Resp (splitStep env a) := by
  unfold splitStep; resp

theorem resp_ifStep (env : Env) (a b : At) : Resp (ifStep env a b) := by
  unfold ifStep; resp

theorem kc_letStep (cx : Scc.Lower.Ctx) (env : Env) (x : String) (op : Op) (e : Expr) :
    KC (letStep cx env x op e) := by
  unfold letStep; kc

theorem kc_splitStep (env : Env) (a : At) : KC (splitStep env a) := by
  unfold splitStep; kc

theorem kc_ifStep (env : Env) (a b : At) : KC (ifStep env a b) := by
  unfold ifStep; kc

/-! ## `runB` from any state with an open block -/

/-- **`runB` agrees with a run from any state with an open block**: both
fail, or both succeed with the same result and counter. -/
theorem runB_congr {α : Type} {m : B α} (hm : Resp m) {s : BState} (hc : s.cur.isSome = true) :
    ResRel (m s) (m { next := s.next }) :=
  hm _ _ ⟨rfl, hc.trans rfl⟩

/-- A run from a state with an open block succeeds iff `runB` does, with the
same result and counter. -/
theorem runB_some_iff {α : Type} {m : B α} (hm : Resp m) {s : BState} (hc : s.cur.isSome = true)
    {a : α} {n' : Nat} : runB m s.next = some (a, n') ↔ ∃ s', m s = .ok (a, s') ∧ s'.next = n' := by
  have r := runB_congr hm hc
  unfold runB
  rcases hs : m s with e | ⟨b, s'⟩ <;> rcases ht : m { next := s.next } with e' | ⟨b', t'⟩ <;>
    rw [hs, ht] at r <;> simp only [ResRel] at r
  · simp
  · obtain ⟨rfl, h1, -⟩ := r
    constructor
    · intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s', rfl, h1⟩
    · rintro ⟨s1, h, rfl⟩
      cases h
      simp only [h1]

/-- A run from a state with an open block fails iff `runB` does. -/
theorem runB_none_iff {α : Type} {m : B α} (hm : Resp m) {s : BState} (hc : s.cur.isSome = true) :
    runB m s.next = none ↔ ∃ e, m s = .error e := by
  have r := runB_congr hm hc
  unfold runB
  rcases hs : m s with e | ⟨b, s'⟩ <;> rcases ht : m { next := s.next } with e' | ⟨b', t'⟩ <;>
    rw [hs, ht] at r <;> simp only [ResRel] at r <;> simp

/-- `runB_some_iff` for a step that keeps the block open (`KC`). -/
theorem runB_some_iff_kc {α : Type} {m : B α} (hm : Resp m) (hk : KC m) {s : BState}
    (hc : s.cur.isSome = true) {a : α} {n' : Nat} :
    runB m s.next = some (a, n') ↔ ∃ s', m s = .ok (a, s') ∧ s'.next = n' ∧ s'.cur.isSome = true := by
  rw [runB_some_iff hm hc]
  constructor
  · rintro ⟨s', h1, h2⟩; exact ⟨s', h1, h2, hk s a s' hc h1⟩
  · rintro ⟨s', h1, h2, -⟩; exact ⟨s', h1, h2⟩

end Congr

end Spike.Lib.LowerNode
