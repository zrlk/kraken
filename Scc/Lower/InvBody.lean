import Scc.Lower.Inv

/-!
# The lowering of an `Accepted0` body, one `let` at a time

`Scc/Lower/Inv.lean` gives the closed form `lower0` of an `Accepted0` body
and its whole-body invariants. A proof that runs over the body one `let` at
a time (the code of each construct, then the rest) needs them per step: what
one step of `lower0` produced, and an invariant of the environment that the
step keeps. This module gives them, independent of the target:

* `lower0_atom_inv`, `lower0_add_inv`, `lower0_ret_inv`: one step of the
  closed form: a `let` of an atom emits nothing and binds the atom's word, a
  `let` of `a + b` emits `addChk (regName x n) p q` before the rest, `ret a`
  emits nothing and returns `a`'s words;
* `EnvBelow env n`: every register among the environment's words is a name
  `fresh` gave below counter `n`, so the name it gives at `n` is new
  (`envBelow_fresh`, `envBelow_fresh'`; `envBelow_fresh_ge`: nor any it gives later);
* `BodyInv S n env`: `EnvBelow env n`, and every register among the
  environment's words is in `S` (for a target, the registers that have a
  frame slot); `bodyInv_init` at the start of a code block,
  `bodyInv_atom`, `bodyInv_add`, `bodyInv_ret`: each step keeps it, given
  that the registers the body writes are in `S`, and the registers the step
  reads and writes are in `S`;
* `lower0_ret_singleton`, `accepted0_ret_singleton`: the `ret` returns one
  word (the body's `ret` is of one atom, `body0`);
* `lower0_insts_addChk`, `lower0_next`: the instructions are all `addChk`,
  one per counter step; `lower0_uses_defs`: from the start of a code block
  every register an instruction or the `ret` reads is one an instruction
  writes.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.Inv

open StackMap (instUses instDefs termUses opRegs)

/-! ## One step of the closed form -/

theorem lower0_atom_inv {env : Env} {n : Nat} {x : String} {a : At} {e : Expr} {r : Res}
    (hr : lower0 env n (.let_ x (.atom a) e) = some r) :
    ∃ t w r', atomV env a = some (t, [w]) ∧ scalar1 t = true ∧
      lower0 ((x, t, [w]) :: env) n e = some r' ∧
      r = { r' with marked := regsOf [w] ++ r'.marked } := by
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
      cases ht : scalar1 t <;> simp [ht, hr'] at hr
      exact ⟨t, w, r', rfl, ht, hr', hr.symm⟩

theorem lower0_add_inv {env : Env} {n : Nat} {x : String} {a b : At} {e : Expr} {r : Res}
    (hr : lower0 env n (.let_ x (.add a b) e) = some r) :
    ∃ tp p tq q r', atomV env a = some (tp, [p]) ∧ atomV env b = some (tq, [q]) ∧
      lower0 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e = some r' ∧
      r = { r' with insts := .addChk (regName x n) p q :: r'.insts,
                    marked := regName x n :: r'.marked } := by
  simp only [lower0] at hr
  cases ha : atomV env a with
  | none => simp [ha] at hr
  | some v =>
    obtain ⟨tp, ws⟩ := v
    rw [ha] at hr
    match ws, hr with
    | [p], hr =>
    cases hb : atomV env b with
    | none => simp [hb] at hr
    | some u =>
      obtain ⟨tq, us⟩ := u
      rw [hb] at hr
      match us, hr with
      | [q], hr =>
      cases hr' : lower0 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e with
      | none => simp [hr'] at hr
      | some r' =>
        simp [hr'] at hr
        exact ⟨tp, p, tq, q, r', rfl, rfl, rfl, hr.symm⟩

theorem lower0_ret_inv {env : Env} {n : Nat} {a : At} {r : Res}
    (hr : lower0 env n (.ret a) = some r) :
    ∃ t, atomV env a = some (t, r.ret) ∧ r.insts = [] ∧ r.next = n := by
  simp only [lower0] at hr
  cases ha : atomV env a with
  | none => simp [ha] at hr
  | some v =>
    obtain ⟨t, ws⟩ := v
    simp [ha] at hr
    subst hr
    exact ⟨t, rfl, rfl, rfl⟩

/-- **The closed form returns one word** on an `Accepted0` body (`body0`)
whose free variables are bound to scalar words: its `ret`'s atom is one. -/
theorem lower0_ret_singleton :
    ∀ (e : Expr) (scope : List String) (env : Env) (n : Nat) {r : Res}, body0 scope e = true →
      EnvScalar scope env → lower0 env n e = some r → ∃ w, r.ret = [w] := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n r hb h hr
    cases op with
    | atom a =>
      simp only [body0, Bool.and_eq_true] at hb
      obtain ⟨t, w, r', -, ht, hr', rfl⟩ := lower0_atom_inv hr
      exact ih (x :: scope) _ n (r := r') hb.2 (envScalar_cons h x w ht) hr'
    | add a b =>
      simp only [body0, Bool.and_eq_true] at hb
      obtain ⟨-, -, -, -, r', -, -, hr', rfl⟩ := lower0_add_inv hr
      exact ih (x :: scope) _ (n + 1) (r := r') hb.2 (envScalar_cons h x _ rfl) hr'
    | _ => simp [body0] at hb
  | ret a =>
    intro scope env n r hb h hr
    obtain ⟨t, w, ha, -⟩ := atomV_of_atom0 (by simpa [body0] using hb) h
    obtain ⟨t', ha', -, -⟩ := lower0_ret_inv hr
    rw [ha] at ha'
    exact ⟨w, (Prod.mk.inj (Option.some.inj ha')).2.symm⟩
  | _ => intro scope env n r hb; simp [body0] at hb

/-- **An `Accepted0` program's `main` returns one word**: `lower0` of its
body, from its `Unit` argument, at any counter. -/
theorem accepted0_ret_singleton {d : Decl} (hd : Accepted0 [d] = true) {n : Nat} {r : Res}
    (hr : lower0 [(d.arg, .unit, [])] n d.body = some r) : ∃ w, r.ret = [w] := by
  simp only [Accepted0, Bool.and_eq_true] at hd
  exact lower0_ret_singleton d.body [] _ n hd.1.2 (envScalar_nil _) hr

/-- The closed form is one of the three steps. -/
theorem lower0_cases {env : Env} {n : Nat} {e : Expr} {r : Res} (hr : lower0 env n e = some r) :
    (∃ x a e', e = .let_ x (.atom a) e') ∨ (∃ x a b e', e = .let_ x (.add a b) e') ∨
      ∃ a, e = .ret a := by
  cases e with
  | let_ x op e' =>
    cases op with
    | atom a => exact .inl ⟨x, a, e', rfl⟩
    | add a b => exact .inr (.inl ⟨x, a, b, e', rfl⟩)
    | _ => simp [lower0] at hr
  | ret a => exact .inr (.inr ⟨a, rfl⟩)
  | _ => simp [lower0] at hr

/-! ## The registers of an atom -/

/-- The registers among an atom's words are among the environment's. -/
theorem atomV_regs_env {env : Env} {a : At} {t : Ty} {ws : List Operand}
    (h : atomV env a = some (t, ws)) :
    ∀ y ∈ ws.flatMap opRegs, ∃ v ∈ env, y ∈ v.2.2.flatMap opRegs := by
  cases a with
  | var z =>
    simp only [atomV, Option.map_eq_some_iff] at h
    obtain ⟨⟨z', u, vs⟩, hf, hv⟩ := h
    cases hv
    exact fun y hy => ⟨_, List.mem_of_find?_eq_some hf, hy⟩
  | lit k =>
    simp only [atomV] at h
    split at h
    · cases h
    · cases h; simp [opRegs, imm]
  | unit => simp only [atomV, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp

/-! ## Fresh names -/

/-- **Every register of the environment is a name `fresh` gave below `n`.** -/
def EnvBelow (env : Env) (n : Nat) : Prop :=
  ∀ v ∈ env, ∀ y ∈ v.2.2.flatMap opRegs, ∃ z k, k < n ∧ y = regName z k

/-- The environment at the start of a code block (the parameter, `Unit`,
no word). -/
theorem envBelow_init (arg : String) (n : Nat) : EnvBelow [(arg, .unit, [])] n := by
  intro v hv y hy
  simp only [List.mem_singleton] at hv
  subst hv
  simp at hy

theorem envBelow_mono {env : Env} {n m : Nat} (h : EnvBelow env n) (hle : n ≤ m) :
    EnvBelow env m := by
  intro v hv y hy
  obtain ⟨z, k, hk, rfl⟩ := h v hv y hy
  exact ⟨z, k, by omega, rfl⟩

/-- **The name `fresh` gives at `n` is new.** -/
theorem envBelow_fresh {env : Env} {n : Nat} (h : EnvBelow env n) (x : String) :
    ∀ v ∈ env, ∀ y ∈ v.2.2.flatMap opRegs, y ≠ regName x n := by
  intro v hv y hy he
  obtain ⟨z, k, hk, rfl⟩ := h v hv y hy
  exact regName_ne (show k ≠ n by omega) he

/-- `envBelow_fresh`, by operands. -/
theorem envBelow_fresh' {env : Env} {n : Nat} (h : EnvBelow env n) (x : String) :
    ∀ v ∈ env, ∀ o ∈ v.2.2, ∀ y, o = .reg y → y ≠ regName x n := by
  intro v hv o ho y hoy
  subst hoy
  exact envBelow_fresh h x v hv y (List.mem_flatMap.mpr ⟨_, ho, by simp [opRegs]⟩)

/-- `envBelow_fresh`, for every counter from `n` on. -/
theorem envBelow_fresh_ge {env : Env} {n : Nat} (h : EnvBelow env n) :
    ∀ v ∈ env, ∀ o ∈ v.2.2, ∀ y, o = .reg y → ∀ (x : String) (k : Nat), n ≤ k → y ≠ regName x k :=
  fun v hv o ho y hoy x k hk => envBelow_fresh' (envBelow_mono h hk) x v hv o ho y hoy

theorem envBelow_atom {env : Env} {n : Nat} {a : At} {t : Ty} {ws : List Operand}
    (h : EnvBelow env n) (ha : atomV env a = some (t, ws)) :
    ∀ y ∈ ws.flatMap opRegs, ∃ z k, k < n ∧ y = regName z k := by
  intro y hy
  obtain ⟨v, hv, hy'⟩ := atomV_regs_env ha y hy
  exact h v hv y hy'

theorem envBelow_cons {env : Env} {n : Nat} (h : EnvBelow env n) (x : String) (t : Ty)
    {ws : List Operand} (hw : ∀ y ∈ ws.flatMap opRegs, ∃ z k, k < n ∧ y = regName z k) :
    EnvBelow ((x, t, ws) :: env) n := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hw
  · exact h v hv

/-! ## The invariant of a step -/

/-- **The invariant of the environment between steps**: its registers are
names `fresh` gave below `n`, and are in `S`. -/
def BodyInv (S : List Reg) (n : Nat) (env : Env) : Prop :=
  EnvBelow env n ∧ EnvIn env S

theorem bodyInv_init (S : List Reg) (arg : String) : BodyInv S 0 [(arg, .unit, [])] :=
  ⟨envBelow_init arg 0, by intro v hv; simp at hv; subst hv; simp⟩

/-- **A `let` of an atom**: no instruction, the atom's word bound; its
registers are in `S`, and the invariant holds after. -/
theorem bodyInv_atom {S : List Reg} {n : Nat} {env : Env} {x : String} {a : At} {e : Expr}
    {r : Res} (hI : BodyInv S n env) (hr : lower0 env n (.let_ x (.atom a) e) = some r) :
    ∃ t w r', atomV env a = some (t, [w]) ∧ scalar1 t = true ∧
      lower0 ((x, t, [w]) :: env) n e = some r' ∧
      r'.insts = r.insts ∧ r'.ret = r.ret ∧ r'.next = r.next ∧
      (∀ y ∈ opRegs w, y ∈ S) ∧ BodyInv S n ((x, t, [w]) :: env) := by
  obtain ⟨t, w, r', ha, ht, hr', rfl⟩ := lower0_atom_inv hr
  have hw := atomV_regs ha hI.2
  refine ⟨t, w, r', ha, ht, hr', rfl, rfl, rfl, by simpa using hw, ?_, envIn_cons hI.2 x t hw⟩
  exact envBelow_cons hI.1 x t (envBelow_atom hI.1 ha)

/-- **A `let` of `a + b`**: the instruction `addChk d p q` with
`d = regName x n` a register not in the environment; the registers it
reads and writes are in `S` (given that the body's written registers are),
and the invariant holds after, at counter `n + 1`. -/
theorem bodyInv_add {S : List Reg} {n : Nat} {env : Env} {x : String} {a b : At} {e : Expr}
    {r : Res} (hI : BodyInv S n env) (hS : ∀ d ∈ defsOf r.insts, d ∈ S)
    (hr : lower0 env n (.let_ x (.add a b) e) = some r) :
    ∃ tp p tq q r', atomV env a = some (tp, [p]) ∧ atomV env b = some (tq, [q]) ∧
      lower0 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e = some r' ∧
      r.insts = .addChk (regName x n) p q :: r'.insts ∧ r'.ret = r.ret ∧ r'.next = r.next ∧
      (∀ y ∈ opRegs p, y ∈ S) ∧ (∀ y ∈ opRegs q, y ∈ S) ∧ regName x n ∈ S ∧
      (∀ v ∈ env, ∀ y ∈ v.2.2.flatMap opRegs, y ≠ regName x n) ∧
      (∀ d ∈ defsOf r'.insts, d ∈ S) ∧
      BodyInv S (n + 1) ((x, .int, [.reg (regName x n)]) :: env) := by
  obtain ⟨tp, p, tq, q, r', ha, hb, hr', rfl⟩ := lower0_add_inv hr
  have hd : regName x n ∈ S := hS _ (by simp [defsOf, instDefs])
  refine ⟨tp, p, tq, q, r', ha, hb, hr', rfl, rfl, rfl,
    by simpa using atomV_regs ha hI.2, by simpa using atomV_regs hb hI.2, hd,
    envBelow_fresh hI.1 x, fun d h => hS d (by simp [defsOf, instDefs] at h ⊢; exact .inr h),
    ?_, envIn_cons hI.2 x .int (by simpa [opRegs] using hd)⟩
  refine envBelow_cons (envBelow_mono hI.1 (Nat.le_succ n)) x .int ?_
  intro y hy
  simp only [List.flatMap_cons, opRegs, List.flatMap_nil, List.append_nil,
    List.mem_singleton] at hy
  exact ⟨x, n, by omega, hy⟩

/-- **`ret a`**: no instruction; the registers it returns are in `S`. -/
theorem bodyInv_ret {S : List Reg} {n : Nat} {env : Env} {a : At} {r : Res}
    (hI : BodyInv S n env) (hr : lower0 env n (.ret a) = some r) :
    ∃ t, atomV env a = some (t, r.ret) ∧ r.insts = [] ∧ r.next = n ∧
      ∀ y ∈ r.ret.flatMap opRegs, y ∈ S := by
  obtain ⟨t, ha, hi, hn⟩ := lower0_ret_inv hr
  exact ⟨t, ha, hi, hn, atomV_regs ha hI.2⟩

/-! ## The whole body -/

/-- **The instructions are all `addChk`**, one per counter step. -/
theorem lower0_insts_addChk :
    ∀ (e : Expr) (env : Env) (n : Nat) (r : Res), lower0 env n e = some r →
      (∀ i ∈ r.insts, ∃ d p q, i = .addChk d p q) ∧ r.next = n + r.insts.length := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r hr
    cases op with
    | atom a =>
      obtain ⟨t, w, r', -, -, hr', rfl⟩ := lower0_atom_inv hr
      exact ih _ n r' hr'
    | add a b =>
      obtain ⟨tp, p, tq, q, r', -, -, hr', rfl⟩ := lower0_add_inv hr
      obtain ⟨h1, h2⟩ := ih _ (n + 1) r' hr'
      refine ⟨?_, by simp only [List.length_cons]; omega⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ⟨_, p, q, rfl⟩
      · exact h1 i hi
    | _ => simp [lower0] at hr
  | ret a =>
    intro env n r hr
    obtain ⟨t, -, hi, hn⟩ := lower0_ret_inv hr
    simp [hi, hn]
  | _ => intro env n r hr; simp [lower0] at hr

/-- **The counter advances by the body's checked `+`s** (`adds0`). -/
theorem lower0_next_adds :
    ∀ (e : Expr) (env : Env) (n : Nat) (r : Res), lower0 env n e = some r → r.next = n + adds0 e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r hr
    cases op with
    | atom a =>
      obtain ⟨t, w, r', -, -, hr', rfl⟩ := lower0_atom_inv hr
      simpa [adds0] using ih _ n r' hr'
    | add a b =>
      obtain ⟨tp, p, tq, q, r', -, -, hr', rfl⟩ := lower0_add_inv hr
      have := ih _ (n + 1) r' hr'
      simp only [adds0]; omega
    | _ => simp [lower0] at hr
  | ret a =>
    intro env n r hr
    obtain ⟨t, -, -, hn⟩ := lower0_ret_inv hr
    simp [hn, adds0]
  | _ => intro env n r hr; simp [lower0] at hr

/-- The registers an `addChk`-only list writes, one per instruction. -/
theorem defsOf_length_addChk : ∀ (is : List Inst), (∀ i ∈ is, ∃ d p q, i = .addChk d p q) →
    (defsOf is).length = is.length
  | [], _ => rfl
  | i :: is, h => by
    obtain ⟨d, p, q, rfl⟩ := h i (by simp)
    have ih := defsOf_length_addChk is fun j hj => h j (by simp [hj])
    simp only [defsOf, List.flatMap_cons, instDefs, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

/-- What `DefBefore` says of each read register: in `ds`, or written by an
instruction of the list. -/
theorem defBefore_mem : ∀ {ds : List Reg} {is : List Inst} {t : Term}, DefBefore ds is t →
    (∀ i ∈ is, ∀ x ∈ instUses i, x ∈ ds ∨ x ∈ defsOf is) ∧
      ∀ x ∈ termUses t, x ∈ ds ∨ x ∈ defsOf is
  | ds, [], t, h => ⟨by simp, fun x hx => .inl (h x hx)⟩
  | ds, i :: is, t, ⟨hi, hrest⟩ => by
    obtain ⟨h1, h2⟩ := defBefore_mem hrest
    have lift : ∀ x, x ∈ instDefs i ++ ds ∨ x ∈ defsOf is → x ∈ ds ∨ x ∈ defsOf (i :: is) := by
      intro x hx
      simp only [defsOf, List.flatMap_cons, List.mem_append] at hx ⊢
      rcases hx with (h | h) | h
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)
    refine ⟨?_, fun x hx => lift x (h2 x hx)⟩
    intro j hj x hx
    rcases List.mem_cons.mp hj with rfl | hj
    · exact .inl (hi x hx)
    · exact lift x (h1 j hj x hx)

/-- **From the start of a code block, every register read is written by an
instruction of the body.** -/
theorem lower0_uses_defs {arg : String} {e : Expr} {r : Res}
    (hr : lower0 [(arg, .unit, [])] 0 e = some r) :
    (∀ i ∈ r.insts, ∀ x ∈ instUses i, x ∈ defsOf r.insts) ∧
      ∀ x ∈ r.ret.flatMap opRegs, x ∈ defsOf r.insts := by
  have hd := reads_defined _ _ 0 [] r hr (by intro v hv; simp at hv; subst hv; simp)
  obtain ⟨h1, h2⟩ := defBefore_mem hd
  refine ⟨fun i hi x hx => ?_, fun x hx => ?_⟩
  · rcases h1 i hi x hx with h | h
    · cases h
    · exact h
  · rcases h2 x hx with h | h
    · cases h
    · exact h

end Scc.Lower.Inv
