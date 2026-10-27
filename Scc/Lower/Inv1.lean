import Scc.Lower.Inv
import Scc.Lower.Spec1

/-!
# The lowering of `Accepted1` bodies without calls: closed form

`Scc/Lower/Inv.lean` gives the term lowering `lowerExpr` in closed form on
`Accepted0` bodies (`lower0`: one block). This module does the same for the
call-free part of `Accepted1` (`Scc/Lower/Spec1.lean`): `let`s of an atom, a
checked `+` or a saturating `-`, the integer `if` and `ret`. An `if` closes the
open block with a `br` and lowers its branches into two fresh blocks
`then{n}` and `else{n+1}`, so the result is a list of blocks:

* `lower1 env n e`: what lowering `e` in environment `env` from fresh-name
  counter `n` produces (`Res1`): the instructions appended to the open block
  and its terminator, the blocks after it, the final counter, the registers
  marked scalar, the placement marks recorded and the source point at the end;
* `lowerExpr_lower1`: from a state whose open block is `(l, is)` and whose
  source point is set, `lowerExpr` closes `l` with `is`, `lower1`'s
  instructions and terminator, pushes `lower1`'s blocks, and changes nothing
  else but the counter, the scalar registers, the marks and the source point;
* `lower1_isSome`: on a call-free `Accepted1` body (`body1 []`) it succeeds.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.Inv

/-! ## Builder steps -/

/-- What `markAt` does to the trace. -/
def markOp (ms : Array (Node × Point)) (m : Node × Point) : Array (Node × Point) :=
  (ms.toList.filter (·.1 != m.1)).toArray.push m

theorem markAt_eq (n : Node) (p : Point) (s : BState) :
    markAt n p s = .ok ((), { s with marks := markOp s.marks (n, p) }) := rfl

theorem startBlock_eq (l : Label) {s : BState} {p : Point} (hc : s.cur = none)
    (hh : s.here = some p) :
    startBlock l s = .ok ((), { s with cur := some (l, #[]), marks := markOp s.marks (.block l, p) }) := by
  unfold startBlock
  simp [hc, hh, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure, markAt_eq, Except.bind]

/-- The label `freshLabel hint` gives at counter `n`. -/
def labName (hint : String) (n : Nat) : Label := s!"{hint}{n}"

theorem freshLabel_eq (hint : String) (s : BState) :
    freshLabel hint s = .ok (labName hint s.next, { s with next := s.next + 1 }) := rfl

theorem emit_subSat {d : Reg} {p q : Operand} {s : BState} {l : Label}
    {is : Array Inst} (hc : s.cur = some (l, is)) :
    emit (.subSat d p q) s = .ok ((), { s with cur := some (l, is.push (.subSat d p q)) }) := by
  unfold emit
  rw [bind_ok (modify_eq _ _)]
  simp only [hc]
  rfl

theorem lowerOp_sub (cx : Ctx) (env : Env) (x : String) {a b : At} {t t' : Ty} {p q : Operand}
    (ha : atomV env a = some (t, [p])) (hb : atomV env b = some (t', [q])) {s : BState} {l : Label}
    {is : Array Inst} (hc : s.cur = some (l, is)) :
    lowerOp cx env x (.sub a b) s = .ok ((.int, [.reg (regName x s.next)]),
      { s with next := s.next + 1, cur := some (l, is.push (.subSat (regName x s.next) p q)) }) := by
  simp only [lowerOp]
  rw [bind_ok (evalOne_eq ha _ _), bind_ok (evalOne_eq hb _ _), bind_ok (fresh_eq _ _),
    bind_ok (emit_subSat (s := { s with next := s.next + 1 }) hc)]
  rfl

/-! ## The closed form -/

/-- **What lowering a call-free `Accepted1` body produces** (`lower1`). -/
structure Res1 where
  /-- The instructions appended to the open block. -/
  insts : List Inst
  /-- The open block's terminator. -/
  term : Term
  /-- The blocks after the open one, in order. -/
  blocks : List Block
  /-- The fresh-name counter at the end. -/
  next : Nat
  /-- The registers marked scalar (`markScalar`), in order. -/
  marked : List Reg
  /-- The placement marks recorded (`markAt`), in order. -/
  marks : List (Node × Point)
  /-- The source point at the end (the last `ret`). -/
  here : Point

/-- **The closed form of `lowerExpr` on a call-free `Accepted1` body**, in
environment `env` from counter `n`: as `lower0` for `let`s of an atom and
`+`; a `let` of `a - b` emits `subSat d a b` into `d = regName x n`; `if a = b`
closes the open block with `br .eq a b (then{n}) (else{n+1})`, then the
`then` branch's blocks from counter `n + 2` start with `then{n}`, the `else`
branch's blocks with `else{n+1}`. `none` off the fragment, or where an atom
has no scalar word.

The marks are `markAt`'s calls in order, so a node can occur twice: an `if`
records `.block ly` at the `if` (`startBlock`) and then at the branch, and
`markOp` keeps only the last mark of a node. -/
def lower1 (env : Env) (n : Nat) : Expr → Option Res1
  | .let_ x (.atom a) e => do
      let (t, ws) ← atomV env a
      let w ← match ws with | [w] => some w | _ => none
      if scalar1 t then
        let r ← lower1 ((x, t, ws) :: env) n e
        pure { r with marked := regsOf [w] ++ r.marked }
      else none
  | .let_ x (.add a b) e => do
      let (_, ws) ← atomV env a
      let p ← match ws with | [p] => some p | _ => none
      let (_, us) ← atomV env b
      let q ← match us with | [q] => some q | _ => none
      let d := regName x n
      let r ← lower1 ((x, .int, [.reg d]) :: env) (n + 1) e
      pure { r with insts := .addChk d p q :: r.insts, marked := d :: r.marked }
  | .let_ x (.sub a b) e => do
      let (_, ws) ← atomV env a
      let p ← match ws with | [p] => some p | _ => none
      let (_, us) ← atomV env b
      let q ← match us with | [q] => some q | _ => none
      let d := regName x n
      let r ← lower1 ((x, .int, [.reg d]) :: env) (n + 1) e
      pure { r with insts := .subSat d p q :: r.insts, marked := d :: r.marked }
  | .ifeq a b yes no => do
      let (_, ws) ← atomV env a
      let p ← match ws with | [p] => some p | _ => none
      let (_, us) ← atomV env b
      let q ← match us with | [q] => some q | _ => none
      let ly := labName "then" n
      let ln := labName "else" (n + 1)
      let ry ← lower1 env (n + 2) yes
      let rn ← lower1 env ry.next no
      pure { insts := [], term := .br .eq p q ly ln,
             blocks := ⟨ly, ry.insts, ry.term⟩ :: ry.blocks ++ ⟨ln, rn.insts, rn.term⟩ :: rn.blocks,
             next := rn.next, marked := ry.marked ++ rn.marked,
             marks := [(.block ly, (env, .ifeq a b yes no)), (.block ly, (env, yes))] ++ ry.marks ++
               [(.block ln, ry.here), (.block ln, (env, no))] ++ rn.marks,
             here := rn.here }
  | .ret a => do
      let (_, ws) ← atomV env a
      pure { insts := [], term := .ret ws, blocks := [], next := n, marked := [], marks := [],
             here := (env, .ret a) }
  | _ => none

/-! ## `lowerExpr` is the closed form -/

/-- **`lowerExpr` on a call-free `Accepted1` body is `lower1`**: from a state
whose open block is `(l, is)`, it closes `l` with `is` and `lower1`'s
instructions and terminator, pushes `lower1`'s blocks, and records
`lower1`'s marks. No hypothesis on `s.here`: every case sets it (`setHere`)
before it is read. -/
theorem lowerExpr_lower1 (cx : Ctx) :
    ∀ (e : Expr) (env : Env) (s : BState) (l : Label) (is : Array Inst) (r : Res1),
      s.cur = some (l, is) → lower1 env s.next e = some r →
      lowerExpr cx env e s = .ok ((), { s with
        blocks := (s.blocks.push ⟨l, is.toList ++ r.insts, r.term⟩) ++ r.blocks.toArray, cur := none,
        next := r.next, scalarRegs := r.marked.foldl pushNew s.scalarRegs, here := some r.here,
        marks := r.marks.foldl markOp s.marks }) := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env s l is r hc hr
    cases op with
    | atom a =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
          rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases ht : scalar1 t with
        | false => simp [ht] at hr
        | true =>
          cases hr' : lower1 ((x, t, [w]) :: env) s.next e with
          | none => simp [ht, hr'] at hr
          | some r' =>
            simp [ht, hr'] at hr
            subst hr
            rw [lowerExpr]
            simp only [setHere, lowerOp]
            rw [bind_ok (modify_eq _ _), bind_ok (evalAt_eq ha _), bind_ok (markWords_scalar1 ht _)]
            refine (ih _ _ l is r' (by simpa using hc) (by simpa using hr')).trans ?_
            simp [List.foldl_append]
    | add a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
          rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
            rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
          cases hr' : lower1 ((x, .int, [.reg (regName x s.next)]) :: env) (s.next + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            rw [lowerExpr]
            simp only [setHere]
            rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_add cx env x ha hb (by simpa using hc))]
            rw [bind_ok (markWords_scalar1 rfl _)]
            refine (ih _ _ l _ r' rfl (by simpa using hr')).trans ?_
            simp [regsOf]
    | sub a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
          rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
            rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
          cases hr' : lower1 ((x, .int, [.reg (regName x s.next)]) :: env) (s.next + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            rw [lowerExpr]
            simp only [setHere]
            rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_sub cx env x ha hb (by simpa using hc))]
            rw [bind_ok (markWords_scalar1 rfl _)]
            refine (ih _ _ l _ r' rfl (by simpa using hr')).trans ?_
            simp [regsOf]
    | _ => simp [lower1] at hr
  | ifeq a b yes no ihy ihn =>
    intro env s l is r hc hr
    simp only [lower1] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      rw [ha] at hr
      obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
        rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
      cases hb : atomV env b with
      | none => simp [hb] at hr
      | some u =>
        obtain ⟨t', us⟩ := u
        rw [hb] at hr
        obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
          rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hy : lower1 env (s.next + 2) yes with
        | none => simp [hy] at hr
        | some ry =>
          cases hn : lower1 env ry.next no with
          | none => simp [hy, hn] at hr
          | some rn =>
            simp [hy, hn] at hr
            subst hr
            rw [lowerExpr]
            simp only [setHere]
            rw [bind_ok (modify_eq _ _), bind_ok (evalOne_eq ha _ _), bind_ok (evalOne_eq hb _ _),
              bind_ok (freshLabel_eq _ _), bind_ok (freshLabel_eq _ _),
              bind_ok (terminate_eq _ (by simpa using hc)),
              bind_ok (startBlock_eq _ rfl rfl), bind_ok (markAt_eq _ _ _)]
            rw [bind_ok (ihy env _ _ _ ry rfl (by simpa [Nat.add_assoc] using hy))]
            rw [bind_ok (startBlock_eq _ rfl rfl), bind_ok (markAt_eq _ _ _)]
            refine (ihn env _ _ _ rn rfl (by simpa using hn)).trans ?_
            simp only [List.foldl_append, List.foldl_cons, List.nil_append, List.append_nil,
              Except.ok.injEq, Prod.mk.injEq, true_and, BState.mk.injEq, and_true]
            apply Array.toList_inj.mp
            simp
  | ret a =>
    intro env s l is r hc hr
    simp only [lower1] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      simp [ha] at hr
      subst hr
      rw [lowerExpr]
      simp only [setHere]
      rw [bind_ok (modify_eq _ _), bind_ok (evalAt_eq ha _), terminate_eq _ (by simpa using hc)]
      simp
  | _ => intro env s l is r _ hr; simp [lower1] at hr

/-! ## The closed form exists on call-free `Accepted1` bodies -/

/-- **The closed form exists on a call-free `Accepted1` body** whose free
variables are bound to scalar words. -/
theorem lower1_isSome :
    ∀ (e : Expr) (scope : List String) (env : Env) (n : Nat), body1 [] scope e = true →
      EnvScalar scope env → ∃ r, lower1 env n e = some r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n hb h
    cases op with
    | atom a =>
      simp only [body1, atom1, Bool.and_eq_true] at hb
      obtain ⟨t, w, ha, ht⟩ := atomV_of_atom0 hb.1 h
      obtain ⟨r, hr⟩ := ih (x :: scope) _ n hb.2 (envScalar_cons h x w ht)
      exact ⟨_, by simp [lower1, ha, ht, hr]; rfl⟩
    | add a b =>
      simp only [body1, atom1, Bool.and_eq_true] at hb
      obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 hb.1.1 h
      obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb.1.2 h
      obtain ⟨r, hr⟩ := ih (x :: scope) ((x, .int, [.reg (regName x n)]) :: env) (n + 1) hb.2
        (envScalar_cons h x _ rfl)
      exact ⟨_, by simp [lower1, ha, hb', hr]; rfl⟩
    | sub a b =>
      simp only [body1, atom1, Bool.and_eq_true] at hb
      obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 hb.1.1 h
      obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb.1.2 h
      obtain ⟨r, hr⟩ := ih (x :: scope) ((x, .int, [.reg (regName x n)]) :: env) (n + 1) hb.2
        (envScalar_cons h x _ rfl)
      exact ⟨_, by simp [lower1, ha, hb', hr]; rfl⟩
    | call g is a ts => simp [body1, callee1] at hb
    | _ => simp [body1] at hb
  | ifeq a b yes no ihy ihn =>
    intro scope env n hb h
    simp only [body1, atom1, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨ha0, hb0⟩, hy0⟩, hn0⟩ := hb
    obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 ha0 h
    obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb0 h
    obtain ⟨ry, hy⟩ := ihy scope env (n + 2) hy0 h
    obtain ⟨rn, hn⟩ := ihn scope env ry.next hn0 h
    exact ⟨_, by simp [lower1, ha, hb', hy, hn]; rfl⟩
  | ret a =>
    intro scope env n hb h
    obtain ⟨t, w, ha, -⟩ := atomV_of_atom0 (by simpa [body1] using hb) h
    exact ⟨_, by simp [lower1, ha]; rfl⟩
  | _ => intro scope env n hb; simp [body1] at hb

/-! ## The lowering of a call-free `Accepted1` code block -/

/-- The parameter registers of an `Accepted1` code block (`lowerDeclMarks`):
`x.0` for an `Int` parameter `x`, none for a `Unit` one. -/
def params1R (d : Decl) : List Reg := if d.argTy == .int then [s!"{d.arg}.{0}"] else []

/-- The environment an `Accepted1` code block's body is lowered in: its
parameter bound to the parameter registers. -/
def env1 (d : Decl) : Env := [(d.arg, d.argTy, (params1R d).map .reg)]

/-- **The IR function of an `Accepted1` code block** named `name` with
parameter registers `params`, whose body's closed form is `r`: block `entry`
holding `r`'s instructions and terminator, then `r`'s blocks; stack-checked;
the parameters and `r`'s marked registers as its scalar registers. -/
def func1 (name : Sym) (params : List Reg) (r : Res1) : Func :=
  { name, params, blocks := ⟨"entry", r.insts, r.term⟩ :: r.blocks, checkStack := true,
    heapRegs := [], scalarRegs := ((params ++ r.marked).foldl pushNew #[]).toList }

/-- **The placement trace of an `Accepted1` code block** `d` whose body's
closed form is `r`: the start of block `entry` with the parameter and the
whole body, then `r`'s marks. -/
def marks1 (d : Decl) (r : Res1) : Array (Node × Point) :=
  r.marks.foldl markOp #[(.block "entry", (env1 d, d.body))]

/-- An `Accepted1` code block takes a `Unit` or an `Int`, returns an `Int`,
and has an `Accepted1` body in the scope of its parameter. -/
theorem decl1_shape {earlier : List String} {d : Decl} (hd : decl1 earlier d = true) :
    (d.argTy = .unit ∨ d.argTy = .int) ∧ d.retTy = .int ∧ body1 earlier (params1 d) d.body = true := by
  simp only [decl1, Bool.and_eq_true, beq_iff_eq] at hd
  obtain ⟨⟨⟨⟨-, -⟩, hr⟩, ha⟩, hb⟩ := hd
  refine ⟨?_, hr, hb⟩
  split at ha
  · exact .inl (by simpa using ha)
  · exact .inr (by simpa using ha)

theorem envScalar_env1 {d : Decl} (h : d.argTy = .unit ∨ d.argTy = .int) :
    EnvScalar (params1 d) (env1 d) := by
  rcases h with h | h
  · simp only [params1, h]
    exact envScalar_nil _
  · simp only [params1, env1, params1R, h, beq_self_eq_true, ite_true, List.map_cons, List.map_nil]
    exact envScalar_cons (envScalar_nil []) d.arg _ rfl

/-- **The lowering of a call-free `Accepted1` code block** (`lowerDeclMarks`,
any depth limit: without calls it is not read) is `func1` with the trace
`marks1`, for the body's closed form from the parameter's environment and
counter 0. -/
theorem lowerDeclMarks_lower1 (prog : Prog) (externs : List (String × Frontend.Extern))
    (obj : ObjLayout) (frames : Option Nat) {d : Decl} (hd : decl1 [] d = true) :
    ∃ r, lower1 (env1 d) 0 d.body = some r ∧
      lowerDeclMarks prog externs d obj frames = .ok (func1 (Names.user d.name) (params1R d) r, marks1 d r) := by
  obtain ⟨harg, hret, hbody⟩ := decl1_shape hd
  obtain ⟨r, hr⟩ := lower1_isSome d.body (params1 d) (env1 d) 0 hbody (envScalar_env1 harg)
  refine ⟨r, hr, ?_⟩
  have hi : Obj.valWords .int = some 1 := rfl
  have hmr : ¬ (1 > maxRets) := by simp [maxRets]
  have hma : ∀ (p : Point) (s : BState), markAt (.block "entry") p s =
      .ok ((), { s with marks := markOp s.marks (.block "entry", p) }) := fun _ _ => rfl
  rcases harg with harg | harg
  · have hu : Obj.valWords .unit = some 0 := rfl
    have hmw : ∀ s : BState, markWords .unit [] s = .ok ((), s) := fun _ => rfl
    have hl := lowerExpr_lower1 { prog, externs, fn := d.name, obj, frames } d.body (env1 d)
      { marks := #[(.block "entry", (env1 d, d.body))] } "entry" #[] r rfl hr
    simp only [env1, params1R, harg, reduceCtorEq, beq_iff_eq, ite_false, List.map_nil] at hl
    simp only [lowerDeclMarks, harg, hret, hu, hi, pure_bind, gt_iff_lt, Nat.not_lt_zero,
      ite_false, List.range_zero, List.map_nil]
    simp only [← gt_iff_lt, hmr, ite_false, buildFuncMarks, StateT.run]
    rw [bind_ok (hmw _), bind_ok (hma _ _)]
    erw [hl]
    simp [func1, marks1, env1, params1R, harg]
    rfl
  · have hmw : ∀ s : BState, markWords .int [.reg s!"{d.arg}.{0}"] s =
        .ok ((), { s with scalarRegs := pushNew s.scalarRegs s!"{d.arg}.{0}" }) := fun s =>
      (markWords_scalar1 (w := .reg _) rfl s).trans (by simp [regsOf])
    have hl := lowerExpr_lower1 { prog, externs, fn := d.name, obj, frames } d.body (env1 d)
      { scalarRegs := pushNew #[] s!"{d.arg}.{0}", marks := markOp #[] (.block "entry", (env1 d, d.body)) }
      "entry" #[] r rfl hr
    simp only [env1, params1R, harg, beq_self_eq_true, ite_true, List.map_cons, List.map_nil] at hl
    have h32 : ¬ (1 > maxArgs) := by simp [maxArgs]
    have h1 : List.range 1 = [0] := rfl
    simp only [lowerDeclMarks, harg, hret, hi, pure_bind, h32, ite_false, h1, List.map_cons, List.map_nil]
    simp only [hmr, ite_false, buildFuncMarks, StateT.run]
    rw [bind_ok (hmw _), bind_ok (hma _ _)]
    erw [hl]
    simp [func1, marks1, env1, params1R, harg, pushNew]
    rfl

end Scc.Lower.Inv
