import Scc.Lower.Inv1

/-!
# The lowering of `Accepted1` bodies with calls: closed form

`Scc/Lower/Inv1.lean` gives `lowerExpr` in closed form on call-free
`Accepted1` bodies (`lower1`). This module adds the call of a code block,
`let x = g(a); e` (`callBlock`): with no depth limit (`Ctx.frames = none`)
one `call` instruction in the open block; with a limit `fr`, the depth
counter's bracket around it: the open block reads the counter and closes
with `br .ugt (d + 1) fr deep call`, block `deep{n+4}` aborts (`stack`),
block `call{n+5}` stores `d + 1`, calls `g`, and stores `d` back.

* `lowerC cx env n l k e`: as `lower1`, from an open block `l` holding `k`
  instructions (a call's return point is `.ret l k`);
* `lowerC_of_lower1`: on a call-free body it is `lower1`;
* `lowerExpr_lowerC`: `lowerExpr` is `lowerC`, as `lowerExpr_lower1`;
* `lowerC_isSome`: on an `Accepted1` body (`body1 earlier`) whose callees are
  code blocks of the program returning an `Int`, not externs (`CalleesC`), it
  succeeds;
* `lowerDeclMarks_lowerC`: an `Accepted1` code block lowers to `func1` with
  the trace `marks1` (as `lowerDeclMarks_lower1`); `decls1_lowerC`,
  `accepted1_lowerC`: every code block of an `Accepted1` program does (it has
  no externs: `externs_accepted1`);
* `cntC`, `lowerC_next`: the fresh names consumed; `callRegs_ne`: a call's
  registers are distinct.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.Inv

/-! ## Builder steps -/

/-- `emit` of an instruction other than a call appends it to the open block. -/
theorem emit_plain {i : Inst} (hi : ∀ ds f args, i ≠ .call ds f args) {s : BState} {l : Label}
    {is : Array Inst} (hc : s.cur = some (l, is)) :
    emit i s = .ok ((), { s with cur := some (l, is.push i) }) := by
  unfold emit
  rw [bind_ok (modify_eq _ _)]
  simp only [hc]
  cases i <;> first | rfl | exact absurd rfl (hi _ _ _)

/-- `emit` of a call appends it to the open block and marks its return point
with the source point being lowered. -/
theorem emit_call (ds : List Reg) (f : Sym) (args : List Operand) {s : BState} {l : Label}
    {is : Array Inst} {p : Point} (hc : s.cur = some (l, is)) (hh : s.here = some p) :
    emit (.call ds f args) s = .ok ((), { s with
      cur := some (l, is.push (.call ds f args)), marks := markOp s.marks (.ret l is.size, p) }) := by
  unfold emit
  rw [bind_ok (modify_eq _ _)]
  simp only [hc, hh, ite_true]
  have hs : (is.push (Inst.call ds f args)).size - 1 = is.size := by simp
  show (do let s ← get; _ : B Unit) _ = _
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure, Except.bind]
  rw [hs]
  rfl

theorem markScalar_eq (r : Reg) (s : BState) :
    markScalar r s = .ok ((), { s with scalarRegs := pushNew s.scalarRegs r }) := by
  unfold markScalar
  rw [modify_eq]
  by_cases h : r ∈ s.scalarRegs <;> simp [hasReg_eq, pushNew, h]

theorem binR_eq (op : BinOp) (a b : Operand) (hint : String) {s : BState} {l : Label}
    {is : Array Inst} (hc : s.cur = some (l, is)) :
    binR op a b hint s = .ok (.reg (regName hint s.next),
      { s with next := s.next + 1, cur := some (l, is.push (.bin op (regName hint s.next) a b)) }) := by
  unfold binR
  rw [bind_ok (fresh_eq _ _), bind_ok (emit_plain (by intros; exact Inst.noConfusion)
    (s := { s with next := s.next + 1 }) hc)]
  rfl

theorem mapM_fresh1 (hint : String) (s : BState) :
    (List.range 1).mapM (fun _ => fresh hint) s =
      .ok ([regName hint s.next], { s with next := s.next + 1 }) := rfl

/-- **`callBlock` of a code block without the depth counter**
(`frames = none`), one argument word and one result: one `call` into the
fresh result register `r%n`, its return point marked with the source point
being lowered. -/
theorem callBlock_none {cx : Ctx} (g : String) (w : Operand) (hf : cx.frames = none)
    (hx : cx.externs.find? (·.1 == g) = none) {s : BState} {l : Label} {is : Array Inst} {p : Point}
    (hc : s.cur = some (l, is)) (hh : s.here = some p) :
    callBlock cx g [w] 1 s = .ok ([.reg (regName "r" s.next)], { s with
      next := s.next + 1, cur := some (l, is.push (.call [regName "r" s.next] (Names.user g) [w])),
      marks := markOp s.marks (.ret l is.size, p) }) := by
  have h1 : ¬ ([w].length > maxArgs) := by simp [maxArgs]
  have h2 : ¬ (1 > maxRets) := by simp [maxRets]
  simp only [callBlock, hx, h1, h2, ite_false, hf]
  rw [bind_ok (mapM_fresh1 _ _), bind_ok (emit_call _ _ _ (s := { s with next := s.next + 1 }) hc hh)]
  rfl

/-- `lowerOp` of a call of a code block `g` returning an `Int`: `callBlock`
with `a`'s word and one result. -/
theorem lowerOp_call {cx : Ctx} (env : Env) (x g : String) {is' : List String} {a : At} {ts : List Ty}
    {d : Decl} {t : Ty} {w : Operand} (hd : cx.prog.find? (·.name == g) = some d) (hr : d.retTy = .int)
    (ha : atomV env a = some (t, [w])) {s s' : BState} {rs : List Operand}
    (hcb : callBlock cx g [w] 1 s = .ok (rs, s')) :
    lowerOp cx env x (.call g is' a ts) s = .ok ((.int, rs), s') := by
  simp only [lowerOp]
  have hw : words d.retTy s = .ok (1, s) := by rw [hr]; rfl
  rw [bind_ok (show needSome (cx.prog.find? (·.name == g)) s!"unknown block '{g}'" s = .ok (d, s) by
    rw [hd]; rfl), bind_ok (evalAt_eq ha _), bind_ok hw, bind_ok hcb, hr]
  rfl


theorem markOp_back (ms : Array (Node × Point)) (m : Node × Point) : (markOp ms m).back? = some m := by
  simp [markOp]

theorem get_bind {α : Type} {f : BState → B α} {s : BState} : (get >>= f) s = f s s := rfl

/-! ## The depth counter's bracket -/

/-- The depth counter's bracket around a call from counter `n` (`callBlock`
with `frames = some fr`), before the call: read the thread pointer into
`tp%(n+1)`, the depth into `depth%(n+2)`, and `depth%(n+3) := depth%(n+2) + 1`. -/
def depthPre (n : Nat) : List Inst :=
  [.getTp (regName "tp" (n + 1)), .load .plain .w64 (regName "depth" (n + 2)) ⟨regName "tp" (n + 1), Tcb.depth⟩,
   .bin .add (regName "depth" (n + 3)) (.reg (regName "depth" (n + 2))) (imm 1)]

/-- The bracket's test: past the limit `fr`, to `deep{n+4}`; else to `call{n+5}`. -/
def depthTerm (fr n : Nat) : Term :=
  .br .ugt (.reg (regName "depth" (n + 3))) (imm fr) (labName "deep" (n + 4)) (labName "call" (n + 5))

/-- The bracket's abort block `deep{n+4}`: abort with `AbortKind.stack`. -/
def deepBlock (n : Nat) : Block :=
  ⟨labName "deep" (n + 4), [.call [] Names.abort [imm AbortKind.stack.code]], .unreachable⟩

/-- The start of the bracket's call block `call{n+5}`: store the new depth,
call `g` with `w` into `r%n`, read the thread pointer again into `tp%(n+6)`
and store the old depth back. -/
def callPost (g : String) (w : Operand) (n : Nat) : List Inst :=
  [.store .plain .w64 ⟨regName "tp" (n + 1), Tcb.depth⟩ (.reg (regName "depth" (n + 3))),
   .call [regName "r" n] (Names.user g) [w],
   .getTp (regName "tp" (n + 6)),
   .store .plain .w64 ⟨regName "tp" (n + 6), Tcb.depth⟩ (.reg (regName "depth" (n + 2)))]

/-- **`callBlock` of a code block with the depth counter** (`frames = some
fr`), one argument word and one result: closes the open block with
`depthPre` and `depthTerm`, pushes `deepBlock`, and leaves `call{n+5}` open
with `callPost`; marks `depth%(n+2)` scalar; marks the starts of the two
blocks and the two calls' return points with the source point being
lowered. -/
theorem callBlock_some {cx : Ctx} (g : String) (w : Operand) {fr : Nat} (hf : cx.frames = some fr)
    (hx : cx.externs.find? (·.1 == g) = none) {s : BState} {l : Label} {is : Array Inst} {p : Point}
    (hc : s.cur = some (l, is)) (hh : s.here = some p) :
    callBlock cx g [w] 1 s = .ok ([.reg (regName "r" s.next)], { s with
      next := s.next + 7,
      blocks := (s.blocks.push ⟨l, is.toList ++ depthPre s.next, depthTerm fr s.next⟩).push (deepBlock s.next),
      cur := some (labName "call" (s.next + 5), (callPost g w s.next).toArray),
      scalarRegs := pushNew s.scalarRegs (regName "depth" (s.next + 2)),
      marks := [(.block (labName "deep" (s.next + 4)), p), (.ret (labName "deep" (s.next + 4)) 0, p),
        (.block (labName "call" (s.next + 5)), p), (.ret (labName "call" (s.next + 5)) 1, p)].foldl
        markOp s.marks }) := by
  have h1 : ¬ ([w].length > maxArgs) := by simp [maxArgs]
  have h2 : ¬ (1 > maxRets) := by simp [maxRets]
  simp only [callBlock, hx, h1, h2, ite_false, hf]
  rw [bind_ok (mapM_fresh1 _ _), bind_ok (fresh_eq _ _),
    bind_ok (emit_plain (by intros; exact Inst.noConfusion) ?c1), bind_ok (fresh_eq _ _),
    bind_ok (emit_plain (by intros; exact Inst.noConfusion) ?c2), bind_ok (markScalar_eq _ _),
    bind_ok (binR_eq _ _ _ _ ?c3), bind_ok (freshLabel_eq _ _), bind_ok (freshLabel_eq _ _),
    bind_ok (terminate_eq _ ?c4), bind_ok (startBlock_eq _ rfl ?h1),
    bind_ok (emit_call _ _ _ ?c5 ?h2), bind_ok (terminate_eq _ ?c6), bind_ok (startBlock_eq _ rfl ?h3),
    bind_ok (emit_plain (by intros; exact Inst.noConfusion) ?c7), bind_ok (emit_call _ _ _ ?c8 ?h4),
    bind_ok (fresh_eq _ _), bind_ok (emit_plain (by intros; exact Inst.noConfusion) ?c9),
    bind_ok (emit_plain (by intros; exact Inst.noConfusion) ?c10)]
  all_goals try first | exact hc | exact hh | rfl
  simp only [pure, StateT.pure, Except.pure, List.map_cons, List.map_nil, Except.ok.injEq, Prod.mk.injEq,
    BState.mk.injEq, true_and, List.foldl_cons, List.foldl_nil, Array.size_push, Array.size_empty]
  refine ⟨?_, ?_⟩
  · simp [depthPre, deepBlock, depthTerm, Nat.add_assoc]
  · simp [callPost, Nat.add_assoc]


/-! ## The closed form with calls -/

/-- **The closed form of `lowerExpr` on an `Accepted1` body**, in
environment `env` from counter `n`, with the open block `l` holding `k`
instructions: as `lower1` (`lowerC_of_lower1`), and a `let x = g(a); e` of a
code block `g` of `cx.prog` returning an `Int`, not an extern, binds `x` to
the fresh result register `r = regName "r" n`:

* with `cx.frames = none`, appends `call [r] g [a]` to the open block, whose
  return point `.ret l k` is marked with the `let` and then with `e` in the
  environment with `x`;
* with `cx.frames = some fr`, appends `depthPre n` and closes the open block
  with `depthTerm fr n`; then `deepBlock n`; then block `call{n+5}` from
  `callPost g a n` (the call is its instruction 1), with `e` lowered from
  counter `n + 7`; `depth%(n+2)` is marked scalar.

`none` off the fragment, or where an atom has no scalar word. -/
def lowerC (cx : Ctx) (env : Env) (n : Nat) (l : Label) (k : Nat) : Expr → Option Res1
  | .let_ x (.atom a) e => do
      let (t, ws) ← atomV env a
      let w ← match ws with | [w] => some w | _ => none
      if scalar1 t then
        let r ← lowerC cx ((x, t, ws) :: env) n l k e
        pure { r with marked := regsOf [w] ++ r.marked }
      else none
  | .let_ x (.add a b) e => do
      let (_, ws) ← atomV env a
      let p ← match ws with | [p] => some p | _ => none
      let (_, us) ← atomV env b
      let q ← match us with | [q] => some q | _ => none
      let d := regName x n
      let r ← lowerC cx ((x, .int, [.reg d]) :: env) (n + 1) l (k + 1) e
      pure { r with insts := .addChk d p q :: r.insts, marked := d :: r.marked }
  | .let_ x (.sub a b) e => do
      let (_, ws) ← atomV env a
      let p ← match ws with | [p] => some p | _ => none
      let (_, us) ← atomV env b
      let q ← match us with | [q] => some q | _ => none
      let d := regName x n
      let r ← lowerC cx ((x, .int, [.reg d]) :: env) (n + 1) l (k + 1) e
      pure { r with insts := .subSat d p q :: r.insts, marked := d :: r.marked }
  | .let_ x (.call g is a ts) e =>
      if (cx.externs.find? (·.1 == g)).isNone then do
        let dg ← cx.prog.find? (·.name == g)
        if dg.retTy == .int then do
          let (_, ws) ← atomV env a
          let w ← match ws with | [w] => some w | _ => none
          let rr := regName "r" n
          let env' := (x, Ty.int, [Operand.reg rr]) :: env
          let pt : Point := (env, .let_ x (.call g is a ts) e)
          match cx.frames with
          | none =>
            let r ← lowerC cx env' (n + 1) l (k + 1) e
            pure { r with insts := .call [rr] (Names.user g) [w] :: r.insts, marked := rr :: r.marked,
                          marks := [(.ret l k, pt), (.ret l k, (env', e))] ++ r.marks }
          | some fr =>
            let lc := labName "call" (n + 5)
            let ld := labName "deep" (n + 4)
            let r ← lowerC cx env' (n + 7) lc 4 e
            pure { insts := depthPre n, term := depthTerm fr n,
                   blocks := deepBlock n :: ⟨lc, callPost g w n ++ r.insts, r.term⟩ :: r.blocks,
                   next := r.next, marked := regName "depth" (n + 2) :: rr :: r.marked,
                   marks := [(.block ld, pt), (.ret ld 0, pt), (.block lc, pt), (.ret lc 1, pt),
                     (.ret lc 1, (env', e))] ++ r.marks,
                   here := r.here }
        else none
      else none
  | .ifeq a b yes no => do
      let (_, ws) ← atomV env a
      let p ← match ws with | [p] => some p | _ => none
      let (_, us) ← atomV env b
      let q ← match us with | [q] => some q | _ => none
      let ly := labName "then" n
      let ln := labName "else" (n + 1)
      let ry ← lowerC cx env (n + 2) ly 0 yes
      let rn ← lowerC cx env ry.next ln 0 no
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

/-- **On a call-free body the closed form is `lower1`** (whatever the
context, the open block and its size). -/
theorem lowerC_of_lower1 (cx : Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lower1 env n e = some r → lowerC cx env n l k e = some r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
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
          cases hr' : lower1 ((x, t, [w]) :: env) n e with
          | none => simp [ht, hr'] at hr
          | some r' =>
            simp [ht, hr'] at hr
            subst hr
            simp [lowerC, ha, ht, ih _ _ l k r' hr']
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
          cases hr' : lower1 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            simp [lowerC, ha, hb, ih _ _ l (k + 1) r' hr']
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
          cases hr' : lower1 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            simp [lowerC, ha, hb, ih _ _ l (k + 1) r' hr']
    | _ => simp [lower1] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr
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
        cases hy : lower1 env (n + 2) yes with
        | none => simp [hy] at hr
        | some ry =>
          cases hn : lower1 env ry.next no with
          | none => simp [hy, hn] at hr
          | some rn =>
            simp [hy, hn] at hr
            subst hr
            simp [lowerC, ha, hb, ihy _ _ _ 0 _ hy, ihn _ _ _ 0 _ hn]
  | ret a =>
    intro env n l k r hr
    simpa [lower1, lowerC] using hr
  | _ => intro env n l k r hr; simp [lower1] at hr


/-! ## `lowerExpr` is the closed form -/

/-- **`lowerExpr` on an `Accepted1` body is `lowerC`**, as
`lowerExpr_lower1`, from an open block `(l, is)` (`lowerC` from `l` and
`is.size`). -/
theorem lowerExpr_lowerC (cx : Ctx) :
    ∀ (e : Expr) (env : Env) (s : BState) (l : Label) (is : Array Inst) (r : Res1),
      s.cur = some (l, is) → lowerC cx env s.next l is.size e = some r →
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
      simp only [lowerC] at hr
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
          cases hr' : lowerC cx ((x, t, [w]) :: env) s.next l is.size e with
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
      simp only [lowerC] at hr
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
          cases hr' : lowerC cx ((x, .int, [.reg (regName x s.next)]) :: env) (s.next + 1) l (is.size + 1) e with
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
      simp only [lowerC] at hr
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
          cases hr' : lowerC cx ((x, .int, [.reg (regName x s.next)]) :: env) (s.next + 1) l (is.size + 1) e with
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
    | call g is' a ts =>
      simp only [lowerC] at hr
      cases hx : (cx.externs.find? (·.1 == g)).isNone with
      | false => simp [hx] at hr
      | true =>
      have hx' : cx.externs.find? (·.1 == g) = none := by simpa using hx
      cases hd : cx.prog.find? (·.name == g) with
      | none => simp [hx, hd] at hr
      | some dg =>
      cases hrt : dg.retTy == .int with
      | false => simp only [beq_eq_false_iff_ne] at hrt; simp [hx, hd] at hr; exact absurd hr.1 hrt
      | true =>
      have hrt' : dg.retTy = .int := by simpa using hrt
      cases ha : atomV env a with
      | none => simp [hx, hd, ha] at hr
      | some v =>
      obtain ⟨t, ws⟩ := v
      simp only [hx, hd, hrt, ha, ite_true, Option.bind_eq_bind, Option.bind_some] at hr
      obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
        rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
      rw [lowerExpr]
      simp only [setHere]
      rw [bind_ok (modify_eq _ _)]
      cases hf : cx.frames with
      | none =>
        cases hr' : lowerC cx ((x, .int, [.reg (regName "r" s.next)]) :: env) (s.next + 1) l (is.size + 1) e with
        | none => simp [hf, hr'] at hr
        | some r' =>
        simp [hf, hr'] at hr
        subst hr
        rw [bind_ok (lowerOp_call env x g hd hrt' ha (callBlock_none g w hf hx' (by simpa using hc) rfl))]
        simp only [hx, ite_true]
        rw [get_bind]
        simp only [markOp_back]
        rw [bind_ok (markAt_eq _ _ _), bind_ok (markWords_scalar1 rfl _)]
        refine (ih _ _ l _ r' rfl (by simpa using hr')).trans ?_
        simp [regsOf, markOp]
      | some fr =>
        cases hr' : lowerC cx ((x, .int, [.reg (regName "r" s.next)]) :: env) (s.next + 7)
            (labName "call" (s.next + 5)) 4 e with
        | none => simp [hf, hr'] at hr
        | some r' =>
        simp [hf, hr'] at hr
        subst hr
        rw [bind_ok (lowerOp_call env x g hd hrt' ha (callBlock_some g w hf hx' (by simpa using hc) rfl))]
        simp only [hx, ite_true]
        rw [get_bind]
        simp only [List.foldl_cons, List.foldl_nil, markOp_back]
        rw [bind_ok (markAt_eq _ _ _), bind_ok (markWords_scalar1 rfl _)]
        refine (ih _ _ _ _ r' rfl (by simpa [callPost] using hr')).trans ?_
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and, BState.mk.injEq, and_true]
        refine ⟨?_, ?_⟩
        · apply Array.toList_inj.mp
          simp
        · simp [regsOf]
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env s l is r hc hr
    simp only [lowerC] at hr
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
        cases hy : lowerC cx env (s.next + 2) (labName "then" s.next) 0 yes with
        | none => simp [hy] at hr
        | some ry =>
          cases hn : lowerC cx env ry.next (labName "else" (s.next + 1)) 0 no with
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
    simp only [lowerC] at hr
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
  | _ => intro env s l is r _ hr; simp [lowerC] at hr

/-! ## The closed form exists on `Accepted1` bodies -/

/-- The callees of `earlier` are code blocks of `prog` returning an `Int`,
and not externs. -/
def CalleesC (prog : Prog) (externs : List (String × Frontend.Extern)) (earlier : List String) : Prop :=
  ∀ g ∈ earlier, externs.find? (·.1 == g) = none ∧
    ∃ dg, prog.find? (·.name == g) = some dg ∧ dg.retTy = .int

/-- **The closed form exists on an `Accepted1` body** (`body1 earlier`)
whose callees are code blocks of the program returning an `Int`, not externs
(`CalleesC`), and whose free variables are bound to scalar words. -/
theorem lowerC_isSome (cx : Ctx) {earlier : List String} (hcx : CalleesC cx.prog cx.externs earlier) :
    ∀ (e : Expr) (scope : List String) (env : Env) (n : Nat) (l : Label) (k : Nat),
      body1 earlier scope e = true → EnvScalar scope env → ∃ r, lowerC cx env n l k e = some r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n l k hb h
    cases op with
    | atom a =>
      simp only [body1, atom1, Bool.and_eq_true] at hb
      obtain ⟨t, w, ha, ht⟩ := atomV_of_atom0 hb.1 h
      obtain ⟨r, hr⟩ := ih (x :: scope) _ n l k hb.2 (envScalar_cons h x w ht)
      exact ⟨_, by simp [lowerC, ha, ht, hr]; rfl⟩
    | add a b =>
      simp only [body1, atom1, Bool.and_eq_true] at hb
      obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 hb.1.1 h
      obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb.1.2 h
      obtain ⟨r, hr⟩ := ih (x :: scope) ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) hb.2
        (envScalar_cons h x _ rfl)
      exact ⟨_, by simp [lowerC, ha, hb', hr]; rfl⟩
    | sub a b =>
      simp only [body1, atom1, Bool.and_eq_true] at hb
      obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 hb.1.1 h
      obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb.1.2 h
      obtain ⟨r, hr⟩ := ih (x :: scope) ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) hb.2
        (envScalar_cons h x _ rfl)
      exact ⟨_, by simp [lowerC, ha, hb', hr]; rfl⟩
    | call g is a ts =>
      simp only [body1, callee1, atom1, Bool.and_eq_true] at hb
      obtain ⟨⟨⟨⟨⟨hg, -⟩, -⟩, -⟩, ha0⟩, he⟩ := hb
      obtain ⟨hx, dg, hd, hrt⟩ := hcx g (by simpa using hg)
      obtain ⟨t, w, ha, -⟩ := atomV_of_atom0 ha0 h
      have hs := envScalar_cons h x (t := .int) (.reg (regName "r" n)) rfl
      cases hf : cx.frames with
      | none =>
        obtain ⟨r, hr⟩ := ih (x :: scope) _ (n + 1) l (k + 1) he hs
        exact ⟨_, by simp [lowerC, hx, hd, hrt, ha, hf, hr]; rfl⟩
      | some fr =>
        obtain ⟨r, hr⟩ := ih (x :: scope) _ (n + 7) (labName "call" (n + 5)) 4 he hs
        exact ⟨_, by simp [lowerC, hx, hd, hrt, ha, hf, hr]; rfl⟩
    | _ => simp [body1] at hb
  | ifeq a b yes no ihy ihn =>
    intro scope env n l k hb h
    simp only [body1, atom1, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨ha0, hb0⟩, hy0⟩, hn0⟩ := hb
    obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 ha0 h
    obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb0 h
    obtain ⟨ry, hy⟩ := ihy scope env (n + 2) (labName "then" n) 0 hy0 h
    obtain ⟨rn, hn⟩ := ihn scope env ry.next (labName "else" (n + 1)) 0 hn0 h
    exact ⟨_, by simp [lowerC, ha, hb', hy, hn]; rfl⟩
  | ret a =>
    intro scope env n l k hb h
    obtain ⟨t, w, ha, -⟩ := atomV_of_atom0 (by simpa [body1] using hb) h
    exact ⟨_, by simp [lowerC, ha]; rfl⟩
  | _ => intro scope env n l k hb; simp [body1] at hb

/-! ## The lowering of an `Accepted1` code block -/

/-- **The lowering of an `Accepted1` code block** (`decl1 earlier`) whose
callees are code blocks of the program returning an `Int`, not externs
(`CalleesC`), is `func1` with the trace `marks1`, for the body's closed form
`lowerC` from the parameter's environment, counter 0 and the empty block
`entry` (as `lowerDeclMarks_lower1`). -/
theorem lowerDeclMarks_lowerC (prog : Prog) (externs : List (String × Frontend.Extern))
    (obj : ObjLayout) (frames : Option Nat) {earlier : List String} (hcx : CalleesC prog externs earlier)
    {d : Decl} (hd : decl1 earlier d = true) :
    ∃ r, lowerC { prog, externs, fn := d.name, obj, frames } (env1 d) 0 "entry" 0 d.body = some r ∧
      lowerDeclMarks prog externs d obj frames = .ok (func1 (Names.user d.name) (params1R d) r, marks1 d r) := by
  obtain ⟨harg, hret, hbody⟩ := decl1_shape hd
  obtain ⟨r, hr⟩ := lowerC_isSome { prog, externs, fn := d.name, obj, frames } hcx d.body (params1 d)
    (env1 d) 0 "entry" 0 hbody (envScalar_env1 harg)
  refine ⟨r, hr, ?_⟩
  have hi : Obj.valWords .int = some 1 := rfl
  have hmr : ¬ (1 > maxRets) := by simp [maxRets]
  have hma : ∀ (p : Point) (s : BState), markAt (.block "entry") p s =
      .ok ((), { s with marks := markOp s.marks (.block "entry", p) }) := fun _ _ => rfl
  rcases harg with harg | harg
  · have hu : Obj.valWords .unit = some 0 := rfl
    have hmw : ∀ s : BState, markWords .unit [] s = .ok ((), s) := fun _ => rfl
    have hl := lowerExpr_lowerC { prog, externs, fn := d.name, obj, frames } d.body (env1 d)
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
    have hl := lowerExpr_lowerC { prog, externs, fn := d.name, obj, frames } d.body (env1 d)
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

/-! ## The lowering of the code blocks of an `Accepted1` program -/

/-- The code blocks of a `decls1` list return an `Int`. -/
theorem decls1_retTy : ∀ (ds : Prog) (earlier : List String), decls1 earlier ds = true →
    ∀ d ∈ ds, d.retTy = .int
  | [], _, _, _, hd => by cases hd
  | d :: ds, earlier, h, d', hd' => by
    simp only [decls1, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd' with rfl | hm
    · exact (decl1_shape h.1).2.1
    · exact decls1_retTy ds _ h.2 d' hm

/-- In a program whose code blocks return an `Int`, not externs, the names
of code blocks are `CalleesC`. -/
theorem calleesC_of_names {prog : Prog} {externs : List (String × Frontend.Extern)}
    (hret : ∀ d ∈ prog, d.retTy = .int) (hext : ∀ d ∈ prog, externs.find? (·.1 == d.name) = none)
    {earlier : List String} (he : ∀ g ∈ earlier, ∃ d ∈ prog, d.name = g) : CalleesC prog externs earlier := by
  intro g hg
  obtain ⟨d, hd, rfl⟩ := he g hg
  refine ⟨hext d hd, ?_⟩
  obtain ⟨dg, hf⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨d, hd, by simp⟩ : (prog.find? (·.name == d.name)).isSome)
  exact ⟨dg, hf, hret dg (List.mem_of_find?_eq_some hf)⟩

/-- **The lowering of the code blocks of a `decls1` list** `ds` of a program
whose code blocks return an `Int`, not externs, the names in `earlier` and
in `ds` being code blocks of the program: each is `func1` with the trace
`marks1` (`lowerDeclMarks_lowerC`). -/
theorem decls1_lowerC (prog : Prog) (externs : List (String × Frontend.Extern)) (obj : ObjLayout)
    (frames : Option Nat) (hret : ∀ d ∈ prog, d.retTy = .int)
    (hext : ∀ d ∈ prog, externs.find? (·.1 == d.name) = none) :
    ∀ (ds : Prog) (earlier : List String), decls1 earlier ds = true → (∀ g ∈ earlier, ∃ d ∈ prog, d.name = g) →
      (∀ d ∈ ds, d ∈ prog) → ∀ d ∈ ds,
      ∃ r, lowerC { prog, externs, fn := d.name, obj, frames } (env1 d) 0 "entry" 0 d.body = some r ∧
        lowerDeclMarks prog externs d obj frames = .ok (func1 (Names.user d.name) (params1R d) r, marks1 d r)
  | [], _, _, _, _, _, hd => by cases hd
  | d :: ds, earlier, h, he, hp, d', hd' => by
    simp only [decls1, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd' with rfl | hm
    · exact lowerDeclMarks_lowerC prog externs obj frames (calleesC_of_names hret hext he) h.1
    · refine decls1_lowerC prog externs obj frames hret hext ds _ h.2 ?_ (fun x hx => hp x (by simp [hx])) d' hm
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨d, hp d (by simp), rfl⟩
      · exact he g hg

/-- A code block returning an `Int` is no extern (`Frontend.externOf`: every
extern returns `Unit`). -/
theorem externOf_int {d : Decl} (h : d.retTy = .int) : Frontend.externOf d = none := by
  simp [Frontend.externOf, h, Frontend.declIs, Frontend.printLoopD]

/-- **An `Accepted1` program has no externs** (`Frontend.externs`): its code
blocks return an `Int`. -/
theorem externs_accepted1 {prog : Prog} (hp : Accepted1 prog = true) : Frontend.externs prog = [] := by
  have hd : decls1 [] prog = true := by
    simp only [Accepted1, Bool.and_eq_true] at hp
    exact hp.1.2
  have hret := decls1_retTy prog [] hd
  simp only [Frontend.externs, List.filterMap_eq_nil_iff]
  intro d hm
  simp [externOf_int (hret d hm)]

/-- **The lowering of every code block of an `Accepted1` program** with the
frontend's externs (`Frontend.externs`, none: `externs_accepted1`): `func1`
with the trace `marks1`, for the body's closed form `lowerC` (any object
layout and depth limit). -/
theorem accepted1_lowerC {prog : Prog} (hp : Accepted1 prog = true) (obj : ObjLayout) (frames : Option Nat) :
    ∀ d ∈ prog,
      ∃ r, lowerC { prog, externs := Frontend.externs prog, fn := d.name, obj, frames } (env1 d) 0 "entry" 0
          d.body = some r ∧
        lowerDeclMarks prog (Frontend.externs prog) d obj frames =
          .ok (func1 (Names.user d.name) (params1R d) r, marks1 d r) := by
  have hd : decls1 [] prog = true := by
    simp only [Accepted1, Bool.and_eq_true] at hp
    exact hp.1.2
  exact decls1_lowerC prog _ obj frames (decls1_retTy prog [] hd) (fun _ _ => by simp [externs_accepted1 hp])
    prog [] hd (by simp) (fun _ h => h)

/-! ## Counters and free variables -/

/-- **The fresh names `lowerC` consumes on `e`** with depth limit `frames`:
a `let` of `+`/`-` one; a call one (`r%n`), seven with the depth counter;
an `if` its two labels and its branches'. -/
def cntC (frames : Option Nat) : Expr → Nat
  | .let_ _ (.add _ _) e => cntC frames e + 1
  | .let_ _ (.sub _ _) e => cntC frames e + 1
  | .let_ _ (.call ..) e => cntC frames e + (if frames.isSome then 7 else 1)
  | .let_ _ _ e => cntC frames e
  | .ifeq _ _ yes no => cntC frames yes + cntC frames no + 2
  | _ => 0

/-- **`lowerC`'s final counter** is the start plus `cntC`. -/
theorem lowerC_next (cx : Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → r.next = n + cntC cx.frames e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | atom a =>
      simp only [lowerC] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        match ws, hr with
        | [w], hr =>
        cases hr' : lowerC cx ((x, t, [w]) :: env) n l k e with
        | none => cases ht : scalar1 t <;> simp [ht, hr'] at hr
        | some r' =>
          cases ht : scalar1 t <;> simp [ht, hr'] at hr
          subst hr
          simp [ih _ _ _ _ _ hr', cntC]
    | add a b | sub a b =>
      simp only [lowerC] at hr
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
          cases hr' : lowerC cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            simp [ih _ _ _ _ _ hr', cntC]; omega
    | call g is a ts =>
      simp only [lowerC] at hr
      cases hx : (cx.externs.find? (·.1 == g)).isNone with
      | false => simp [hx] at hr
      | true =>
      cases hd : cx.prog.find? (·.name == g) with
      | none => simp [hx, hd] at hr
      | some dg =>
      cases hrt : dg.retTy == .int with
      | false => simp only [beq_eq_false_iff_ne] at hrt; simp [hx, hd] at hr; exact absurd hr.1 hrt
      | true =>
      cases ha : atomV env a with
      | none => simp [hx, hd, ha] at hr
      | some v =>
      obtain ⟨t, ws⟩ := v
      simp only [hx, hd, hrt, ha, ite_true, Option.bind_eq_bind, Option.bind_some] at hr
      match ws, hr with
      | [w], hr =>
      cases hf : cx.frames with
      | none =>
        cases hr' : lowerC cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1) l (k + 1) e with
        | none => simp [hf, hr'] at hr
        | some r' =>
          simp [hf, hr'] at hr
          subst hr
          simp [ih _ _ _ _ _ hr', cntC, hf]; omega
      | some fr =>
        cases hr' : lowerC cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 7) (labName "call" (n + 5)) 4 e with
        | none => simp [hf, hr'] at hr
        | some r' =>
          simp [hf, hr'] at hr
          subst hr
          simp [ih _ _ _ _ _ hr', cntC, hf]; omega
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr
    simp only [lowerC] at hr
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
        cases hy : lowerC cx env (n + 2) (labName "then" n) 0 yes with
        | none => simp [hy] at hr
        | some ry =>
          cases hn : lowerC cx env ry.next (labName "else" (n + 1)) 0 no with
          | none => simp [hy, hn] at hr
          | some rn =>
            simp [hy, hn] at hr
            subst hr
            simp only [ihn _ _ _ _ _ hn, ihy _ _ _ _ _ hy, cntC]; omega
  | ret a =>
    intro env n l k r hr
    simp only [lowerC] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v => simp [ha] at hr; subst hr; simp [cntC]
  | _ => intro env n l k r hr; simp [lowerC] at hr

/-- **The registers of a call from counter `n` are distinct**: the result
`r%n`, the thread pointers `tp%(n+1)`, `tp%(n+6)` and the depths
`depth%(n+2)`, `depth%(n+3)` are pairwise distinct (`regName_ne`), and
distinct from every register named from a counter outside `n .. n+6`. -/
theorem callRegs_ne (n : Nat) :
    regName "r" n ≠ regName "tp" (n + 1) ∧ regName "r" n ≠ regName "tp" (n + 6) ∧
    regName "r" n ≠ regName "depth" (n + 2) ∧ regName "r" n ≠ regName "depth" (n + 3) ∧
    regName "tp" (n + 1) ≠ regName "tp" (n + 6) ∧ regName "depth" (n + 2) ≠ regName "depth" (n + 3) ∧
    regName "tp" (n + 1) ≠ regName "depth" (n + 2) ∧ regName "tp" (n + 1) ≠ regName "depth" (n + 3) ∧
    regName "tp" (n + 6) ≠ regName "depth" (n + 2) ∧ regName "tp" (n + 6) ≠ regName "depth" (n + 3) :=
  ⟨regName_ne (by omega), regName_ne (by omega), regName_ne (by omega), regName_ne (by omega),
   regName_ne (by omega), regName_ne (by omega), regName_ne (by omega), regName_ne (by omega),
   regName_ne (by omega), regName_ne (by omega)⟩

end Scc.Lower.Inv
