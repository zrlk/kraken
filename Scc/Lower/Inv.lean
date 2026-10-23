import Scc.Lower.Spec
import Scc.IR.StackMap

/-!
# The lowering of `Accepted0` bodies: closed form and builder invariants

For a body in the fragment `Accepted0` (`Scc/Lower/Spec.lean`: straight-line
`let`s of an atom or a checked `+`, then `ret`), the term lowering
`lowerExpr` is a fold that the composition proof can induct on. This module
gives it in closed form and proves the builder's invariants on it:

* `lower0 env n e`: what lowering `e` in environment `env` from fresh-name
  counter `n` produces: the instructions (one `addChk` per `+`, nothing for a
  `let` of an atom), the returned operands, the final counter, the registers
  marked scalar, and the source point at the `ret`;
* `lowerExpr_lower0`: from a state whose open block is `(l, is)`,
  `lowerExpr` closes the block `l` with `is` and `lower0`'s instructions and
  `ret`, and changes nothing else but the counter, the scalar registers and
  the source point; `lower0_isSome`: on an `Accepted0` body it succeeds;
* `lowerDeclMarks_accepted0`: the lowering of an `Accepted0` code block is
  one function with one block `entry` (`func0`) and one placement mark, the
  block's start with the parameter and the whole body;
* the invariants: the registers `fresh` names are pairwise distinct
  (`regName_ne`; `dests_nodup`: the instructions write pairwise distinct
  registers), every register an instruction or the `ret` reads is written by
  an earlier instruction (`reads_defined`, `DefBefore`), the block list is
  well-formed (`BlocksWF`: each label once, every branch target a block) and
  the placement trace names only nodes of the function (`MarksIn`);
  `accepted0_inv` collects them for an `Accepted0` code block.

`Spike/Test/LowerInv.lean` instantiates them at `ret0.w`.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.Inv

/-! ## Register names -/

/-- The name `fresh hint` gives at counter `n`. -/
def regName (hint : String) (n : Nat) : Reg := s!"{hint}%{n}"

theorem fresh_eq (hint : String) (s : BState) :
    fresh hint s = .ok (regName hint s.next, { s with next := s.next + 1 }) := rfl

private theorem notPct_of_toDigits {n : Nat} : '%' ∉ Nat.toDigits 10 n := by
  intro h
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert this; decide

private theorem tail_eq_of_sep {c : Char} :
    ∀ {a b s t : List Char}, c ∉ s → c ∉ t → a ++ c :: s = b ++ c :: t → s = t := by
  intro a b s t hs ht h
  have h' := congrArg (fun l => (l.reverse.takeWhile (· != c))) h
  simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append] at h'
  have key : ∀ (u v : List Char), c ∉ u → (u.reverse ++ c :: v).takeWhile (· != c) = u.reverse := by
    intro u v hu
    rw [List.takeWhile_append_of_pos]
    · simp
    · intro x hx
      have : x ∈ u := List.mem_reverse.mp hx
      simp only [bne_iff_ne, ne_eq]
      rintro rfl; exact hu this
  rw [key s _ hs, key t _ ht] at h'
  exact List.reverse_inj.mp h'

/-- Names `fresh` gives at different counters differ (whatever the hints):
the counter is the digits after the last `%`. -/
theorem regName_ne {a b : String} {n m : Nat} (h : n ≠ m) : regName a n ≠ regName b m := by
  intro he
  apply h
  have hl := congrArg String.toList he
  simp only [regName, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr] at hl
  have hp : (toString "%").toList = ['%'] := rfl
  have : Nat.toDigits 10 n = Nat.toDigits 10 m := by
    refine tail_eq_of_sep (c := '%') (a := (toString a).toList) (b := (toString b).toList)
      notPct_of_toDigits notPct_of_toDigits ?_
    simpa [hp, List.append_assoc] using hl
  rw [← Nat.ofDigitChars_ten_toDigits (n := n), ← Nat.ofDigitChars_ten_toDigits (n := m), this]

/-! ## The closed form -/

/-- `evalAt` as a function: the shape type and words of an atom. -/
def atomV (env : Env) : At → Option (Ty × List Operand)
  | .var x => (env.find? (·.1 == x)).map fun (_, t, ws) => (t, ws)
  | .lit n => if n ≥ 2 ^ 64 then none else some (.intS (.lit n), [imm n])
  | .unit => some (.unit, [])

/-- A scalar one-word type: its trace mask is one scalar word. -/
def scalar1 (t : Ty) : Bool := Obj.traceMask t == some [false]

/-- The registers among some operands. -/
def regsOf (ws : List Operand) : List Reg := ws.filterMap fun | .reg r => some r | .imm _ => none

/-- **What lowering an `Accepted0` body produces** (`lower0`). -/
structure Res where
  /-- The instructions, in order. -/
  insts : List Inst
  /-- The operands of the `ret`. -/
  ret : List Operand
  /-- The fresh-name counter at the end. -/
  next : Nat
  /-- The registers marked scalar (`markScalar`), in order. -/
  marked : List Reg
  /-- The source point at the `ret`. -/
  here : Point

/-- **The closed form of `lowerExpr` on an `Accepted0` body**, in
environment `env` from counter `n`: a `let` of an atom binds its words and
emits nothing; a `let` of `a + b` emits `addChk d a b` into the fresh
register `d = regName x n`; `ret a` returns `a`'s words. `none` off the
fragment, or where an atom has no scalar word. -/
def lower0 (env : Env) (n : Nat) : Expr → Option Res
  | .let_ x (.atom a) e => do
      let (t, ws) ← atomV env a
      let w ← match ws with | [w] => some w | _ => none
      if scalar1 t then
        let r ← lower0 ((x, t, ws) :: env) n e
        pure { r with marked := regsOf [w] ++ r.marked }
      else none
  | .let_ x (.add a b) e => do
      let (_, ws) ← atomV env a
      let p ← match ws with | [p] => some p | _ => none
      let (_, us) ← atomV env b
      let q ← match us with | [q] => some q | _ => none
      let d := regName x n
      let r ← lower0 ((x, .int, [.reg d]) :: env) (n + 1) e
      pure { r with insts := .addChk d p q :: r.insts, marked := d :: r.marked }
  | .ret a => do
      let (_, ws) ← atomV env a
      pure { insts := [], ret := ws, next := n, marked := [], here := (env, .ret a) }
  | _ => none

/-- Push `r` unless it is there (`markScalar`, `markHeap`). -/
def pushNew (a : Array Reg) (r : Reg) : Array Reg := if a.contains r then a else a.push r

/-! ## `lowerExpr` is the closed form -/

theorem bind_ok {α β : Type} {m : B α} {f : α → B β} {s : BState} {a : α} {s' : BState}
    (h : m s = .ok (a, s')) : (m >>= f) s = f a s' := by
  show (do let (a, s) ← m s; f a s : Except String _) = _
  rw [h]; rfl

theorem modify_eq (f : BState → BState) (s : BState) : (modify f : B Unit) s = .ok ((), f s) := rfl

theorem evalAt_eq {env : Env} {a : At} {v : Ty × List Operand} (h : atomV env a = some v)
    (s : BState) : evalAt env a s = .ok (v, s) := by
  cases a with
  | var x =>
    simp only [atomV, Option.map_eq_some_iff] at h
    obtain ⟨⟨y, t, ws⟩, hf, rfl⟩ := h
    simp [evalAt, lookupV, hf]; rfl
  | lit n =>
    simp only [atomV] at h
    split at h
    · cases h
    · cases h; simp [evalAt, *]; rfl
  | unit => simp only [atomV, Option.some.injEq] at h; subst h; rfl

theorem markWords_scalar1 {t : Ty} {w : Operand} (ht : scalar1 t = true) (s : BState) :
    markWords t [w] s = .ok ((), { s with scalarRegs := (regsOf [w]).foldl pushNew s.scalarRegs }) := by
  have hm : Obj.traceMask t = some [false] := by simpa [scalar1] using ht
  cases w with
  | imm v => simp [markWords, hm, needSome, regsOf]; rfl
  | reg r =>
    have hmod : ∀ f : BState → BState, (modify f : B Unit) s = .ok ((), f s) := fun _ => rfl
    by_cases hr : r ∈ s.scalarRegs <;>
      simp [markWords, hm, needSome, markScalar, hasReg_eq, regsOf, pushNew, hr, hmod]

theorem evalOne_eq {env : Env} {a : At} {t : Ty} {p : Operand} (h : atomV env a = some (t, [p]))
    (what : String) (s : BState) : evalOne env a what s = .ok (p, s) := by
  unfold evalOne
  rw [bind_ok (evalAt_eq h s)]
  rfl

theorem emit_addChk {d : Reg} {p q : Operand} {s : BState} {l : Label}
    {is : Array Inst} (hc : s.cur = some (l, is)) :
    emit (.addChk d p q) s = .ok ((), { s with cur := some (l, is.push (.addChk d p q)) }) := by
  unfold emit
  rw [bind_ok (modify_eq _ _)]
  simp only [hc]
  rfl

theorem terminate_eq (t : Term) {s : BState} {l : Label} {is : Array Inst} (hc : s.cur = some (l, is)) :
    terminate t s = .ok ((), { s with blocks := s.blocks.push ⟨l, is.toList, t⟩, cur := none }) := by
  unfold terminate
  rw [modify_eq]
  simp only [hc]

theorem lowerOp_add (cx : Ctx) (env : Env) (x : String) {a b : At} {t t' : Ty} {p q : Operand}
    (ha : atomV env a = some (t, [p])) (hb : atomV env b = some (t', [q])) {s : BState} {l : Label}
    {is : Array Inst} (hc : s.cur = some (l, is)) :
    lowerOp cx env x (.add a b) s = .ok ((.int, [.reg (regName x s.next)]),
      { s with next := s.next + 1, cur := some (l, is.push (.addChk (regName x s.next) p q)) }) := by
  simp only [lowerOp]
  rw [bind_ok (evalOne_eq ha _ _), bind_ok (evalOne_eq hb _ _), bind_ok (fresh_eq _ _),
    bind_ok (emit_addChk (s := { s with next := s.next + 1 }) hc)]
  rfl

/-- **`lowerExpr` on an `Accepted0` body** (see the module docstring). -/
theorem lowerExpr_lower0 (cx : Ctx) :
    ∀ (e : Expr) (env : Env) (s : BState) (l : Label) (is : Array Inst) (r : Res),
      s.cur = some (l, is) → lower0 env s.next e = some r →
      lowerExpr cx env e s = .ok ((), { s with
        blocks := s.blocks.push ⟨l, is.toList ++ r.insts, .ret r.ret⟩, cur := none,
        next := r.next, scalarRegs := r.marked.foldl pushNew s.scalarRegs, here := some r.here }) := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env s l is r hc hr
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
        cases ht : scalar1 t with
        | false => simp [ht] at hr
        | true =>
          cases hr' : lower0 ((x, t, [w]) :: env) s.next e with
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
          cases hr' : lower0 ((x, .int, [.reg (regName x s.next)]) :: env) (s.next + 1) e with
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
    | _ => simp [lower0] at hr
  | ret a =>
    intro env s l is r hc hr
    simp only [lower0] at hr
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
  | _ => intro env s l is r _ hr; simp [lower0] at hr

/-! ## The closed form exists on `Accepted0` bodies -/

/-- Every variable of `scope` is bound in `env` to one scalar word. -/
def EnvScalar (scope : List String) (env : Env) : Prop :=
  ∀ x ∈ scope, ∃ y t w, env.find? (·.1 == x) = some (y, t, [w]) ∧ scalar1 t = true

theorem envScalar_nil (env : Env) : EnvScalar [] env := by
  intro x hx; cases hx

theorem envScalar_cons {scope : List String} {env : Env} (h : EnvScalar scope env) (x : String)
    {t : Ty} (w : Operand) (ht : scalar1 t = true) :
    EnvScalar (x :: scope) ((x, t, [w]) :: env) := by
  intro y hy
  by_cases hxy : x = y
  · subst hxy; exact ⟨x, t, w, by simp, ht⟩
  · have hy' : y ∈ scope := by
      rcases List.mem_cons.mp hy with h | h
      · exact absurd h.symm hxy
      · exact h
    obtain ⟨z, u, v, hf, hu⟩ := h y hy'
    refine ⟨z, u, v, ?_, hu⟩
    simp [hxy, hf]

theorem atomV_of_atom0 {scope : List String} {env : Env} {a : At} (ha : atom0 scope a = true)
    (h : EnvScalar scope env) : ∃ t w, atomV env a = some (t, [w]) ∧ scalar1 t = true := by
  cases a with
  | var x =>
    obtain ⟨y, t, w, hf, ht⟩ := h x (by simpa [atom0] using ha)
    exact ⟨t, w, by simp [atomV, hf], ht⟩
  | lit n =>
    have hn : n < 2 ^ 63 := by simpa [atom0] using ha
    refine ⟨.intS (.lit n), imm n, ?_, rfl⟩
    have : ¬ n ≥ 2 ^ 64 := by omega
    simp [atomV, this]
  | unit => simp [atom0] at ha

/-- **The closed form exists on an `Accepted0` body** whose free variables
are bound to scalar words. -/
theorem lower0_isSome :
    ∀ (e : Expr) (scope : List String) (env : Env) (n : Nat), body0 scope e = true →
      EnvScalar scope env → ∃ r, lower0 env n e = some r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n hb h
    cases op with
    | atom a =>
      simp only [body0, Bool.and_eq_true] at hb
      obtain ⟨t, w, ha, ht⟩ := atomV_of_atom0 hb.1 h
      obtain ⟨r, hr⟩ := ih (x :: scope) _ n hb.2 (envScalar_cons h x w ht)
      exact ⟨_, by simp [lower0, ha, ht, hr]; rfl⟩
    | add a b =>
      simp only [body0, Bool.and_eq_true] at hb
      obtain ⟨t, p, ha, -⟩ := atomV_of_atom0 hb.1.1 h
      obtain ⟨t', q, hb', -⟩ := atomV_of_atom0 hb.1.2 h
      obtain ⟨r, hr⟩ := ih (x :: scope) ((x, .int, [.reg (regName x n)]) :: env) (n + 1) hb.2
        (envScalar_cons h x _ rfl)
      exact ⟨_, by simp [lower0, ha, hb', hr]; rfl⟩
    | _ => simp [body0] at hb
  | ret a =>
    intro scope env n hb h
    obtain ⟨t, w, ha, -⟩ := atomV_of_atom0 (by simpa [body0] using hb) h
    exact ⟨_, by simp [lower0, ha]; rfl⟩
  | _ => intro scope env n hb; simp [body0] at hb

/-! ## The lowering of an `Accepted0` code block -/

/-- **The IR function of an `Accepted0` code block** named `name` whose
body's closed form is `r`: no parameters, one block `entry` holding `r`'s
instructions and returning `r.ret`, stack-checked, `r`'s marked registers as
its scalar registers. -/
def func0 (name : Sym) (r : Res) : Func :=
  { name, params := [], blocks := [⟨"entry", r.insts, .ret r.ret⟩], checkStack := true,
    heapRegs := [], scalarRegs := (r.marked.foldl pushNew #[]).toList }

/-- **The placement trace of an `Accepted0` code block**: one mark, the
start of block `entry`, with the parameter (`Unit`, no word) and the whole
body. -/
def marks0 (d : Decl) : Array (Node × Point) :=
  #[(.block "entry", ([(d.arg, .unit, [])], d.body))]

theorem accepted0_decl {d : Decl} (hd : Accepted0 [d] = true) :
    d.name = "main" ∧ d.tparams = [] ∧ d.idx = [] ∧ d.argTy = .unit ∧ d.retTy = .int ∧
      body0 [] d.body = true := by
  simp only [Accepted0, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hd
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩ := hd
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- An `Accepted0` code block has at most `maxAdds0` checked `+`s. -/
theorem accepted0_adds {d : Decl} (hd : Accepted0 [d] = true) : adds0 d.body ≤ maxAdds0 := by
  simp only [Accepted0, Bool.and_eq_true, decide_eq_true_eq] at hd
  exact hd.2

/-- **The lowering of an `Accepted0` code block** (`lowerDeclMarks`) is
`func0` with the trace `marks0`, for the body's closed form from the
parameter's environment and counter 0. -/
theorem lowerDeclMarks_accepted0 (prog : Prog) (externs : List (String × Frontend.Extern))
    (obj : ObjLayout) (frames : Option Nat) {d : Decl} (hd : Accepted0 [d] = true) :
    ∃ r, lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      lowerDeclMarks prog externs d obj frames = .ok (func0 (Names.user d.name) r, marks0 d) := by
  obtain ⟨-, -, -, harg, hret, hbody⟩ := accepted0_decl hd
  obtain ⟨r, hr⟩ := lower0_isSome d.body [] [(d.arg, .unit, [])] 0 hbody (envScalar_nil _)
  refine ⟨r, hr, ?_⟩
  have hu : Obj.valWords .unit = some 0 := rfl
  have hi : Obj.valWords .int = some 1 := rfl
  have hmw : ∀ s : BState, markWords .unit [] s = .ok ((), s) := fun _ => rfl
  have hl := lowerExpr_lower0 { prog, externs, fn := d.name, obj, frames } d.body
    [(d.arg, .unit, [])] { marks := #[(.block "entry", ([(d.arg, .unit, [])], d.body))] }
    "entry" #[] r rfl hr
  have hmr : ¬ (1 > maxRets) := by simp [maxRets]
  simp only [lowerDeclMarks, harg, hret, hu, hi, pure_bind, gt_iff_lt, Nat.not_lt_zero,
    ite_false, List.range_zero, List.map_nil]
  simp only [← gt_iff_lt, hmr, ite_false, buildFuncMarks, StateT.run]
  have hma : ∀ s : BState, markAt (.block "entry") ([(d.arg, .unit, [])], d.body) s =
      .ok ((), { s with
        marks := Array.push (s.marks.toList.filter fun m => m.1 != Node.block "entry").toArray
          (Node.block "entry", ([(d.arg, .unit, [])], d.body)) }) := fun _ => rfl
  rw [bind_ok (hmw _), bind_ok (hma _)]
  erw [hl]
  rfl

/-! ## The builder's invariants

Stated on IR blocks and functions in general (with `StackMap`'s use and def
sets), proved for the lowering of `Accepted0` code blocks. -/

open StackMap (instUses instDefs termUses termSuccs opRegs)

/-- **Every register read is defined before**: each instruction reads only
registers of `ds` or written by an earlier instruction, and so does the
terminator. -/
def DefBefore : List Reg → List Inst → Term → Prop
  | ds, [], t => ∀ x ∈ termUses t, x ∈ ds
  | ds, i :: is, t => (∀ x ∈ instUses i, x ∈ ds) ∧ DefBefore (instDefs i ++ ds) is t

/-- The registers the instructions write, in order. -/
def defsOf (is : List Inst) : List Reg := is.flatMap instDefs

/-- **The block list is well-formed**: each label once, every successor of a
terminator a label of the list. -/
def BlocksWF (bs : List Block) : Prop :=
  (bs.map (·.label)).Nodup ∧ ∀ b ∈ bs, ∀ l ∈ termSuccs b.term, l ∈ bs.map (·.label)

/-- **The placement trace names nodes of `f`**: block starts of its blocks
and return points of its calls. -/
def MarksIn (f : Func) (ms : Array (Node × Point)) : Prop :=
  ∀ m ∈ ms.toList, match m.1 with
    | .block l => l ∈ f.blocks.map (·.label)
    | .ret l i => ∃ b ∈ f.blocks, b.label = l ∧ ∃ h : i < b.insts.length, b.insts[i] matches .call ..

/-- Every register among the environment's words is in `ds`. -/
def EnvIn (env : Env) (ds : List Reg) : Prop :=
  ∀ v ∈ env, ∀ x ∈ v.2.2.flatMap opRegs, x ∈ ds

theorem atomV_regs {env : Env} {ds : List Reg} {a : At} {t : Ty} {ws : List Operand}
    (h : atomV env a = some (t, ws)) (he : EnvIn env ds) : ∀ x ∈ ws.flatMap opRegs, x ∈ ds := by
  cases a with
  | var y =>
    simp only [atomV, Option.map_eq_some_iff] at h
    obtain ⟨⟨z, u, vs⟩, hf, hv⟩ := h
    cases hv
    exact he _ (List.mem_of_find?_eq_some hf)
  | lit n =>
    simp only [atomV] at h
    split at h
    · cases h
    · cases h; simp [opRegs, imm]
  | unit => simp only [atomV, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp

theorem envIn_cons {env : Env} {ds : List Reg} (he : EnvIn env ds) (x : String) (t : Ty)
    {ws : List Operand} (hw : ∀ y ∈ ws.flatMap opRegs, y ∈ ds) : EnvIn ((x, t, ws) :: env) ds := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hw
  · exact he v hv

theorem envIn_mono {env : Env} {ds ds' : List Reg} (he : EnvIn env ds) (h : ∀ x ∈ ds, x ∈ ds') :
    EnvIn env ds' := fun v hv x hx => h x (he v hv x hx)

private theorem regs_one {p : Operand} {ds : List Reg} (h : ∀ x ∈ [p].flatMap opRegs, x ∈ ds) :
    ∀ x ∈ opRegs p, x ∈ ds := by simpa using h

/-- **`reads_defined`**: in the closed form, every register an instruction or
the `ret` reads is in `ds` (the registers defined on entry, which hold the
environment's words) or written by an earlier instruction. -/
theorem reads_defined :
    ∀ (e : Expr) (env : Env) (n : Nat) (ds : List Reg) (r : Res),
      lower0 env n e = some r → EnvIn env ds → DefBefore ds r.insts (.ret r.ret) := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n ds r hr he
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
          cases ht : scalar1 t <;> simp [ht, hr'] at hr
          subst hr
          exact ih _ n ds r' hr' (envIn_cons he x t (atomV_regs ha he))
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
          cases hr' : lower0 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            refine ⟨?_, ?_⟩
            · intro y hy
              simp only [instUses, List.mem_append] at hy
              rcases hy with hy | hy
              · exact regs_one (atomV_regs ha he) y hy
              · exact regs_one (atomV_regs hb he) y hy
            · refine ih _ (n + 1) _ r' hr' (envIn_cons ?_ x .int ?_)
              · exact envIn_mono he fun y hy => by simp [instDefs, hy]
              · simp [opRegs, instDefs]
    | _ => simp [lower0] at hr
  | ret a =>
    intro env n ds r hr he
    simp only [lower0] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      simp [ha] at hr
      subst hr
      exact atomV_regs ha he
  | _ => intro env n ds r hr; simp [lower0] at hr

/-- **`dests_nodup`**: in the closed form from counter `n`, the registers the
instructions write are pairwise distinct, each `regName x k` for a counter
`n ≤ k < r.next`. -/
theorem dests_nodup :
    ∀ (e : Expr) (env : Env) (n : Nat) (r : Res), lower0 env n e = some r →
      n ≤ r.next ∧ (defsOf r.insts).Nodup ∧
        ∀ d ∈ defsOf r.insts, ∃ x k, n ≤ k ∧ k < r.next ∧ d = regName x k := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r hr
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
          cases ht : scalar1 t <;> simp [ht, hr'] at hr
          subst hr
          exact ih _ n r' hr'
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
          cases hr' : lower0 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            obtain ⟨hle, hnd, hk⟩ := ih _ (n + 1) r' hr'
            dsimp only
            refine ⟨by omega, ?_, ?_⟩
            · simp only [defsOf, List.flatMap_cons, instDefs, List.singleton_append,
                List.nodup_cons]
              refine ⟨fun hm => ?_, hnd⟩
              obtain ⟨y, k, hk1, -, he⟩ := hk _ hm
              exact regName_ne (a := x) (b := y) (by omega) he
            · intro d hd
              simp only [defsOf, List.flatMap_cons, instDefs, List.singleton_append,
                List.mem_cons] at hd
              rcases hd with rfl | hd
              · exact ⟨x, n, Nat.le_refl n, by omega, rfl⟩
              · obtain ⟨y, k, hk1, hk2, he⟩ := hk d hd
                exact ⟨y, k, by omega, hk2, he⟩
    | _ => simp [lower0] at hr
  | ret a =>
    intro env n r hr
    simp only [lower0] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      simp [ha] at hr
      subst hr
      simp [defsOf]
  | _ => intro env n r hr; simp [lower0] at hr

/-- **The invariants of an `Accepted0` code block's lowering**: one function
(`func0`, trace `marks0`, by `lowerDeclMarks_accepted0`) whose block list is
well-formed, whose trace names its nodes, whose instructions write pairwise
distinct registers and read only registers written before them (it has no
parameter registers). -/
theorem accepted0_inv (name : Sym) {d : Decl} {r : Res}
    (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r) :
    BlocksWF (func0 name r).blocks ∧ MarksIn (func0 name r) (marks0 d) ∧
      (func0 name r).params = [] ∧
      (∀ b ∈ (func0 name r).blocks, DefBefore [] b.insts b.term ∧ (defsOf b.insts).Nodup) := by
  refine ⟨⟨by simp [func0], ?_⟩, ?_, rfl, ?_⟩
  · intro b hb l hl
    simp only [func0, List.mem_singleton] at hb
    subst hb
    simp [termSuccs] at hl
  · intro m hm
    simp only [marks0, List.mem_singleton] at hm
    subst hm
    simp [func0]
  · intro b hb
    simp only [func0, List.mem_singleton] at hb
    subst hb
    exact ⟨reads_defined _ _ 0 [] r hr (by intro v hv; simp at hv; subst hv; simp),
      (dests_nodup _ _ 0 r hr).2.1⟩

end Scc.Lower.Inv
