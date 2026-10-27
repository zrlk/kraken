/-
**The shape of an `Accepted1` code block's lowering** (ISA-neutral): what
the closed form `lowerC` (`Scc/Lower/InvC1.lean`) emits, for the emitters'
per-block proofs.

- `lowerC_atom_inv` … `lowerC_ret_inv`: one inversion lemma per
  constructor: the closed form of a `let`, `if` or `ret` from the closed
  form of its continuation (or branches), with or without the depth counter;
- `InstC`, `TermC`, `ResC`, `lowerC_resC`, `func1_shape`: the instructions
  are checked `+`, saturating `-`, a call of a code block, and (with the
  depth counter) the bracket's thread-pointer reads, depth loads and stores,
  increment and abort call; the terminators are a one-word `ret`, an `if`'s
  `br .eq`, the bracket's `br .ugt` and the abort block's `unreachable`;
  every operand is a register or an immediate below `2^63` (`OpOk`, from
  the environment's `EnvOk`);
- `allInsts`, `callsC`, `lowerC_calls`, `func1_calls`: the number of `call`s
  in the function's instructions, in block order;
- `LabIn`, `lowerC_labels`, `blocksWF_func1`: the labels of the later blocks
  are `then`/`else`/`deep`/`call` labels named from counters between the
  start and the final one, pairwise distinct and not `entry`; every branch
  target is a block of the function (`BlocksWF`).
-/
import Scc.Lower.InvC1

namespace Spike.Lib.LowerShape

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Scc.IR.StackMap (termSuccs)

/-! ## Inversion -/

theorem lowerC_atom_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x : String} {a : At}
    {e : Expr} {r : Res1} (hr : lowerC cx env n l k (.let_ x (.atom a) e) = some r) :
    ∃ t w r', atomV env a = some (t, [w]) ∧ scalar1 t = true ∧ lowerC cx ((x, t, [w]) :: env) n l k e = some r' ∧
      r = { r' with marked := regsOf [w] ++ r'.marked } := by
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
      exact ⟨t, w, r', rfl, ht, hr', hr.symm⟩

theorem lowerC_add_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x : String} {a b : At}
    {e : Expr} {r : Res1} (hr : lowerC cx env n l k (.let_ x (.add a b) e) = some r) :
    ∃ ta p tb q r', atomV env a = some (ta, [p]) ∧ atomV env b = some (tb, [q]) ∧
      lowerC cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) e = some r' ∧
      r = { r' with insts := .addChk (regName x n) p q :: r'.insts, marked := regName x n :: r'.marked } := by
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
        exact ⟨t, p, t', q, r', rfl, rfl, rfl, hr.symm⟩

theorem lowerC_sub_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x : String} {a b : At}
    {e : Expr} {r : Res1} (hr : lowerC cx env n l k (.let_ x (.sub a b) e) = some r) :
    ∃ ta p tb q r', atomV env a = some (ta, [p]) ∧ atomV env b = some (tb, [q]) ∧
      lowerC cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) e = some r' ∧
      r = { r' with insts := .subSat (regName x n) p q :: r'.insts, marked := regName x n :: r'.marked } := by
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
        exact ⟨t, p, t', q, r', rfl, rfl, rfl, hr.symm⟩

/-- **A call's closed form**: the callee is a code block of the program
returning an `Int`, not an extern; without the depth counter one `call`
in the open block, with it the bracket (`depthPre`, `depthTerm`,
`deepBlock`, `callPost`) and the continuation in block `call{n+5}`. -/
theorem lowerC_call_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x g : String}
    {is : List String} {a : At} {ts : List Ty} {e : Expr} {r : Res1}
    (hr : lowerC cx env n l k (.let_ x (.call g is a ts) e) = some r) :
    ∃ dg t w, cx.externs.find? (·.1 == g) = none ∧ cx.prog.find? (·.name == g) = some dg ∧
      dg.retTy = .int ∧ atomV env a = some (t, [w]) ∧
      ((cx.frames = none ∧ ∃ r', lowerC cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1) l (k + 1) e = some r' ∧
          r = { r' with insts := .call [regName "r" n] (Names.user g) [w] :: r'.insts,
                        marked := regName "r" n :: r'.marked,
                        marks := [(.ret l k, (env, .let_ x (.call g is a ts) e)),
                          (.ret l k, ((x, .int, [.reg (regName "r" n)]) :: env, e))] ++ r'.marks }) ∨
       (∃ fr r', cx.frames = some fr ∧
          lowerC cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 7) (labName "call" (n + 5)) 4 e = some r' ∧
          r = { insts := depthPre n, term := depthTerm fr n,
                blocks := deepBlock n :: ⟨labName "call" (n + 5), callPost g w n ++ r'.insts, r'.term⟩ :: r'.blocks,
                next := r'.next, marked := regName "depth" (n + 2) :: regName "r" n :: r'.marked,
                marks := [(.block (labName "deep" (n + 4)), (env, .let_ x (.call g is a ts) e)),
                  (.ret (labName "deep" (n + 4)) 0, (env, .let_ x (.call g is a ts) e)),
                  (.block (labName "call" (n + 5)), (env, .let_ x (.call g is a ts) e)),
                  (.ret (labName "call" (n + 5)) 1, (env, .let_ x (.call g is a ts) e)),
                  (.ret (labName "call" (n + 5)) 1, ((x, .int, [.reg (regName "r" n)]) :: env, e))] ++ r'.marks,
                here := r'.here })) := by
  simp only [lowerC] at hr
  cases hx : (cx.externs.find? (·.1 == g)).isNone with
  | false => simp [hx] at hr
  | true =>
  have hx' : cx.externs.find? (·.1 == g) = none := Option.isNone_iff_eq_none.mp hx
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
  refine ⟨dg, t, w, hx', rfl, by simpa using hrt, rfl, ?_⟩
  cases hf : cx.frames with
  | none =>
    cases hr' : lowerC cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1) l (k + 1) e with
    | none => simp [hf, hr'] at hr
    | some r' =>
      simp [hf, hr'] at hr
      exact .inl ⟨rfl, r', rfl, hr.symm⟩
  | some fr =>
    cases hr' : lowerC cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 7) (labName "call" (n + 5)) 4 e with
    | none => simp [hf, hr'] at hr
    | some r' =>
      simp [hf, hr'] at hr
      exact .inr ⟨fr, r', rfl, rfl, hr.symm⟩

theorem lowerC_ifeq_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {a b : At}
    {yes no : Expr} {r : Res1} (hr : lowerC cx env n l k (.ifeq a b yes no) = some r) :
    ∃ ta p tb q ry rn, atomV env a = some (ta, [p]) ∧ atomV env b = some (tb, [q]) ∧
      lowerC cx env (n + 2) (labName "then" n) 0 yes = some ry ∧
      lowerC cx env ry.next (labName "else" (n + 1)) 0 no = some rn ∧
      r = { insts := [], term := .br .eq p q (labName "then" n) (labName "else" (n + 1)),
            blocks := ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
              ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks,
            next := rn.next, marked := ry.marked ++ rn.marked,
            marks := [(.block (labName "then" n), (env, .ifeq a b yes no)), (.block (labName "then" n), (env, yes))] ++
              ry.marks ++ [(.block (labName "else" (n + 1)), ry.here), (.block (labName "else" (n + 1)), (env, no))] ++
              rn.marks,
            here := rn.here } := by
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
          exact ⟨t, p, t', q, ry, rn, rfl, rfl, by first | exact hy | rfl, by first | exact hn | rfl,
            by rw [← hr]; simp⟩

theorem lowerC_ret_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {a : At} {r : Res1}
    (hr : lowerC cx env n l k (.ret a) = some r) :
    ∃ t ws, atomV env a = some (t, ws) ∧
      r = { insts := [], term := .ret ws, blocks := [], next := n, marked := [], marks := [],
            here := (env, .ret a) } := by
  simp only [lowerC] at hr
  cases ha : atomV env a with
  | none => simp [ha] at hr
  | some v =>
    obtain ⟨t, ws⟩ := v
    simp [ha] at hr
    exact ⟨t, ws, rfl, hr.symm⟩

/-- **Only `let`s of an atom, `+`, `-` or a call, `if` and `ret` have a
closed form.** -/
theorem lowerC_cases {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {e : Expr} {r : Res1}
    (hr : lowerC cx env n l k e = some r) :
    (∃ x a e', e = .let_ x (.atom a) e') ∨ (∃ x a b e', e = .let_ x (.add a b) e') ∨
      (∃ x a b e', e = .let_ x (.sub a b) e') ∨ (∃ x g is a ts e', e = .let_ x (.call g is a ts) e') ∨
      (∃ a b yes no, e = .ifeq a b yes no) ∨ (∃ a, e = .ret a) := by
  cases e with
  | let_ x op e' =>
    cases op with
    | atom a => exact .inl ⟨_, _, _, rfl⟩
    | add a b => exact .inr (.inl ⟨_, _, _, _, rfl⟩)
    | sub a b => exact .inr (.inr (.inl ⟨_, _, _, _, rfl⟩))
    | call g is a ts => exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, rfl⟩)))
    | _ => simp [lowerC] at hr
  | ifeq a b yes no => exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl⟩))))
  | ret a => exact .inr (.inr (.inr (.inr (.inr ⟨_, rfl⟩))))
  | _ => simp [lowerC] at hr

/-! ## The instructions and terminators -/

/-- **An operand of the body**: a register, or an immediate below `2^63`
(`body1`'s literals; not in general a sign-extended 32-bit one). -/
def OpOk : Operand → Prop
  | .reg _ => True
  | .imm v => ∃ n, n < 2 ^ 63 ∧ v = UInt64.ofNat n

/-- **The instructions `lowerC` emits**: checked `+`, saturating `-`, a
one-result one-argument call of a code block (body operands, `OpOk`), and
the depth counter's bracket: a thread-pointer read, a 64-bit plain load and
store, the depth's increment and the stack abort's call. -/
inductive InstC : Inst → Prop
  | addChk (d : Reg) (p q : Operand) : OpOk p → OpOk q → InstC (.addChk d p q)
  | subSat (d : Reg) (p q : Operand) : OpOk p → OpOk q → InstC (.subSat d p q)
  | call (d : Reg) (g : String) (w : Operand) : OpOk w → InstC (.call [d] (Names.user g) [w])
  | getTp (d : Reg) : InstC (.getTp d)
  | load (d : Reg) (a : Addr) : InstC (.load .plain .w64 d a)
  | store (a : Addr) (v : Reg) : InstC (.store .plain .w64 a (.reg v))
  | inc (d s : Reg) : InstC (.bin .add d (.reg s) (imm 1))
  | abort : InstC (.call [] Names.abort [imm AbortKind.stack.code])

/-- **The terminators `lowerC` emits** with depth limit `frames`: a one-word
`ret`, an `if`'s `br .eq` (body operands, `OpOk`), the bracket's `br .ugt`
against the limit, and the abort block's `unreachable`. -/
inductive TermC (frames : Option Nat) : Term → Prop
  | ret (w : Operand) : OpOk w → TermC frames (.ret [w])
  | br (p q : Operand) (t f : Label) : OpOk p → OpOk q → TermC frames (.br .eq p q t f)
  | depth (d : Reg) (fr : Nat) (t f : Label) : frames = some fr → TermC frames (.br .ugt (.reg d) (imm fr) t f)
  | unreachable : TermC frames .unreachable

/-- Every word of the environment is a body operand (`OpOk`). -/
def EnvOk (env : Env) : Prop := ∀ v ∈ env, ∀ o ∈ v.2.2, OpOk o

theorem envOk_cons {env : Env} (h : EnvOk env) (x : String) (t : Ty) {ws : List Operand}
    (hw : ∀ o ∈ ws, OpOk o) : EnvOk ((x, t, ws) :: env) := by
  intro v hv o ho
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hw o ho
  · exact h v hv o ho

theorem envOk_env1 (d : Decl) : EnvOk (env1 d) := by
  intro v hv o ho
  simp only [env1, List.mem_cons, List.mem_nil_iff, or_false] at hv
  subst hv
  simp only [params1R, List.mem_map] at ho
  obtain ⟨r, -, rfl⟩ := ho
  trivial

/-- **An atom of the body has body operands**. -/
theorem atomV_ok {scope : List String} {env : Env} {a : At} {t : Ty} {ws : List Operand}
    (ha : atom0 scope a = true) (he : EnvOk env) (h : atomV env a = some (t, ws)) : ∀ o ∈ ws, OpOk o := by
  cases a with
  | var x =>
    simp only [atomV, Option.map_eq_some_iff] at h
    obtain ⟨⟨y, u, vs⟩, hf, hv⟩ := h
    cases hv
    exact he _ (List.mem_of_find?_eq_some hf)
  | lit n =>
    have hn : n < 2 ^ 63 := by simpa [atom0] using ha
    have : ¬ n ≥ 2 ^ 64 := by omega
    simp only [atomV, this, ite_false, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    intro o ho
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
    subst ho
    exact ⟨n, hn, rfl⟩
  | unit => simp [atom0] at ha

/-- A block of `lowerC`'s shape. -/
def BlockC (frames : Option Nat) (b : Block) : Prop := (∀ i ∈ b.insts, InstC i) ∧ TermC frames b.term

/-- A closed form of `lowerC`'s shape: the open block's instructions and
terminator, and every later block. -/
def ResC (frames : Option Nat) (r : Res1) : Prop :=
  (∀ i ∈ r.insts, InstC i) ∧ TermC frames r.term ∧ ∀ b ∈ r.blocks, BlockC frames b

/-- **`lowerC` emits only `InstC` instructions and `TermC` terminators** on
an `Accepted1` body whose free variables are bound to scalar words (so the
`ret` returns one word). -/
theorem lowerC_resC (cx : Scc.Lower.Ctx) {earlier : List String} :
    ∀ (e : Expr) (scope : List String) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → body1 earlier scope e = true → EnvScalar scope env → EnvOk env →
        ResC cx.frames r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n l k r hr hb hs he
    cases op with
    | atom a =>
      obtain ⟨t, w, r', ha, ht, hr', rfl⟩ := lowerC_atom_inv hr
      simp only [body1, atom1, Bool.and_eq_true] at hb
      exact ih _ _ _ _ _ r' hr' hb.2 (envScalar_cons hs x w ht) (envOk_cons he x t (atomV_ok hb.1 he ha))
    | add a b =>
      obtain ⟨_, p, _, q, r', ha, hb', hr', rfl⟩ := lowerC_add_inv hr
      simp only [body1, atom1, Bool.and_eq_true] at hb
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ _ _ hr' hb.2 (envScalar_cons hs x _ rfl)
        (envOk_cons he x _ (by simp [OpOk]))
      refine ⟨fun i hi => ?_, h2, h3⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact .addChk _ _ _ (atomV_ok hb.1.1 he ha _ (by simp)) (atomV_ok hb.1.2 he hb' _ (by simp))
      · exact h1 i hi
    | sub a b =>
      obtain ⟨_, p, _, q, r', ha, hb', hr', rfl⟩ := lowerC_sub_inv hr
      simp only [body1, atom1, Bool.and_eq_true] at hb
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ _ _ hr' hb.2 (envScalar_cons hs x _ rfl)
        (envOk_cons he x _ (by simp [OpOk]))
      refine ⟨fun i hi => ?_, h2, h3⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · exact .subSat _ _ _ (atomV_ok hb.1.1 he ha _ (by simp)) (atomV_ok hb.1.2 he hb' _ (by simp))
      · exact h1 i hi
    | call g is a ts =>
      obtain ⟨dg, t, w, -, -, -, ha, h⟩ := lowerC_call_inv hr
      simp only [body1, callee1, atom1, Bool.and_eq_true] at hb
      have hw : OpOk w := atomV_ok hb.1.2 he ha _ (by simp)
      have hs' := envScalar_cons hs x (t := .int) (.reg (regName "r" n)) rfl
      have he' := envOk_cons he x .int (ws := [.reg (regName "r" n)]) (by simp [OpOk])
      rcases h with ⟨-, r', hr', rfl⟩ | ⟨fr, r', hf, hr', rfl⟩
      · obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ _ _ hr' hb.2 hs' he'
        refine ⟨fun i hi => ?_, h2, h3⟩
        rcases List.mem_cons.mp hi with rfl | hi
        · exact .call _ _ _ hw
        · exact h1 i hi
      · obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ _ _ hr' hb.2 hs' he'
        refine ⟨fun i hi => ?_, ?_, fun b hb' => ?_⟩
        · simp only [depthPre, List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl | rfl
          · exact .getTp _
          · exact .load _ _
          · exact .inc _ _
        · exact .depth _ _ _ _ hf
        · simp only [List.mem_cons] at hb'
          rcases hb' with rfl | rfl | hb'
          · exact ⟨fun i hi => by simp [deepBlock] at hi; subst hi; exact .abort, .unreachable⟩
          · refine ⟨fun i hi => ?_, h2⟩
            rcases List.mem_append.mp hi with hi | hi
            · simp only [callPost, List.mem_cons, List.mem_nil_iff, or_false] at hi
              rcases hi with rfl | rfl | rfl | rfl
              · exact .store _ _
              · exact .call _ _ _ hw
              · exact .getTp _
              · exact .store _ _
            · exact h1 i hi
          · exact h3 b hb'
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro scope env n l k r hr hb hs he
    obtain ⟨_, p, _, q, ry, rn, ha, hb', hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    simp only [body1, atom1, Bool.and_eq_true] at hb
    obtain ⟨y1, y2, y3⟩ := ihy _ _ _ _ _ _ hy hb.1.2 hs he
    obtain ⟨n1, n2, n3⟩ := ihn _ _ _ _ _ _ hn hb.2 hs he
    refine ⟨by simp, .br _ _ _ _ (atomV_ok hb.1.1.1 he ha _ (by simp)) (atomV_ok hb.1.1.2 he hb' _ (by simp)),
      fun b hb' => ?_⟩
    simp only [List.mem_cons, List.mem_append] at hb'
    rcases hb' with (rfl | hb') | rfl | hb'
    · exact ⟨y1, y2⟩
    · exact y3 b hb'
    · exact ⟨n1, n2⟩
    · exact n3 b hb'
  | ret a =>
    intro scope env n l k r hr hb hs he
    obtain ⟨t, ws, ha, rfl⟩ := lowerC_ret_inv hr
    have ha0 : atom0 scope a = true := by simpa [body1] using hb
    obtain ⟨t', w, ha', -⟩ := atomV_of_atom0 ha0 hs
    have hok := atomV_ok ha0 he ha
    rw [ha] at ha'
    cases ha'
    exact ⟨by simp, .ret _ (hok _ (by simp)), by simp⟩
  | _ => intro scope env n l k r hr; simp [lowerC] at hr

/-- **The shape of an `Accepted1` code block's function**: `func1` of the
closed form of its body has `lowerC`'s instructions and terminators. -/
theorem func1_shape (cx : Scc.Lower.Ctx) {earlier : List String} {d : Decl} (hd : decl1 earlier d = true)
    {r : Res1} (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    ∀ b ∈ (func1 name (params1R d) r).blocks, BlockC cx.frames b := by
  obtain ⟨harg, -, hb⟩ := decl1_shape hd
  obtain ⟨h1, h2, h3⟩ := lowerC_resC cx d.body _ _ _ _ _ r hr hb (envScalar_env1 harg) (envOk_env1 d)
  intro b hb'
  simp only [func1, List.mem_cons] at hb'
  rcases hb' with rfl | hb'
  · exact ⟨h1, h2⟩
  · exact h3 b hb'

/-! ## Calls -/

/-- A `call` instruction. -/
def isCall : Inst → Bool
  | .call .. => true
  | _ => false

/-- A closed form's instructions, in block order: the open block's, then
each later block's. -/
def allInsts (r : Res1) : List Inst := r.insts ++ r.blocks.flatMap (·.insts)

/-- **The `call`s `lowerC` emits on `e`** with depth limit `frames`: one per
call of a code block, two with the depth counter (the stack abort's in
`deepBlock`). -/
def callsC (frames : Option Nat) : Expr → Nat
  | .let_ _ (.call ..) e => callsC frames e + (if frames.isSome then 2 else 1)
  | .let_ _ _ e => callsC frames e
  | .ifeq _ _ yes no => callsC frames yes + callsC frames no
  | _ => 0

/-- **The number of `call`s of a closed form** is `callsC`. -/
theorem lowerC_calls (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → (allInsts r).countP isCall = callsC cx.frames e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | atom a =>
      obtain ⟨t, w, r', -, -, hr', rfl⟩ := lowerC_atom_inv hr
      simpa [allInsts, callsC] using ih _ _ _ _ _ hr'
    | add a b =>
      obtain ⟨-, p, -, q, r', -, -, hr', rfl⟩ := lowerC_add_inv hr
      simpa [allInsts, callsC, isCall] using ih _ _ _ _ _ hr'
    | sub a b =>
      obtain ⟨-, p, -, q, r', -, -, hr', rfl⟩ := lowerC_sub_inv hr
      simpa [allInsts, callsC, isCall] using ih _ _ _ _ _ hr'
    | call g is a ts =>
      obtain ⟨dg, t, w, -, -, -, -, h⟩ := lowerC_call_inv hr
      rcases h with ⟨hf, r', hr', rfl⟩ | ⟨fr, r', hf, hr', rfl⟩
      · have := ih _ _ _ _ _ hr'
        rw [hf] at this
        simp only [allInsts, List.countP_append, List.countP_cons, List.cons_append] at this ⊢
        simp [callsC, isCall, hf]; omega
      · have := ih _ _ _ _ _ hr'
        rw [hf] at this
        simp only [allInsts, List.countP_append] at this ⊢
        simp [callsC, isCall, hf, depthPre, deepBlock, callPost, List.countP_append, List.countP_cons]; omega
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr
    obtain ⟨-, p, -, q, ry, rn, -, -, hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    have hy' := ihy _ _ _ _ _ hy
    have hn' := ihn _ _ _ _ _ hn
    simp only [allInsts, List.countP_append] at hy' hn' ⊢
    simp [callsC, List.countP_append, ← hy', ← hn']; omega
  | ret a =>
    intro env n l k r hr
    obtain ⟨t, ws, -, rfl⟩ := lowerC_ret_inv hr
    simp [allInsts, callsC]
  | _ => intro env n l k r hr; simp [lowerC] at hr

/-- **The number of `call`s of an `Accepted1` code block's function**, in
its blocks in order, is `callsC` of its body. -/
theorem func1_calls (cx : Scc.Lower.Ctx) {d : Decl} {r : Res1}
    (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    ((func1 name (params1R d) r).blocks.flatMap (·.insts)).countP isCall = callsC cx.frames d.body := by
  rw [← lowerC_calls cx _ _ _ _ _ _ hr]
  simp [func1, allInsts]

/-! ## Labels -/

/-- The hints of the labels `lowerC` names (`labName`). -/
def LabHint (h : String) : Prop := h = "then" ∨ h = "else" ∨ h = "deep" ∨ h = "call"

/-- A label's trailing digits, reversed. -/
def labNum (l : String) : List Char := l.toList.reverse.takeWhile Char.isDigit

theorem labNum_labName {h : String} (hh : LabHint h) (n : Nat) :
    labNum (labName h n) = (Nat.toDigits 10 n).reverse := by
  have e : (labName h n).toList = h.toList ++ Nat.toDigits 10 n := by
    simp [labName, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr]; rfl
  simp only [labNum, e, List.reverse_append]
  rw [List.takeWhile_append_of_pos (fun c hc =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) (List.mem_reverse.mp hc))]
  have : List.takeWhile Char.isDigit h.toList.reverse = [] := by
    rcases hh with rfl | rfl | rfl | rfl <;> decide
  simp [this]

/-- **Labels named from different counters differ** (whatever the hints):
the counter is the label's trailing digits. -/
theorem labName_ne {h h' : String} (hh : LabHint h) (hh' : LabHint h') {n m : Nat} (hnm : n ≠ m) :
    labName h n ≠ labName h' m := by
  intro he
  apply hnm
  have := congrArg labNum he
  rw [labNum_labName hh, labNum_labName hh', List.reverse_inj] at this
  rw [← Nat.ofDigitChars_ten_toDigits (n := n), ← Nat.ofDigitChars_ten_toDigits (n := m), this]

/-- **A named label is not `entry`** (which has no trailing digits). -/
theorem labName_ne_entry {h : String} (hh : LabHint h) (n : Nat) : labName h n ≠ "entry" := by
  intro he
  have := congrArg labNum he
  rw [labNum_labName hh] at this
  have h2 : labNum "entry" = [] := by decide
  rw [h2, List.reverse_eq_nil_iff] at this
  exact Nat.toDigits_ne_nil this

/-- A label `lowerC` names from a counter in `[n, m)`. -/
def LabIn (n m : Nat) (l : Label) : Prop := ∃ h k, LabHint h ∧ n ≤ k ∧ k < m ∧ l = labName h k

theorem LabIn.mono {n m n' m' : Nat} {l : Label} (h : LabIn n m l) (h1 : n' ≤ n) (h2 : m ≤ m') : LabIn n' m' l := by
  obtain ⟨h, k, hh, hk1, hk2, rfl⟩ := h
  exact ⟨h, k, hh, by omega, by omega, rfl⟩

theorem LabIn.ne {n m n' m' : Nat} {l l' : Label} (h : LabIn n m l) (h' : LabIn n' m' l') (hm : m ≤ n') : l ≠ l' := by
  obtain ⟨h, k, hh, -, hk2, rfl⟩ := h
  obtain ⟨h', k', hh', hk1', -, rfl⟩ := h'
  exact labName_ne hh hh' (by omega)

theorem LabIn.ne_entry {n m : Nat} {l : Label} (h : LabIn n m l) : l ≠ "entry" := by
  obtain ⟨h, k, hh, -, -, rfl⟩ := h
  exact labName_ne_entry hh k

theorem labIn_labName {h : String} (hh : LabHint h) {n m k : Nat} (h1 : n ≤ k) (h2 : k < m) :
    LabIn n m (labName h k) := ⟨h, k, hh, h1, h2, rfl⟩

/-- The labels of a closed form's later blocks. -/
def labsOf (r : Res1) : List Label := r.blocks.map (·.label)

/-- **The labels of a closed form**: the later blocks' labels are pairwise
distinct, named from counters between the start and the final one; every
branch target of the open block or of a later block is a later block's
label. -/
structure Labs (n : Nat) (r : Res1) : Prop where
  nodup : (labsOf r).Nodup
  labIn : ∀ l ∈ labsOf r, LabIn n r.next l
  succ : ∀ l ∈ termSuccs r.term, l ∈ labsOf r
  succs : ∀ b ∈ r.blocks, ∀ l ∈ termSuccs b.term, l ∈ labsOf r

/-- **The labels of `lowerC`'s closed form** (`Labs`). -/
theorem lowerC_labels (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → Labs n r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | atom a =>
      obtain ⟨t, w, r', -, -, hr', rfl⟩ := lowerC_atom_inv hr
      have h := ih _ _ _ _ r' hr'
      exact ⟨h.nodup, h.labIn, h.succ, h.succs⟩
    | add a b | sub a b =>
      first
        | obtain ⟨-, p, -, q, r', -, -, hr', rfl⟩ := lowerC_add_inv hr
        | obtain ⟨-, p, -, q, r', -, -, hr', rfl⟩ := lowerC_sub_inv hr
      have h := ih _ _ _ _ _ hr'
      exact ⟨h.nodup, fun l hl => (h.labIn l hl).mono (by omega) (Nat.le_refl _), h.succ, h.succs⟩
    | call g is a ts =>
      obtain ⟨dg, t, w, -, -, -, -, h⟩ := lowerC_call_inv hr
      rcases h with ⟨-, r', hr', rfl⟩ | ⟨fr, r', -, hr', rfl⟩
      · have h := ih _ _ _ _ _ hr'
        exact ⟨h.nodup, fun l hl => (h.labIn l hl).mono (by omega) (Nat.le_refl _), h.succ, h.succs⟩
      · have h := ih _ _ _ _ _ hr'
        have hn := lowerC_next cx _ _ _ _ _ _ hr'
        have hd : LabHint "deep" := by simp [LabHint]
        have hc : LabHint "call" := by simp [LabHint]
        have h4 : LabIn n r'.next (labName "deep" (n + 4)) := labIn_labName hd (by omega) (by omega)
        have h5 : LabIn n r'.next (labName "call" (n + 5)) := labIn_labName hc (by omega) (by omega)
        have h4' : LabIn (n + 4) (n + 5) (labName "deep" (n + 4)) := labIn_labName hd (by omega) (by omega)
        have h5' : LabIn (n + 5) (n + 6) (labName "call" (n + 5)) := labIn_labName hc (by omega) (by omega)
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [labsOf, deepBlock, List.map_cons, List.nodup_cons, List.mem_cons, not_or]
          refine ⟨⟨h4'.ne h5' (by omega), fun hm => h4'.ne (h.labIn _ hm) (by omega) rfl⟩,
            fun hm => h5'.ne (h.labIn _ hm) (by omega) rfl, h.nodup⟩
        · intro l hl
          simp only [labsOf, deepBlock, List.map_cons, List.mem_cons] at hl
          rcases hl with rfl | rfl | hl
          · exact h4
          · exact h5
          · exact (h.labIn l hl).mono (by omega) (Nat.le_refl _)
        · intro l hl
          simp only [depthTerm, termSuccs, List.mem_cons, List.mem_nil_iff, or_false] at hl
          rcases hl with rfl | rfl <;> simp [labsOf, deepBlock]
        · intro b hb l hl
          simp only [List.mem_cons] at hb
          rcases hb with rfl | rfl | hb
          · simp [deepBlock, termSuccs] at hl
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h.succ l hl))
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h.succs b hb l hl))
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr
    obtain ⟨-, p, -, q, ry, rn, -, -, hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    have hy' := ihy _ _ _ _ _ hy
    have hn' := ihn _ _ _ _ _ hn
    have ny := lowerC_next cx _ _ _ _ _ _ hy
    have nn := lowerC_next cx _ _ _ _ _ _ hn
    have ht : LabHint "then" := by simp [LabHint]
    have he : LabHint "else" := by simp [LabHint]
    have h0 : LabIn n (n + 1) (labName "then" n) := labIn_labName ht (by omega) (by omega)
    have h1 : LabIn (n + 1) (n + 2) (labName "else" (n + 1)) := labIn_labName he (by omega) (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [labsOf, List.map_cons, List.map_append]
      refine List.nodup_append.mpr ⟨List.nodup_cons.mpr ⟨fun hm => h0.ne (hy'.labIn _ hm) (by omega) rfl,
        hy'.nodup⟩, List.nodup_cons.mpr ⟨fun hm => h1.ne (hn'.labIn _ hm) (by omega) rfl, hn'.nodup⟩, ?_⟩
      intro u hu v hv
      have hu' : LabIn n ry.next u := by
        rcases List.mem_cons.mp hu with rfl | hu
        · exact h0.mono (Nat.le_refl _) (by omega)
        · exact (hy'.labIn u hu).mono (by omega) (Nat.le_refl _)
      have hv' : LabIn (n + 1) rn.next v := by
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h1.mono (Nat.le_refl _) (by omega)
        · exact (hn'.labIn v hv).mono (by omega) (Nat.le_refl _)
      rcases List.mem_cons.mp hu with rfl | hu
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact h0.ne h1 (by omega)
        · exact h0.ne (hn'.labIn v hv) (by omega)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact fun he' => h1.ne (hy'.labIn u hu) (by omega) he'.symm |>.elim
        · exact (hy'.labIn u hu).ne (hn'.labIn v hv) (Nat.le_refl _)
    · simp only [labsOf, List.map_cons, List.map_append]
      intro u hu
      simp only [List.mem_append, List.mem_cons] at hu
      rcases hu with (rfl | hu) | rfl | hu
      · exact h0.mono (Nat.le_refl _) (by omega)
      · exact (hy'.labIn u hu).mono (by omega) (by omega)
      · exact h1.mono (by omega) (by omega)
      · exact (hn'.labIn u hu).mono (by omega) (Nat.le_refl _)
    · simp only [labsOf, List.map_cons, List.map_append]
      intro u hu
      simp only [termSuccs, List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl <;> simp
    · simp only [labsOf, List.map_cons, List.map_append]
      intro b hb u hu
      simp only [List.mem_append, List.mem_cons] at hb
      rcases hb with (rfl | hb) | rfl | hb
      · have := hy'.succ u hu; simp only [labsOf, List.mem_map] at this; simp [this]
      · have := hy'.succs b hb u hu; simp only [labsOf, List.mem_map] at this; simp [this]
      · have := hn'.succ u hu; simp only [labsOf, List.mem_map] at this; simp [this]
      · have := hn'.succs b hb u hu; simp only [labsOf, List.mem_map] at this; simp [this]
  | ret a =>
    intro env n l k r hr
    obtain ⟨t, ws, -, rfl⟩ := lowerC_ret_inv hr
    exact ⟨by simp [labsOf], by simp [labsOf], by simp [termSuccs], by simp⟩
  | _ => intro env n l k r hr; simp [lowerC] at hr

/-- **The blocks of an `Accepted1` code block's function are well formed**
(`BlocksWF`): `entry` and the later blocks' labels are pairwise distinct,
and every branch target is a block of the function. -/
theorem blocksWF_func1 (cx : Scc.Lower.Ctx) {d : Decl} {r : Res1}
    (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    BlocksWF (func1 name (params1R d) r).blocks := by
  have h := lowerC_labels cx _ _ _ _ _ _ hr
  refine ⟨?_, ?_⟩
  · simp only [func1, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => (h.labIn _ hm).ne_entry rfl, h.nodup⟩
  · intro b hb l hl
    simp only [func1, List.mem_cons] at hb
    simp only [func1, List.map_cons, List.mem_cons]
    rcases hb with rfl | hb
    · exact .inr (h.succ l hl)
    · exact .inr (h.succs b hb l hl)

/-- The entry block of an `Accepted1` code block's function is `entry`. -/
theorem func1_entry (name : Sym) (ps : List Reg) (r : Res1) :
    (func1 name ps r).blocks.head? = some ⟨"entry", r.insts, r.term⟩ := rfl

end Spike.Lib.LowerShape
