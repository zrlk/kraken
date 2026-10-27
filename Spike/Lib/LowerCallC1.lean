/-
**The call sites of an `Accepted1` code block's lowering** (ISA-neutral),
with the depth counter (`cx.frames = some fr`), for the emitters' per-block
proofs of calls.

- `NoCall`, `Callee`, `callBlk`, `CallBlk`: every block of `func1` of the
  closed form `lowerC` is the bracket's abort block `deepBlock n` (its only
  call is the stack abort's), a block without a `call`, or a call block
  `call{n+5}`: `callPost g w n` (store the new depth, `call [r%n] (wc_g)
  [w]`, read the thread pointer, store the old depth back) and then
  instructions without a `call`; `g` is a code block of the program
  returning an `Int`, not an extern, and `w` a body operand (`OpOk`);
- `CallRes`, `lowerC_callRes`, `func1_callBlk`, `func1_bracket`: every call
  block `call{n+5}` has the bracket before it: the abort block `deepBlock n`
  and a block ending with `depthPre n` and terminated by `depthTerm fr n`.
-/
import Spike.Lib.LowerShapeC1

namespace Spike.Lib.LowerCall

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Spike.Lib.LowerShape

/-! ## Blocks with calls -/

/-- Instructions without a `call`. -/
def NoCall (is : List Inst) : Prop := ∀ i ∈ is, isCall i = false

theorem noCall_nil : NoCall [] := by simp [NoCall]

theorem noCall_cons {i : Inst} {is : List Inst} (hi : isCall i = false) (h : NoCall is) : NoCall (i :: is) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj
  · exact hi
  · exact h j hj

theorem noCall_depthPre (n : Nat) : NoCall (depthPre n) := by simp [NoCall, depthPre, isCall]

/-- `callPost` has a `call` (its instruction 1). -/
theorem not_noCall_callPost (g : String) (w : Operand) (n : Nat) (rest : List Inst) :
    ¬ NoCall (callPost g w n ++ rest) := by
  intro h
  have := h (.call [regName "r" n] (Names.user g) [w]) (List.mem_append_left _ (by simp [callPost]))
  simp [isCall] at this

/-- `g` is a code block of `cx.prog` returning an `Int`, not an extern. -/
def Callee (cx : Scc.Lower.Ctx) (g : String) : Prop :=
  cx.externs.find? (·.1 == g) = none ∧ ∃ dg, cx.prog.find? (·.name == g) = some dg ∧ dg.retTy = .int

/-- The bracket's call block `call{n+5}`: `callPost g w n`, then `rest`,
terminated by `t`. -/
abbrev callBlk (n : Nat) (g : String) (w : Operand) (rest : List Inst) (t : Term) : Block :=
  ⟨labName "call" (n + 5), callPost g w n ++ rest, t⟩

/-- A block without a `call` is no call block. -/
theorem callBlk_ne {n : Nat} {g : String} {w : Operand} {rest : List Inst} {t : Term} {b : Block}
    (hb : NoCall b.insts) : callBlk n g w rest t ≠ b := by
  rintro rfl
  exact not_noCall_callPost g w n rest hb

/-- **A block of `lowerC`'s shape with the depth counter, by its calls**:
the abort block, a block without a `call`, or a call block whose user call
(instruction 1, result `r%n`, argument `w`) is its only one. -/
inductive CallBlk (cx : Scc.Lower.Ctx) : Block → Prop
  | deep (n : Nat) : CallBlk cx (deepBlock n)
  | plain (b : Block) : NoCall b.insts → CallBlk cx b
  | call (n : Nat) (g : String) (w : Operand) (rest : List Inst) (t : Term) :
      Callee cx g → OpOk w → NoCall rest → CallBlk cx (callBlk n g w rest t)

/-- **A closed form's calls** with depth limit `fr`: the open block has no
`call`, every later block is a `CallBlk`, and every call block `call{n+5}`
has the abort block `deepBlock n` and, in the open block or a later one,
the bracket's start `depthPre n` and test `depthTerm fr n`. -/
structure CallRes (cx : Scc.Lower.Ctx) (fr : Nat) (r : Res1) : Prop where
  insts : NoCall r.insts
  blocks : ∀ b ∈ r.blocks, CallBlk cx b
  bracket : ∀ n g w rest t, callBlk n g w rest t ∈ r.blocks → deepBlock n ∈ r.blocks ∧
    ((∃ pre, r.insts = pre ++ depthPre n ∧ r.term = depthTerm fr n) ∨
      ∃ b ∈ r.blocks, ∃ pre, b.insts = pre ++ depthPre n ∧ b.term = depthTerm fr n)

/-- **The calls of `lowerC`'s closed form with the depth counter**
(`CallRes`), on an `Accepted1` body whose free variables are bound to
scalar body operands. -/
theorem lowerC_callRes (cx : Scc.Lower.Ctx) {fr : Nat} (hf : cx.frames = some fr) {earlier : List String} :
    ∀ (e : Expr) (scope : List String) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → body1 earlier scope e = true → EnvScalar scope env → EnvOk env →
        CallRes cx fr r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n l k r hr hb hs he
    cases op with
    | atom a =>
      obtain ⟨t, w, r', ha, ht, hr', rfl⟩ := lowerC_atom_inv hr
      simp only [body1, atom1, Bool.and_eq_true] at hb
      have h := ih _ _ _ _ _ r' hr' hb.2 (envScalar_cons hs x w ht) (envOk_cons he x t (atomV_ok hb.1 he ha))
      exact ⟨h.insts, h.blocks, h.bracket⟩
    | add a b | sub a b =>
      first
        | obtain ⟨_, p, _, q, r', ha, hb', hr', rfl⟩ := lowerC_add_inv hr
        | obtain ⟨_, p, _, q, r', ha, hb', hr', rfl⟩ := lowerC_sub_inv hr
      simp only [body1, atom1, Bool.and_eq_true] at hb
      have h := ih _ _ _ _ _ _ hr' hb.2 (envScalar_cons hs x _ rfl) (envOk_cons he x _ (by simp [OpOk]))
      refine ⟨noCall_cons (by simp [isCall]) h.insts, h.blocks, fun m g w rest t hm => ?_⟩
      obtain ⟨h1, h2⟩ := h.bracket m g w rest t hm
      refine ⟨h1, h2.imp (fun ⟨pre, hp, ht⟩ => ⟨_ :: pre, by rw [List.cons_append, ← hp], ht⟩) id⟩
    | call g is a ts =>
      obtain ⟨dg, t, w, hx, hd, hrt, ha, h⟩ := lowerC_call_inv hr
      simp only [body1, callee1, atom1, Bool.and_eq_true] at hb
      have hw : OpOk w := atomV_ok hb.1.2 he ha _ (by simp)
      have hs' := envScalar_cons hs x (t := .int) (.reg (regName "r" n)) rfl
      have he' := envOk_cons he x .int (ws := [.reg (regName "r" n)]) (by simp [OpOk])
      rcases h with ⟨hn, -⟩ | ⟨fr', r', hf', hr', rfl⟩
      · rw [hf] at hn; cases hn
      rw [hf] at hf'
      cases hf'
      have h := ih _ _ _ _ _ _ hr' hb.2 hs' he'
      have hc : Callee cx g := ⟨hx, dg, hd, hrt⟩
      refine ⟨noCall_depthPre n, ?_, ?_⟩
      · intro b hb'
        simp only [List.mem_cons] at hb'
        rcases hb' with rfl | rfl | hb'
        · exact .deep n
        · exact .call n g w r'.insts r'.term hc hw h.insts
        · exact h.blocks b hb'
      · intro m g' w' rest t' hm
        simp only [List.mem_cons] at hm
        rcases hm with hm | hm | hm
        · simp [callBlk, deepBlock, callPost] at hm
        · have hl := congrArg Block.label hm
          simp only at hl
          have hh : LabHint "call" := by simp [LabHint]
          have hmn : m = n := Classical.byContradiction fun hne => labName_ne hh hh (by omega) hl
          subst hmn
          exact ⟨by simp, .inl ⟨[], by simp, rfl⟩⟩
        · obtain ⟨h1, h2⟩ := h.bracket m g' w' rest t' hm
          refine ⟨by simp [h1], .inr ?_⟩
          rcases h2 with ⟨pre, hp, ht⟩ | ⟨b, hb, pre, hp, ht⟩
          · exact ⟨⟨labName "call" (n + 5), callPost g w n ++ r'.insts, r'.term⟩, by simp,
              callPost g w n ++ pre, by simp [hp], ht⟩
          · exact ⟨b, by simp [hb], pre, hp, ht⟩
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro scope env n l k r hr hb hs he
    obtain ⟨_, p, _, q, ry, rn, ha, hb', hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    simp only [body1, atom1, Bool.and_eq_true] at hb
    have hy' := ihy _ _ _ _ _ _ hy hb.1.2 hs he
    have hn' := ihn _ _ _ _ _ _ hn hb.2 hs he
    refine ⟨noCall_nil, ?_, ?_⟩
    · intro b hb
      simp only [List.mem_cons, List.mem_append] at hb
      rcases hb with (rfl | hb) | rfl | hb
      · exact .plain _ hy'.insts
      · exact hy'.blocks b hb
      · exact .plain _ hn'.insts
      · exact hn'.blocks b hb
    · intro m g w rest t hm
      simp only [List.mem_cons, List.mem_append] at hm
      rcases hm with (hm | hm) | hm | hm
      · exact absurd hm (callBlk_ne hy'.insts)
      · obtain ⟨h1, h2⟩ := hy'.bracket _ _ _ _ _ hm
        refine ⟨by simp [h1], .inr ?_⟩
        rcases h2 with ⟨pre, hp, ht⟩ | ⟨b, hb, pre, hp, ht⟩
        · exact ⟨⟨labName "then" n, ry.insts, ry.term⟩, by simp, pre, hp, ht⟩
        · exact ⟨b, by simp [hb], pre, hp, ht⟩
      · exact absurd hm (callBlk_ne hn'.insts)
      · obtain ⟨h1, h2⟩ := hn'.bracket _ _ _ _ _ hm
        refine ⟨by simp [h1], .inr ?_⟩
        rcases h2 with ⟨pre, hp, ht⟩ | ⟨b, hb, pre, hp, ht⟩
        · exact ⟨⟨labName "else" (n + 1), rn.insts, rn.term⟩, by simp, pre, hp, ht⟩
        · exact ⟨b, by simp [hb], pre, hp, ht⟩
  | ret a =>
    intro scope env n l k r hr hb hs he
    obtain ⟨t, ws, -, rfl⟩ := lowerC_ret_inv hr
    exact ⟨noCall_nil, by simp, by simp⟩
  | _ => intro scope env n l k r hr; simp [lowerC] at hr

/-- `CallRes` of an `Accepted1` code block's closed form. -/
theorem func1_callRes (cx : Scc.Lower.Ctx) {fr : Nat} (hf : cx.frames = some fr) {earlier : List String} {d : Decl}
    (hd : decl1 earlier d = true) {r : Res1} (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) :
    CallRes cx fr r := by
  obtain ⟨harg, -, hb⟩ := decl1_shape hd
  exact lowerC_callRes cx hf d.body _ _ _ _ _ r hr hb (envScalar_env1 harg) (envOk_env1 d)

/-- **The blocks of an `Accepted1` code block's function, by their calls**
(`CallBlk`), with the depth counter. -/
theorem func1_callBlk (cx : Scc.Lower.Ctx) {fr : Nat} (hf : cx.frames = some fr) {earlier : List String} {d : Decl}
    (hd : decl1 earlier d = true) {r : Res1} (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r)
    (name : Sym) : ∀ b ∈ (func1 name (params1R d) r).blocks, CallBlk cx b := by
  have h := func1_callRes cx hf hd hr
  intro b hb
  simp only [func1, List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact .plain _ h.insts
  · exact h.blocks b hb

/-- **The bracket before each call block** of an `Accepted1` code block's
function: the abort block `deepBlock n`, and a block ending with
`depthPre n`, terminated by `depthTerm fr n`. -/
theorem func1_bracket (cx : Scc.Lower.Ctx) {fr : Nat} (hf : cx.frames = some fr) {earlier : List String} {d : Decl}
    (hd : decl1 earlier d = true) {r : Res1} (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r)
    (name : Sym) {n : Nat} {g : String} {w : Operand} {rest : List Inst} {t : Term}
    (hb : callBlk n g w rest t ∈ (func1 name (params1R d) r).blocks) :
    deepBlock n ∈ (func1 name (params1R d) r).blocks ∧
      ∃ b ∈ (func1 name (params1R d) r).blocks, ∃ pre, b.insts = pre ++ depthPre n ∧ b.term = depthTerm fr n := by
  have h := func1_callRes cx hf hd hr
  simp only [func1, List.mem_cons] at hb
  rcases hb with hb | hb
  · exact absurd hb (callBlk_ne (b := ⟨"entry", r.insts, r.term⟩) h.insts)
  · obtain ⟨h1, h2⟩ := h.bracket _ _ _ _ _ hb
    refine ⟨by simp [func1, h1], ?_⟩
    rcases h2 with ⟨pre, hp, ht⟩ | ⟨b, hb, pre, hp, ht⟩
    · exact ⟨⟨"entry", r.insts, r.term⟩, by simp [func1], pre, hp, ht⟩
    · exact ⟨b, by simp [func1, hb], pre, hp, ht⟩

/-! ## Without the depth counter -/

/-- Instructions without the stack abort's call (`call [] scc_rt_abort
[stack]`, the removed depth counter's). -/
def NoStackAbort (is : List Inst) : Prop :=
  ∀ i ∈ is, i ≠ .call [] Names.abort [imm AbortKind.stack.code]

/-- **The closed form without the depth counter has no stack abort's
call** (`cx.frames = none`): neither in the open block nor in a later
one; its calls are plain user calls `call [r%n] (wc_g) [w]`. -/
theorem lowerC_noStackAbort (cx : Scc.Lower.Ctx) (hf : cx.frames = none) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → NoStackAbort r.insts ∧ ∀ b ∈ r.blocks, NoStackAbort b.insts := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | atom a =>
      obtain ⟨t, w, r', -, -, hr', rfl⟩ := lowerC_atom_inv hr
      exact ih _ _ _ _ r' hr'
    | add a b | sub a b =>
      first
        | obtain ⟨_, p, _, q, r', -, -, hr', rfl⟩ := lowerC_add_inv hr
        | obtain ⟨_, p, _, q, r', -, -, hr', rfl⟩ := lowerC_sub_inv hr
      have h := ih _ _ _ _ _ hr'
      refine ⟨fun i hi => ?_, h.2⟩
      rcases List.mem_cons.mp hi with rfl | hi
      · simp
      · exact h.1 i hi
    | call g is a ts =>
      obtain ⟨dg, t, w, -, -, -, -, h⟩ := lowerC_call_inv hr
      rcases h with ⟨-, r', hr', rfl⟩ | ⟨fr', r', hf', -⟩
      · have h := ih _ _ _ _ _ hr'
        refine ⟨fun i hi => ?_, h.2⟩
        rcases List.mem_cons.mp hi with rfl | hi
        · simp
        · exact h.1 i hi
      · rw [hf] at hf'; cases hf'
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr
    obtain ⟨_, p, _, q, ry, rn, -, -, hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    have hy' := ihy _ _ _ _ _ hy
    have hn' := ihn _ _ _ _ _ hn
    refine ⟨by simp [NoStackAbort], fun b hb => ?_⟩
    simp only [List.mem_cons, List.mem_append] at hb
    rcases hb with (rfl | hb) | rfl | hb
    · exact hy'.1
    · exact hy'.2 b hb
    · exact hn'.1
    · exact hn'.2 b hb
  | ret a =>
    intro env n l k r hr
    obtain ⟨t, ws, -, rfl⟩ := lowerC_ret_inv hr
    exact ⟨by simp [NoStackAbort], by simp⟩
  | _ => intro env n l k r hr; simp [lowerC] at hr

/-- **The blocks of a code block's function without the depth counter have
no stack abort's call** (`lowerC_noStackAbort`). -/
theorem func1_noStackAbort (cx : Scc.Lower.Ctx) (hf : cx.frames = none) {d : Decl} {r : Res1}
    (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    ∀ b ∈ (func1 name (params1R d) r).blocks, NoStackAbort b.insts := by
  have h := lowerC_noStackAbort cx hf d.body _ _ _ _ r hr
  intro b hb
  simp only [func1, List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact h.1
  · exact h.2 b hb

end Spike.Lib.LowerCall
