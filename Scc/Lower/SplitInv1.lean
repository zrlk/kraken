import Scc.Lower.InvC1
import Scc.Lower.Split

/-!
# The split leaves `Accepted1` programs unchanged

Without the depth counter (`frames = none`, as `lowerWithMarks` lowers),
the closed form `lowerC` of a body `e` appends to its open block
instructions and a terminator weighing at most `openW1 e`
(`Scc.Lower.openW1`), and every block it closes after that weighs at most
`armsW1 e` (`lowerC_weight`): a `let` of an atom appends nothing, `+` an
`addChk` and `-` a `subSat` (one unit each), a call `call [r] g [w]` (three
units), an `if` its `br` (one unit) and `ret a` a `ret` of at most one word
(two units), as long as every variable is bound to at most one word
(`EnvW1`).

So for an `Accepted1` program, whose first conjunct `blocksOk1` bounds
these by `Scc.IR.maxBlockLen` (the first block with its parameter),
`func1` of each code block is `blocksOk` (`blocksOk_func1`) and the split
pass (`Scc.Lower.splitFuncMarks`) leaves it and its trace as they are
(`splitFuncMarks_func1`).
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.Inv

/-- Every variable of `env` is bound to at most one word. -/
def EnvW1 (env : Env) : Prop := ∀ v ∈ env, v.2.2.length ≤ 1

theorem envW1_cons {env : Env} (h : EnvW1 env) (x : String) (t : Ty) (w : Operand) :
    EnvW1 ((x, t, [w]) :: env) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · simp
  · exact h v hv

theorem envW1_env1 (d : Decl) : EnvW1 (env1 d) := by
  intro v hv
  simp only [env1, List.mem_singleton] at hv
  subst hv
  simp only [params1R, List.length_map]
  split <;> simp

/-- An atom's words in an `EnvW1` environment: at most one. -/
theorem atomV_length {env : Env} (h : EnvW1 env) {a : At} {t : Ty} {ws : List Operand}
    (ha : atomV env a = some (t, ws)) : ws.length ≤ 1 := by
  cases a with
  | var x =>
    simp only [atomV, Option.map_eq_some_iff] at ha
    obtain ⟨⟨y, t', ws'⟩, hf, he⟩ := ha
    cases he
    exact h _ (List.mem_of_find?_eq_some hf)
  | lit n =>
    simp only [atomV] at ha
    split at ha
    · cases ha
    · cases ha; simp
  | unit => simp only [atomV] at ha; cases ha; simp

/-- **The weights of `lowerC`'s output without the depth counter**: the
open block's appended instructions and terminator weigh at most `openW1 e`,
every block closed after it at most `armsW1 e`. -/
theorem lowerC_weight (cx : Ctx) (hf : cx.frames = none) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      EnvW1 env → lowerC cx env n l k e = some r →
        instsWeight r.insts + termWeight r.term ≤ openW1 e ∧ ∀ b ∈ r.blocks, blockWeight b ≤ armsW1 e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hw hr
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
          simpa [openW1, armsW1] using ih _ n l k r' (envW1_cons hw x t w) hr'
    | add a b =>
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
            have := ih _ (n + 1) l (k + 1) r' (envW1_cons hw x _ _) hr'
            simp only [instsWeight, List.map_cons, List.sum_cons, openW1, armsW1] at this ⊢
            refine ⟨?_, this.2⟩
            simp only [instWeight]
            omega
    | sub a b =>
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
            have := ih _ (n + 1) l (k + 1) r' (envW1_cons hw x _ _) hr'
            simp only [instsWeight, List.map_cons, List.sum_cons, openW1, armsW1] at this ⊢
            refine ⟨?_, this.2⟩
            simp only [instWeight]
            omega
    | call g is a ts =>
      simp only [lowerC, hf] at hr
      split at hr
      · cases hd : cx.prog.find? (·.name == g) with
        | none => simp [hd] at hr
        | some dg =>
          simp only [hd, Option.bind_eq_bind, Option.bind_some] at hr
          split at hr
          · cases ha : atomV env a with
            | none => simp [ha] at hr
            | some v =>
              obtain ⟨t, ws⟩ := v
              rw [ha] at hr
              match ws, hr with
              | [w], hr =>
              cases hr' : lowerC cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1) l (k + 1) e with
              | none => simp [hr'] at hr
              | some r' =>
                simp [hr'] at hr
                subst hr
                have := ih _ (n + 1) l (k + 1) r' (envW1_cons hw x _ _) hr'
                simp only [instsWeight, List.map_cons, List.sum_cons, openW1, armsW1] at this ⊢
                refine ⟨?_, this.2⟩
                simp only [instWeight, List.length_singleton]
                omega
          · cases hr
      · cases hr
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hw hr
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
            obtain ⟨hy1, hy2⟩ := ihy env _ _ _ ry hw hy
            obtain ⟨hn1, hn2⟩ := ihn env _ _ _ rn hw hn
            refine ⟨by simp [instsWeight, termWeight, openW1], ?_⟩
            intro bl hbl
            simp only [List.mem_cons, List.mem_append] at hbl
            simp only [armsW1]
            rcases hbl with rfl | hbl | rfl | hbl
            · simp only [blockWeight]; omega
            · have := hy2 bl hbl; omega
            · simp only [blockWeight]; omega
            · have := hn2 bl hbl; omega
  | ret a =>
    intro env n l k r hw hr
    simp only [lowerC] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      simp [ha] at hr
      subst hr
      have := atomV_length hw ha
      simp only [instsWeight, List.map_nil, List.sum_nil, termWeight, openW1, armsW1, List.not_mem_nil,
        false_imp_iff, implies_true, and_true]
      omega
  | _ => intro env n l k r _ hr; simp [lowerC] at hr

theorem params1R_length (d : Decl) : (params1R d).length = (params1 d).length := by
  simp only [params1R, params1]
  split <;> simp

/-- **`func1` within the bound**: the closed form without the depth counter
of a code block `d` whose blocks `blocksOk1` bounds. -/
theorem blocksOk_func1 (cx : Ctx) (hf : cx.frames = none) {d : Decl} (name : Sym)
    (hb : decide ((params1 d).length + openW1 d.body ≤ maxBlockLen) &&
      decide (armsW1 d.body ≤ maxBlockLen) = true)
    {r : Res1} (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) :
    blocksOk (func1 name (params1R d) r) = true := by
  obtain ⟨h1, h2⟩ := lowerC_weight cx hf d.body (env1 d) 0 "entry" 0 r (envW1_env1 d) hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  simp only [blocksOk, func1, blockWeight, params1R_length, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  refine ⟨by omega, fun b hb' => ?_⟩
  have := h2 b hb'
  simp only [blockWeight] at this
  exact decide_eq_true (by omega)

/-- `blocksOk1`'s bound on one code block. -/
theorem blocksOk1_mem {p : Prog} (h : blocksOk1 p = true) {d : Decl} (hd : d ∈ p) :
    decide ((params1 d).length + openW1 d.body ≤ maxBlockLen) &&
      decide (armsW1 d.body ≤ maxBlockLen) = true :=
  List.all_eq_true.mp h d hd

/-- **`Accepted1` programs have bounded blocks**: `blocksOk1` is the first
conjunct of `Accepted1`. The one place that reads its position: the lemmas
of this module use this one. -/
theorem blocksOk1_of_accepted1 {p : Prog} (h : Accepted1 p = true) : blocksOk1 p = true := by
  simp only [Accepted1, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hb, _hnodup⟩, _hmain⟩, _hdecls⟩, _himms⟩ := h
  exact hb

/-- **`split_id` for `Accepted1`**: the split leaves the lowering without
the depth counter of a code block of an `Accepted1` program, and its trace,
unchanged. -/
theorem splitFuncMarks_func1 {p : Prog} (hp : Accepted1 p = true) (cx : Ctx) (hf : cx.frames = none)
    {d : Decl} (hd : d ∈ p) (name : Sym) {r : Res1} (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) :
    splitFuncMarks (func1 name (params1R d) r, marks1 d r) = (func1 name (params1R d) r, marks1 d r) :=
  splitFuncMarks_id (blocksOk_func1 cx hf name (blocksOk1_mem (blocksOk1_of_accepted1 hp) hd) hr)

end Scc.Lower.Inv
