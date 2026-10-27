/-
**Free variables of an `Accepted1` body with calls** (ISA-neutral), next to
`Spike/Lib/LowerEnvImm1.lean`'s `lower1_fv` for call-free bodies.

- `lowerC_fv`: every free variable of a body lowered by `lowerC` is bound in
  the lowering's environment.
-/
import Scc.Sem.Correct
import Scc.Lower.InvC1

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower.Inv (lowerC atomV Res1)

/-- **Every free variable of a body lowered by `lowerC` is bound** in the
lowering's environment. -/
theorem lowerC_fv (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → ∀ y ∈ Scc.Sem.exprFv e, (env.find? (·.1 == y)).isSome := by
  have hat : ∀ (env : Scc.Lower.Env) (a : At) v, atomV env a = some v →
      ∀ y ∈ Scc.Sem.atVars a, (env.find? (·.1 == y)).isSome := by
    intro env a v ha y hy
    cases a with
    | var x =>
      simp only [Scc.Sem.atVars, List.mem_singleton] at hy
      subst hy
      simp only [atomV, Option.map_eq_some_iff] at ha
      obtain ⟨b, hb, -⟩ := ha
      simp [hb]
    | _ => simp [Scc.Sem.atVars] at hy
  have hcons : ∀ (env : Scc.Lower.Env) (b : String × Ty × List Scc.IR.Operand) (y : String), b.1 ≠ y →
      ((b :: env).find? (·.1 == y)).isSome → (env.find? (·.1 == y)).isSome := by
    intro env b y hne h
    have : (b.1 == y) = false := by simp [hne]
    simpa [List.find?_cons, this] using h
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr y hy
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
        | none => cases ht : Scc.Lower.Inv.scalar1 t <;> simp [ht, hr'] at hr
        | some r' =>
          simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
          rcases hy with hy | ⟨hy, hne⟩
          · exact hat env a _ ha y hy
          · exact hcons env (x, t, [w]) y (fun e => hne e.symm) (ih _ n l k r' hr' y hy)
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
          cases hr' : lowerC cx ((x, .int, [.reg (Scc.Lower.Inv.regName x n)]) :: env) (n + 1) l (k + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
            rcases hy with (hy | hy) | ⟨hy, hne⟩
            · exact hat env a _ ha y hy
            · exact hat env b _ hb y hy
            · exact hcons env _ y (fun e => hne e.symm) (ih _ _ _ _ r' hr' y hy)
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
      simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
      rcases hy with hy | ⟨hy, hne⟩
      · exact hat env a _ ha y hy
      · refine hcons env (x, .int, [.reg (Scc.Lower.Inv.regName "r" n)]) y (fun e => hne e.symm) ?_
        cases hf : cx.frames with
        | none =>
          cases hr' : lowerC cx ((x, .int, [.reg (Scc.Lower.Inv.regName "r" n)]) :: env) (n + 1) l (k + 1) e with
          | none => simp [hf, hr'] at hr
          | some r' => exact ih _ _ _ _ r' hr' y hy
        | some fr =>
          cases hr' : lowerC cx ((x, .int, [.reg (Scc.Lower.Inv.regName "r" n)]) :: env) (n + 7)
              (Scc.Lower.Inv.labName "call" (n + 5)) 4 e with
          | none => simp [hf, hr'] at hr
          | some r' => exact ih _ _ _ _ r' hr' y hy
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr y hy
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
        cases hy' : lowerC cx env (n + 2) (Scc.Lower.Inv.labName "then" n) 0 yes with
        | none => simp [hy'] at hr
        | some ry =>
          cases hn : lowerC cx env ry.next (Scc.Lower.Inv.labName "else" (n + 1)) 0 no with
          | none => simp [hy', hn] at hr
          | some rn =>
            simp only [Scc.Sem.exprFv, List.mem_append] at hy
            rcases hy with ((hy | hy) | hy) | hy
            · exact hat env a _ ha y hy
            · exact hat env b _ hb y hy
            · exact ihy env _ _ _ ry hy' y hy
            · exact ihn env _ _ _ rn hn y hy
  | ret a =>
    intro env n l k r hr y hy
    simp only [lowerC] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v => exact hat env a v ha y hy
  | _ => intro env n l k r hr; simp [lowerC] at hr

end Spike.Lib.LowerNode
