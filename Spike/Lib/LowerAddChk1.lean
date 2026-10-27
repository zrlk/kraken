/-
**A checked `+` in a call-free `Accepted1` body's walk is an instruction**
(ISA-neutral), the twin of `lower0_insts_ne_of_mem`
(`Spike/Lib/LowerEnvImm.lean`): if `lower1` succeeds and its walk
(`lowerEnvs1`) reaches a `let x = a + b`, one of the lowered function's
blocks has a checked `+` (so the function has the local overflow block:
`hasAddChk (func1 name ps r) = true`).

- `HasAdd`, `hasAdd_of_walk`: a `let x = a + b` the walk reaches is on the
  body's `let`/`if` spine;
- `AddIn`, `lower1_addIn`: on that spine, `lower1` emits an `addChk`;
- `lower1_add_insts`: the statement on the function's blocks.
-/
import Spike.Lib.LowerEnvImm1

namespace Spike.Lib.LowerAddChk

open CoreLang CoreTerm
open Scc.Lower.Inv (lower1 atomV Res1)
open Spike.Lib.LowerNode (lowerEnvs1)

/-- A checked `+` instruction. -/
def IsAdd (i : Scc.IR.Inst) : Prop := ∃ d p q, i = .addChk d p q

/-- **A `let x = a + b` on `e`'s `let`/`if` spine.** -/
def HasAdd : Expr → Prop
  | .let_ _ (.add _ _) _ => True
  | .let_ _ _ e => HasAdd e
  | .ifeq _ _ yes no => HasAdd yes ∨ HasAdd no
  | _ => False

/-- **A `let x = a + b` the walk reaches is on the spine.** -/
theorem hasAdd_of_walk :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat),
      (∃ q ∈ lowerEnvs1 env n e, ∃ x a b e', q.1 = .let_ x (.add a b) e') → HasAdd e := by
  intro e
  induction e with
  | let_ y op e ih =>
    intro env n ⟨q, hq, x, a, b, e', hqt⟩
    cases op with
    | atom c =>
      simp only [lowerEnvs1, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqt
      · show HasAdd e
        cases ha : atomV env c with
        | none => rw [ha] at hq; cases hq
        | some v =>
          obtain ⟨t, ws⟩ := v
          rw [ha] at hq
          exact ih _ _ ⟨q, hq, x, a, b, e', hqt⟩
    | add c c' => trivial
    | sub c c' =>
      simp only [lowerEnvs1, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqt
      · exact ih _ _ ⟨q, hq, x, a, b, e', hqt⟩
    | _ =>
      simp only [lowerEnvs1, List.mem_singleton] at hq
      subst hq
      cases hqt
  | ifeq c c' yes no ihy ihn =>
    intro env n ⟨q, hq, x, a, b, e', hqt⟩
    simp only [lowerEnvs1, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · cases hqt
    · exact .inl (ihy _ _ ⟨q, hq, x, a, b, e', hqt⟩)
    · exact .inr (ihn _ _ ⟨q, hq, x, a, b, e', hqt⟩)
  | _ =>
    intro env n ⟨q, hq, x, a, b, e', hqt⟩
    simp only [lowerEnvs1, List.mem_singleton] at hq
    subst hq
    cases hqt

/-- A closed form has a checked `+`: in its open block or a later block. -/
def AddIn (r : Res1) : Prop := (∃ i ∈ r.insts, IsAdd i) ∨ ∃ b ∈ r.blocks, ∃ i ∈ b.insts, IsAdd i

/-- **On the spine, `lower1` emits a checked `+`.** -/
theorem lower1_addIn :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Res1), lower1 env n e = some r → HasAdd e → AddIn r := by
  intro e
  induction e with
  | let_ y op e ih =>
    intro env n r hr hh
    cases op with
    | atom c =>
      simp only [lower1] at hr
      cases ha : atomV env c with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
          rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases ht : Scc.Lower.Inv.scalar1 t with
        | false => simp [ht] at hr
        | true =>
          cases hr' : lower1 ((y, t, [w]) :: env) n e with
          | none => simp [ht, hr'] at hr
          | some r' =>
            simp [ht, hr'] at hr
            subst hr
            exact (ih _ _ _ hr' hh :)
    | add c c' =>
      simp only [lower1] at hr
      cases ha : atomV env c with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
          rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hb : atomV env c' with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
            rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
          cases hr' : lower1 ((y, .int, [.reg (Scc.Lower.Inv.regName y n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            exact .inl ⟨_, List.mem_cons_self .., _, _, _, rfl⟩
    | sub c c' =>
      simp only [lower1] at hr
      cases ha : atomV env c with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
          rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hb : atomV env c' with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
            rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
          cases hr' : lower1 ((y, .int, [.reg (Scc.Lower.Inv.regName y n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp [hr'] at hr
            subst hr
            rcases ih _ _ _ hr' hh with ⟨i, hi, hi'⟩ | hb'
            · exact .inl ⟨i, List.mem_cons_of_mem _ hi, hi'⟩
            · exact .inr hb'
    | _ => simp [lower1] at hr
  | ifeq c c' yes no ihy ihn =>
    intro env n r hr hh
    simp only [lower1] at hr
    cases ha : atomV env c with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      rw [ha] at hr
      obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
        rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
      cases hb : atomV env c' with
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
            right
            have lift : ∀ (l : String) (rr : Res1), AddIn rr →
                ∃ b ∈ (⟨l, rr.insts, rr.term⟩ :: rr.blocks : List Scc.IR.Block), ∃ i ∈ b.insts, IsAdd i := by
              intro l rr h
              rcases h with ⟨i, hi, hi'⟩ | ⟨b, hb, i, hi, hi'⟩
              · exact ⟨_, List.mem_cons_self .., i, hi, hi'⟩
              · exact ⟨b, List.mem_cons_of_mem _ hb, i, hi, hi'⟩
            rcases hh with hh | hh
            · obtain ⟨b, hb, h⟩ := lift (Scc.Lower.Inv.labName "then" n) _ (ihy _ _ _ hy hh)
              refine ⟨b, ?_, h⟩
              simp only [List.mem_cons, List.mem_append] at hb ⊢
              rcases hb with hb | hb
              · exact .inl hb
              · exact .inr (.inl hb)
            · obtain ⟨b, hb, h⟩ := lift (Scc.Lower.Inv.labName "else" (n + 1)) _ (ihn _ _ _ hn hh)
              refine ⟨b, ?_, h⟩
              simp only [List.mem_cons, List.mem_append] at hb ⊢
              rcases hb with hb | hb
              · exact .inr (.inr (.inl hb))
              · exact .inr (.inr (.inr hb))
  | _ => intro env n r hr hh; exact hh.elim

/-- **A checked `+` in the walk is an instruction** of one of the lowered
function's blocks (so `hasAddChk (func1 name ps r) = true`). -/
theorem lower1_add_insts :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (r : Res1), lower1 env n e = some r →
      (∃ q ∈ lowerEnvs1 env n e, ∃ x a b e', q.1 = .let_ x (.add a b) e') →
      ((⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block).any fun b =>
        b.insts.any fun | .addChk .. => true | _ => false) = true := by
  intro e env n r hr hw
  have h : ∃ b ∈ (⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block), ∃ i ∈ b.insts, IsAdd i := by
    rcases lower1_addIn e env n r hr (hasAdd_of_walk e env n hw) with ⟨i, hi, hi'⟩ | ⟨b, hb, i, hi, hi'⟩
    · exact ⟨_, List.mem_cons_self .., i, hi, hi'⟩
    · exact ⟨b, List.mem_cons_of_mem _ hb, i, hi, hi'⟩
  obtain ⟨b, hb, i, hi, d, p, q, rfl⟩ := h
  exact List.any_eq_true.mpr ⟨b, hb, List.any_eq_true.mpr ⟨_, hi, rfl⟩⟩

end Spike.Lib.LowerAddChk
