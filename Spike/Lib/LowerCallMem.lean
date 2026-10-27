/-
**A call at a point of the walk is emitted** (ISA-neutral): a call of a
code block `g` at a point of the closed form's walk (`lowerEnvsC`) has a
`call` of `Names.user g` among the closed form's instructions (`allInsts`),
the premise of the call sites' row and room lemmas (e.g.
`calleeRow_name_of_placeOK`) from a source call.

- `lowerC_callMem`: the statement, by induction on the body.
-/
import Spike.Lib.LowerShapeC1
import Spike.Lib.LowerEnvImmC1Of

namespace Spike.Lib.LowerShape

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Spike.Lib.LowerNode (lowerEnvsC)

/-- **A call at a point of the walk is emitted**: a call of `g` at a point
of the walk of `e` (at the closed form's depth limit, environment and
counter) has a `call` of `Names.user g` in the closed form. -/
theorem lowerC_callMem (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → ∀ q ∈ lowerEnvsC cx.frames env n e,
        ∀ x g is a ts e', q.1 = .let_ x (.call g is a ts) e' →
          ∃ ds ws, Inst.call ds (Names.user g) ws ∈ allInsts r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr q hq y g is a0 ts e' hqe
    cases op with
    | atom a =>
      obtain ⟨t, w, r', ha, -, hr', rfl⟩ := lowerC_atom_inv hr
      simp only [lowerEnvsC, List.mem_cons, ha] at hq
      rcases hq with rfl | hq
      · cases hqe
      · obtain ⟨ds, ws, hm⟩ := ih _ _ _ _ _ hr' q hq y g is a0 ts e' hqe
        exact ⟨ds, ws, by simpa [allInsts] using hm⟩
    | add a b =>
      obtain ⟨-, p, -, q', r', -, -, hr', rfl⟩ := lowerC_add_inv hr
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · obtain ⟨ds, ws, hm⟩ := ih _ _ _ _ _ hr' q hq y g is a0 ts e' hqe
        refine ⟨ds, ws, ?_⟩
        simp only [allInsts, List.mem_append, List.mem_cons] at hm ⊢
        rcases hm with hm | hm
        · exact .inl (.inr hm)
        · exact .inr hm
    | sub a b =>
      obtain ⟨-, p, -, q', r', -, -, hr', rfl⟩ := lowerC_sub_inv hr
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · obtain ⟨ds, ws, hm⟩ := ih _ _ _ _ _ hr' q hq y g is a0 ts e' hqe
        refine ⟨ds, ws, ?_⟩
        simp only [allInsts, List.mem_append, List.mem_cons] at hm ⊢
        rcases hm with hm | hm
        · exact .inl (.inr hm)
        · exact .inr hm
    | call g' is' a' ts' =>
      obtain ⟨dg, t, w, -, -, -, -, h⟩ := lowerC_call_inv hr
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
        rcases h with ⟨-, r', -, rfl⟩ | ⟨fr, r', -, -, rfl⟩
        · exact ⟨[regName "r" n], [w], by simp [allInsts]⟩
        · exact ⟨[regName "r" n], [w], by simp [allInsts, callPost]⟩
      · rcases h with ⟨hf, r', hr', rfl⟩ | ⟨fr, r', hf, hr', rfl⟩
        · simp only [hf, Option.isSome_none, Bool.false_eq_true, ite_false] at hq
          rw [← hf] at hq
          obtain ⟨ds, ws, hm⟩ := ih _ _ _ _ _ hr' q hq y g is a0 ts e' hqe
          refine ⟨ds, ws, ?_⟩
          simp only [allInsts, List.mem_append, List.mem_cons] at hm ⊢
          rcases hm with hm | hm
          · exact .inl (.inr hm)
          · exact .inr hm
        · simp only [hf, Option.isSome_some, ite_true] at hq
          rw [← hf] at hq
          obtain ⟨ds, ws, hm⟩ := ih _ _ _ _ _ hr' q hq y g is a0 ts e' hqe
          refine ⟨ds, ws, ?_⟩
          simp only [allInsts, List.mem_append, List.mem_flatMap, List.mem_cons] at hm ⊢
          rcases hm with hm | ⟨b, hb, hm⟩
          · exact .inr ⟨_, .inr (.inl rfl), List.mem_append_right _ hm⟩
          · exact .inr ⟨b, .inr (.inr hb), hm⟩
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr q hq y g is a0 ts e' hqe
    obtain ⟨-, p, -, q', ry, rn, -, -, hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    have hnx := lowerC_next cx _ _ _ _ _ _ hy
    simp only [lowerEnvsC, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · cases hqe
    · obtain ⟨ds, ws, hm⟩ := ihy _ _ _ _ _ hy q hq y g is a0 ts e' hqe
      refine ⟨ds, ws, ?_⟩
      simp only [allInsts, List.mem_append, List.mem_flatMap, List.mem_cons, List.nil_append] at hm ⊢
      rcases hm with hm | ⟨b, hb, hm⟩
      · exact ⟨_, .inl (.inl rfl), hm⟩
      · exact ⟨b, .inl (.inr hb), hm⟩
    · rw [← hnx] at hq
      obtain ⟨ds, ws, hm⟩ := ihn _ _ _ _ _ hn q hq y g is a0 ts e' hqe
      refine ⟨ds, ws, ?_⟩
      simp only [allInsts, List.mem_append, List.mem_flatMap, List.mem_cons, List.nil_append] at hm ⊢
      rcases hm with hm | ⟨b, hb, hm⟩
      · exact ⟨_, .inr (.inl rfl), hm⟩
      · exact ⟨b, .inr (.inr hb), hm⟩
  | ret a =>
    intro env n l k r hr q hq y g is a0 ts e' hqe
    simp only [lowerEnvsC, List.mem_singleton] at hq
    subst hq
    cases hqe
  | _ => intro env n l k r hr; simp [lowerC] at hr

/-- **An addition at a point of the walk is emitted**: an addition at a
point of the walk of `e` (at the closed form's depth limit, environment and
counter) has a checked `addChk` in the closed form. -/
theorem lowerC_addMem (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → ∀ q ∈ lowerEnvsC cx.frames env n e,
        ∀ x a b e', q.1 = .let_ x (.add a b) e' →
          ∃ i ∈ allInsts r, ∃ d u v, i = .addChk d u v := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr q hq y a1 b1 e' hqe
    cases op with
    | atom a =>
      obtain ⟨t, w, r', ha, -, hr', rfl⟩ := lowerC_atom_inv hr
      simp only [lowerEnvsC, List.mem_cons, ha] at hq
      rcases hq with rfl | hq
      · cases hqe
      · obtain ⟨ii, hm, hii⟩ := ih _ _ _ _ _ hr' q hq y a1 b1 e' hqe
        exact ⟨ii, by simpa [allInsts] using hm, hii⟩
    | add a b =>
      obtain ⟨-, p, -, q', r', -, -, hr', rfl⟩ := lowerC_add_inv hr
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨.addChk (regName x n) p q', by simp [allInsts], _, _, _, rfl⟩
      · obtain ⟨ii, hm, hii⟩ := ih _ _ _ _ _ hr' q hq y a1 b1 e' hqe
        refine ⟨ii, ?_, hii⟩
        simp only [allInsts, List.mem_append, List.mem_cons] at hm ⊢
        rcases hm with hm | hm
        · exact .inl (.inr hm)
        · exact .inr hm
    | sub a b =>
      obtain ⟨-, p, -, q', r', -, -, hr', rfl⟩ := lowerC_sub_inv hr
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · obtain ⟨ii, hm, hii⟩ := ih _ _ _ _ _ hr' q hq y a1 b1 e' hqe
        refine ⟨ii, ?_, hii⟩
        simp only [allInsts, List.mem_append, List.mem_cons] at hm ⊢
        rcases hm with hm | hm
        · exact .inl (.inr hm)
        · exact .inr hm
    | call g' is' a' ts' =>
      obtain ⟨dg, t, w, -, -, -, -, h⟩ := lowerC_call_inv hr
      simp only [lowerEnvsC, List.mem_cons] at hq
      rcases hq with rfl | hq
      · cases hqe
      · rcases h with ⟨hf, r', hr', rfl⟩ | ⟨fr, r', hf, hr', rfl⟩
        · simp only [hf, Option.isSome_none, Bool.false_eq_true, ite_false] at hq
          rw [← hf] at hq
          obtain ⟨ii, hm, hii⟩ := ih _ _ _ _ _ hr' q hq y a1 b1 e' hqe
          refine ⟨ii, ?_, hii⟩
          simp only [allInsts, List.mem_append, List.mem_cons] at hm ⊢
          rcases hm with hm | hm
          · exact .inl (.inr hm)
          · exact .inr hm
        · simp only [hf, Option.isSome_some, ite_true] at hq
          rw [← hf] at hq
          obtain ⟨ii, hm, hii⟩ := ih _ _ _ _ _ hr' q hq y a1 b1 e' hqe
          refine ⟨ii, ?_, hii⟩
          simp only [allInsts, List.mem_append, List.mem_flatMap, List.mem_cons] at hm ⊢
          rcases hm with hm | ⟨b, hb, hm⟩
          · exact .inr ⟨_, .inr (.inl rfl), List.mem_append_right _ hm⟩
          · exact .inr ⟨b, .inr (.inr hb), hm⟩
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr q hq y a1 b1 e' hqe
    obtain ⟨-, p, -, q', ry, rn, -, -, hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    have hnx := lowerC_next cx _ _ _ _ _ _ hy
    simp only [lowerEnvsC, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · cases hqe
    · obtain ⟨ii, hm, hii⟩ := ihy _ _ _ _ _ hy q hq y a1 b1 e' hqe
      refine ⟨ii, ?_, hii⟩
      simp only [allInsts, List.mem_append, List.mem_flatMap, List.mem_cons, List.nil_append] at hm ⊢
      rcases hm with hm | ⟨b, hb, hm⟩
      · exact ⟨_, .inl (.inl rfl), hm⟩
      · exact ⟨b, .inl (.inr hb), hm⟩
    · rw [← hnx] at hq
      obtain ⟨ii, hm, hii⟩ := ihn _ _ _ _ _ hn q hq y a1 b1 e' hqe
      refine ⟨ii, ?_, hii⟩
      simp only [allInsts, List.mem_append, List.mem_flatMap, List.mem_cons, List.nil_append] at hm ⊢
      rcases hm with hm | ⟨b, hb, hm⟩
      · exact ⟨_, .inr (.inl rfl), hm⟩
      · exact ⟨b, .inr (.inr hb), hm⟩
  | ret a =>
    intro env n l k r hr q hq y a1 b1 e' hqe
    simp only [lowerEnvsC, List.mem_singleton] at hq
    subst hq
    cases hqe
  | _ => intro env n l k r hr; simp [lowerC] at hr

end Spike.Lib.LowerShape
