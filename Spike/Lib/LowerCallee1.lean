/-
**The callees of an `Accepted1` code block's lowering** (ISA-neutral):
every `call` the closed form `lowerC` (`Scc/Lower/InvC1.lean`) emits is
the stack abort's or one of a code block declared before the caller.

- `decl1_take`: the `j`th code block of a `decls1` list is `decl1` with
  the names of the code blocks before it (reversed) as `earlier`;
- `mem_earlier_index`: such a name is that of a code block at a smaller
  index;
- `CallOk`, `lowerC_callOk`: every instruction of the closed form of an
  `Accepted1` body is a `call` of `Names.abort` or of `Names.user g` for
  `g` in `earlier`, or no `call`;
- `user_ne_abort`: a code block's symbol is not the stack abort's.

`Names.user` is not injective (`mangle` escapes a character `c` as
`_u<hex>_`, which a name may also spell out), so a callee is named up to
its symbol: `Names.user dg.name = Names.user g`.
-/
import Spike.Lib.LowerShapeC1
import Spike.Lib.LowerProgC1Core

namespace Spike.Lib.LowerCallee

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Spike.Lib.LowerShape (allInsts lowerC_atom_inv lowerC_add_inv lowerC_sub_inv lowerC_call_inv
  lowerC_ifeq_inv lowerC_ret_inv)

/-! ## The code blocks before the caller -/

/-- **The `j`th code block of a `decls1` list** is `decl1` with the names
of the code blocks before it, the latest first, then `E`. -/
theorem decl1_take : ∀ (p : Prog) (E : List String), decls1 E p = true →
    ∀ (j : Nat) (hj : j < p.length), decl1 (((p.take j).map (·.name)).reverse ++ E) p[j] = true
  | [], _, _, j, hj => absurd hj (by simp)
  | d :: ds, E, h, 0, _ => by
    simp only [decls1, Bool.and_eq_true] at h
    simpa using h.1
  | d :: ds, E, h, j + 1, hj => by
    simp only [decls1, Bool.and_eq_true] at h
    have := decl1_take ds (d.name :: E) h.2 j (by simpa using hj)
    simpa using this

/-- **A name before the `j`th code block** is that of a code block at a
smaller index. -/
theorem mem_earlier_index {p : Prog} {j : Nat} {g : String}
    (h : g ∈ ((p.take j).map (·.name)).reverse ++ []) :
    ∃ j', ∃ hj' : j' < p.length, j' < j ∧ p[j'].name = g := by
  simp only [List.append_nil, List.mem_reverse, List.mem_map] at h
  obtain ⟨d, hd, rfl⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
  simp only [List.length_take] at hi
  exact ⟨i, by omega, by omega, by simp⟩

/-! ## The calls of the closed form -/

/-- **A call of the closed form**: a `call` instruction is of the stack
abort (`Names.abort`) or of a code block of `earlier`. -/
def CallOk (earlier : List String) (i : Inst) : Prop :=
  ∀ ds f ws, i = .call ds f ws → f = Names.abort ∨ ∃ g ∈ earlier, f = Names.user g

theorem callOk_of_not_call {earlier : List String} {i : Inst} (h : ∀ ds f ws, i ≠ .call ds f ws) :
    CallOk earlier i :=
  fun ds f ws he => absurd he (h ds f ws)

/-- **Every instruction of the closed form of an `Accepted1` body** is
`CallOk`: its calls are of the stack abort (the depth counter's
`deepBlock`) or of a code block of `earlier` (`body1`'s `callee1`). -/
theorem lowerC_callOk (cx : Scc.Lower.Ctx) {earlier : List String} :
    ∀ (e : Expr) (scope : List String) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res1),
      lowerC cx env n l k e = some r → body1 earlier scope e = true → ∀ i ∈ allInsts r, CallOk earlier i := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope env n l k r hr hb
    cases op with
    | atom a =>
      obtain ⟨t, w, r', -, -, hr', rfl⟩ := lowerC_atom_inv hr
      simp only [body1, atom1, Bool.and_eq_true] at hb
      exact fun i hi => ih _ _ _ _ _ r' hr' hb.2 i hi
    | add a b =>
      obtain ⟨-, p, -, q, r', -, -, hr', rfl⟩ := lowerC_add_inv hr
      simp only [body1, atom1, Bool.and_eq_true] at hb
      have ih' := ih _ _ _ _ _ _ hr' hb.2
      intro i hi
      simp only [allInsts, List.cons_append, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact callOk_of_not_call (by intros; simp)
      · exact ih' i hi
    | sub a b =>
      obtain ⟨-, p, -, q, r', -, -, hr', rfl⟩ := lowerC_sub_inv hr
      simp only [body1, atom1, Bool.and_eq_true] at hb
      have ih' := ih _ _ _ _ _ _ hr' hb.2
      intro i hi
      simp only [allInsts, List.cons_append, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact callOk_of_not_call (by intros; simp)
      · exact ih' i hi
    | call g is a ts =>
      obtain ⟨dg, t, w, -, -, -, -, h⟩ := lowerC_call_inv hr
      simp only [body1, callee1, atom1, Bool.and_eq_true] at hb
      have hg : g ∈ earlier := by simpa using hb.1.1.1.1.1
      have hcall : ∀ d, CallOk earlier (.call d (Names.user g) [w]) := by
        intro d ds f ws he
        cases he
        exact .inr ⟨g, hg, rfl⟩
      rcases h with ⟨-, r', hr', rfl⟩ | ⟨fr, r', -, hr', rfl⟩
      · have ih' := ih _ _ _ _ _ _ hr' hb.2
        intro i hi
        simp only [allInsts, List.cons_append, List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact hcall _
        · exact ih' i hi
      · have ih' := ih _ _ _ _ _ _ hr' hb.2
        intro i hi
        simp only [allInsts, List.flatMap_cons, List.mem_append] at hi
        rcases hi with hi | (hi | (hi | hi) | hi)
        · simp only [depthPre, List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> exact callOk_of_not_call (by intros; simp)
        · simp only [deepBlock, List.mem_cons, List.mem_nil_iff, or_false] at hi
          subst hi
          intro ds f ws he
          cases he
          exact .inl rfl
        · simp only [callPost, List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl
          · exact callOk_of_not_call (by intros; simp)
          · exact hcall _
          · exact callOk_of_not_call (by intros; simp)
          · exact callOk_of_not_call (by intros; simp)
        · exact ih' i (List.mem_append_left _ hi)
        · exact ih' i (List.mem_append_right _ hi)
    | _ => simp [lowerC] at hr
  | ifeq a b yes no ihy ihn =>
    intro scope env n l k r hr hb
    obtain ⟨-, p, -, q, ry, rn, -, -, hy, hn, rfl⟩ := lowerC_ifeq_inv hr
    simp only [body1, atom1, Bool.and_eq_true] at hb
    have hy' := ihy _ _ _ _ _ _ hy hb.1.2
    have hn' := ihn _ _ _ _ _ _ hn hb.2
    intro i hi
    have : i ∈ allInsts ry ∨ i ∈ allInsts rn := by
      simp only [allInsts, List.nil_append, List.flatMap_cons, List.flatMap_append, List.mem_append] at hi ⊢
      exact hi
    rcases this with h | h
    · exact hy' i h
    · exact hn' i h
  | ret a =>
    intro scope env n l k r hr hb
    obtain ⟨t, ws, -, rfl⟩ := lowerC_ret_inv hr
    simp [allInsts]
  | _ => intro scope env n l k r hr; simp [lowerC] at hr

/-- **A code block's symbol is not the stack abort's** (`wc_…` against
`scc_rt_…`). -/
theorem user_ne_abort (g : String) : Names.user g ≠ Names.abort := by
  intro h
  have := congrArg (fun s : String => s.toList.head?) h
  simp [Names.user, Names.abort, String.toList_append] at this

end Spike.Lib.LowerCallee
