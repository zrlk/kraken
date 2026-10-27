import Spike.Lib.Src.NJ2Srun

/-!
**The lowering's code-free `let`s are `sstep`s at `ofEnv2`** (ISA-neutral):
where the lowering's own `let` step (`letStep`) succeeds on an atom, a
`nameI`, a pair, a `pack`/`packT` or the `asLanes` of a literal, the
symbolic step `Form.sstep` at the grouped symbolic environment (`ofEnv2`)
reaches the continuation at the grouped environment the lowering extends,
every binding still grouping (`GrpOk`).

- `GrpOk`, `GrpOk.cons`, `ofEnv2_cons`;
- `post_evalAtV`, `post_evalOneV`: the lowering's atom evaluation is `atomV`;
- `sevalAt_ofEnv2`: an atom's symbolic placements group its operands;
- `sstep_let_atom`, `sstep_let_nameI`, `sstep_let_pair`, `sstep_let_pack`,
  `sstep_let_packT`, `sstep_let_asLanes`.

A package's type groups its operands as the packed atom's type does only
under a premise (`group τ ws = group t ws`): placements depend on the type's
layout, which `pack` may change through refinements and binders.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (B Env lowerOp)
open Scc.Lower.Inv (atomV)
open Spike.Lib.Form (SEnv sevalAt sstep lookupS WordPl group grp)

/-- **Every binding's operands group** into placements. -/
def GrpOk (env : Env) : Prop := ∀ b ∈ env, (group b.2.1 b.2.2).isSome = true

theorem GrpOk.cons {env : Env} (h : GrpOk env) {x : String} {t : Ty} {ws : List Operand}
    (hg : (group t ws).isSome = true) : GrpOk ((x, t, ws) :: env) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hg
  · exact h b hb

theorem ofEnv2_cons {env : Env} {x : String} {t : Ty} {ws : List Operand} {pls : List WordPl}
    (h : group t ws = some pls) : ofEnv2 ((x, t, ws) :: env) = (x, t, pls) :: ofEnv2 env := by
  simp [ofEnv2, h]

/-! ## The lowering's atom evaluation -/

theorem post_evalAtV (env : Env) (a : At) : Post (Scc.Lower.evalAt env a) fun r => atomV env a = some r := by
  cases a with
  | var x =>
    show Post (Scc.Lower.lookupV env x) _
    refine Post.mono (post_lookupV env x) fun r ⟨b, hb, hr⟩ => ?_
    subst hr
    simp [atomV, hb]
  | lit n =>
    show Post (if n ≥ 2 ^ 64 then _ else _) _
    split
    · exact Post.throw
    · rename_i hn
      exact Post.pure (by simp [atomV, hn])
  | unit => exact Post.pure rfl

theorem post_evalOneV (env : Env) (a : At) (what : String) :
    Post (Scc.Lower.evalOne env a what) fun o => ∃ t, atomV env a = some (t, [o]) := by
  unfold Scc.Lower.evalOne
  exact Post.bind (post_evalAtV env a) fun r hr => Post.mono (post_one _ _) fun o ho => ⟨r.1, by rw [hr, ← ho]⟩

/-- **An atom's symbolic placements group its operands.** -/
theorem sevalAt_ofEnv2 {env : Env} (hg : GrpOk env) {a : At} {t : Ty} {ws : List Operand}
    (h : atomV env a = some (t, ws)) : ∃ pls, group t ws = some pls ∧ sevalAt (ofEnv2 env) a = some (t, pls) := by
  cases a with
  | var x =>
    simp only [atomV, Option.map_eq_some_iff] at h
    obtain ⟨⟨y, u, vs⟩, hf, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨pls, hp⟩ := Option.isSome_iff_exists.mp (hg _ (List.mem_of_find?_eq_some hf))
    refine ⟨pls, hp, ?_⟩
    simp only [sevalAt, lookupS_ofEnv2, hf, Option.map_some]
    simp only at hp
    rw [hp]; rfl
  | lit n =>
    simp only [atomV] at h
    split at h
    · cases h
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hn' : n < 2 ^ 64 := by omega
      exact ⟨_, rfl, by simp [sevalAt, hn', Scc.Lower.imm]⟩
  | unit =>
    simp only [atomV, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩

/-! ## The code-free `let`s -/

section Lets

variable {cx : Scc.Lower.Ctx} {env : Env} {x : String} {e : Expr} {n n' : Nat} {t : Ty} {ws : List Operand}

theorem sstep_let_atom {a : At} (hg : GrpOk env)
    (hs : runB (letStep cx env x (.atom a) e) n = some ((t, ws), n')) :
    sstep (ofEnv2 env) (.let_ x (.atom a) e) = some (e, ofEnv2 ((x, t, ws) :: env)) ∧
      GrpOk ((x, t, ws) :: env) := by
  have hpost : Post (lowerOp cx env x (.atom a)) fun r => atomV env a = some r := by
    simp only [lowerOp]; exact post_evalAtV env a
  have hv : atomV env a = some (t, ws) := post_runB (post_letStep hpost) hs
  obtain ⟨pls, hp, ha⟩ := sevalAt_ofEnv2 hg hv
  exact ⟨by simp [sstep, ha, ofEnv2_cons hp], hg.cons (by simp [hp])⟩

theorem sstep_let_nameI {a : At} (hg : GrpOk env)
    (hs : runB (letStep cx env x (.nameI a) e) n = some ((t, ws), n')) :
    sstep (ofEnv2 env) (.let_ x (.nameI a) e) = some (e, ofEnv2 ((x, t, ws) :: env)) ∧
      GrpOk ((x, t, ws) :: env) := by
  have hpost : Post (lowerOp cx env x (.nameI a)) fun r => atomV env a = some r := by
    simp only [lowerOp]; exact post_evalAtV env a
  have hv : atomV env a = some (t, ws) := post_runB (post_letStep hpost) hs
  obtain ⟨pls, hp, ha⟩ := sevalAt_ofEnv2 hg hv
  exact ⟨by simp [sstep, ha, ofEnv2_cons hp], hg.cons (by simp [hp])⟩

theorem sstep_let_pair {a b : At} (hg : GrpOk env)
    (hs : runB (letStep cx env x (.pair a b) e) n = some ((t, ws), n')) :
    sstep (ofEnv2 env) (.let_ x (.pair a b) e) = some (e, ofEnv2 ((x, t, ws) :: env)) ∧
      GrpOk ((x, t, ws) :: env) := by
  have hpost : Post (lowerOp cx env x (.pair a b)) fun r =>
      ∃ ta wa tb wb, atomV env a = some (ta, wa) ∧ atomV env b = some (tb, wb) ∧ r = (.prod ta tb, wa ++ wb) := by
    simp only [lowerOp]
    refine Post.bind (post_evalAtV env a) fun r1 h1 => ?_
    obtain ⟨ta, wa⟩ := r1
    refine Post.bind (post_evalAtV env b) fun r2 h2 => ?_
    obtain ⟨tb, wb⟩ := r2
    exact Post.pure ⟨ta, wa, tb, wb, h1, h2, rfl⟩
  obtain ⟨ta, wa, tb, wb, h1, h2, hr⟩ := post_runB (post_letStep hpost) hs
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  obtain ⟨p, hp, ha⟩ := sevalAt_ofEnv2 hg h1
  obtain ⟨q, hq, hb⟩ := sevalAt_ofEnv2 hg h2
  have hpq := group_pair hp hq
  exact ⟨by simp [sstep, ha, hb, ofEnv2_cons hpq], hg.cons (by simp [hpq])⟩

/-- A `pack`, its type grouping the packed operands as the atom's type does. -/
theorem sstep_let_pack {a : At} {w : String} {τ : Ty} (hg : GrpOk env)
    (hs : runB (letStep cx env x (.pack a w τ) e) n = some ((t, ws), n'))
    (hτ : ∀ ta wa, atomV env a = some (ta, wa) → group τ wa = group ta wa) :
    sstep (ofEnv2 env) (.let_ x (.pack a w τ) e) = some (e, ofEnv2 ((x, t, ws) :: env)) ∧
      GrpOk ((x, t, ws) :: env) := by
  have hpost : Post (lowerOp cx env x (.pack a w τ)) fun r =>
      ∃ ta, atomV env a = some (ta, r.2) ∧ r.1 = τ := by
    simp only [lowerOp]
    exact Post.bind (post_evalAtV env a) fun r1 h1 => Post.pure ⟨r1.1, h1, rfl⟩
  obtain ⟨ta, h1, hr⟩ := post_runB (post_letStep hpost) hs
  simp only at h1 hr
  subst hr
  obtain ⟨p, hp, ha⟩ := sevalAt_ofEnv2 hg h1
  have hp' : group t ws = some p := by rw [hτ _ _ h1, hp]
  exact ⟨by simp [sstep, ha, close_nil, ofEnv2_cons hp'], hg.cons (by simp [hp'])⟩

/-- A `packT`, as `pack`. -/
theorem sstep_let_packT {a : At} {σ τ : Ty} (hg : GrpOk env)
    (hs : runB (letStep cx env x (.packT a σ τ) e) n = some ((t, ws), n'))
    (hτ : ∀ ta wa, atomV env a = some (ta, wa) → group τ wa = group ta wa) :
    sstep (ofEnv2 env) (.let_ x (.packT a σ τ) e) = some (e, ofEnv2 ((x, t, ws) :: env)) ∧
      GrpOk ((x, t, ws) :: env) := by
  have hpost : Post (lowerOp cx env x (.packT a σ τ)) fun r =>
      ∃ ta, atomV env a = some (ta, r.2) ∧ r.1 = τ := by
    simp only [lowerOp]
    exact Post.bind (post_evalAtV env a) fun r1 h1 => Post.pure ⟨r1.1, h1, rfl⟩
  obtain ⟨ta, h1, hr⟩ := post_runB (post_letStep hpost) hs
  simp only at h1 hr
  subst hr
  obtain ⟨p, hp, ha⟩ := sevalAt_ofEnv2 hg h1
  have hp' : group t ws = some p := by rw [hτ _ _ h1, hp]
  exact ⟨by simp [sstep, ha, close_nil, ofEnv2_cons hp'], hg.cons (by simp [hp'])⟩

/-- The `asLanes` of a literal: its immediate. -/
theorem sstep_let_asLanes {sg : Bool} {w : Wd} {k : Nat} (hg : GrpOk env)
    (hs : runB (letStep cx env x (.asLanes sg w (.lit k)) e) n = some ((t, ws), n')) :
    sstep (ofEnv2 env) (.let_ x (.asLanes sg w (.lit k)) e) = some (e, ofEnv2 ((x, t, ws) :: env)) ∧
      GrpOk ((x, t, ws) :: env) := by
  have hpost : Post (lowerOp cx env x (.asLanes sg w (.lit k))) fun r =>
      ∃ o u, atomV env (.lit k) = some (u, [o]) ∧ r = (.lanes sg w, [o]) := by
    simp only [lowerOp]
    exact Post.bind (post_evalOneV env _ _) fun o ⟨u, hu⟩ => Post.pure ⟨o, u, hu, rfl⟩
  obtain ⟨o, u, h1, hr⟩ := post_runB (post_letStep hpost) hs
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  simp only [atomV] at h1
  split at h1
  · cases h1
  · rename_i hk
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h1
    obtain ⟨-, rfl⟩ := h1
    have hk' : k < 2 ^ 64 := by omega
    have hp : group (.lanes sg w) [Scc.Lower.imm k] = some [.one (Scc.Lower.imm k)] := rfl
    rw [ofEnv2_cons hp]
    exact ⟨by simp [sstep, hk', Scc.Lower.imm], hg.cons (by simp [hp])⟩

end Lets

end Spike.Lib.LowerNode
