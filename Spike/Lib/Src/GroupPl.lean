/-
**Placements at a lowering environment** (ISA-neutral): what `group`
makes of a one-operand atom and of a buffer's two operands, and an atom's
placements at `ofEnv2` when the bindings found group (`GrpL`).

- `grp_opds`: `grp` places exactly the operands it consumes;
- `group_one`: one operand is one word `.one w`;
- `group_buf`: a buffer's operands `[base, off]` (`refO`) are one locative;
- `sevalAt_ofEnv2G`, `sevalAt_ofEnv2G_one`: an atom at `ofEnv2` under
  `GrpL`;
- `fresh_ofEnv2`: `ofEnv2`'s placed registers are off `regName x n`.
-/
import Spike.Lib.Src.LitPt2
import Spike.Lib.Src.AbortImm2
import Spike.Lib.LowerShapeC2
import Spike.Lib.LowerEnv

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib.Form (sevalAt lookupS WordPl grp group)
open Spike.Lib.LowerShape (refO)
open Scc.Lower.Inv (atomV regName)

/-- **`grp` places exactly the operands it consumes**, in order. -/
theorem grp_opds : ∀ (t : Ty) (os : List Scc.IR.Operand) (p : List WordPl) (r : List Scc.IR.Operand),
    grp t os = some (p, r) → p.flatMap WordPl.opds ++ r = os := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro os p r h
    simp only [grp, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨p1, r1⟩, h1, ⟨p2, r2⟩, h2, h3⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    rw [List.flatMap_append, List.append_assoc, ihb _ _ _ h2, iha _ _ _ h1]
  | refine t _ ih => intro os p r h; exact ih os p r h
  | iall t ih => intro os p r h; exact ih os p r h
  | mu t ih => intro os p r h; exact ih os p r h
  | iex b ih =>
    intro os p r h
    simp only [grp] at h
    split at h
    · cases h
    · exact ih os p r h
  | tex s b ih =>
    intro os p r h
    simp only [grp] at h
    split at h
    · cases h
    · exact ih os p r h
  | _ =>
    intro os p r h
    first
      | (simp only [grp, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl)
      | (rcases os with _ | ⟨o, os⟩ <;> simp only [grp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
         obtain ⟨rfl, rfl⟩ := h; rfl)
      | (rcases os with _ | ⟨o, _ | ⟨o', os⟩⟩ <;> simp only [grp, Option.some.injEq, Prod.mk.injEq,
           reduceCtorEq] at h
         obtain ⟨rfl, rfl⟩ := h; rfl)
      | simp [grp] at h

/-- **One operand groups as one word.** -/
theorem group_one {t : Ty} {w : Scc.IR.Operand} {p : List WordPl} (h : group t [w] = some p) : p = [.one w] := by
  have hg : grp t [w] = some (p, []) := by
    simp only [group] at h
    split at h
    · rename_i pls hg; simp only [Option.some.injEq] at h; subst h; exact hg
    · simp at h
  have he := grp_opds t [w] p [] hg
  rw [List.append_nil] at he
  match p, he with
  | [.one o], he => simp [WordPl.opds] at he; rw [he]
  | [.loc _ _], he => simp [WordPl.opds] at he
  | [], he => simp at he
  | a :: b :: _, he => cases a <;> cases b <;> simp [WordPl.opds, List.flatMap_cons] at he

/-- **A buffer's placement**: a locative type's two operands `[base, off]`
(`refO`) group as one locative word. -/
theorem group_buf {t : Ty} {bw : List Scc.IR.Operand} {μ : Mode} {u : Ty} {rb : Scc.IR.Reg} {o : UInt64}
    {pls : List WordPl} (hb : Scc.Lower.bufElem t = some (μ, u)) (hrf : refO bw = some (.reg rb, .imm o))
    (hg : group t bw = some pls) : pls = [.loc (.reg rb) (.imm o)] := by
  have hg' : grp t bw = some (pls, []) := by
    simp only [group] at hg
    split at hg
    · rename_i q hq; simp only [Option.some.injEq] at hg; subst hg; exact hq
    · simp at hg
  have hloc : ∀ b0 b1, grp t [b0, b1] = some ([.loc b0 b1], []) := by
    intro b0 b1
    unfold Scc.Lower.bufElem at hb
    split at hb <;> simp_all [grp]
  match bw, hrf with
  | [b0, b1], hrf =>
    simp only [refO, Option.some.injEq, Prod.mk.injEq] at hrf
    obtain ⟨rfl, rfl⟩ := hrf
    rw [hloc] at hg'
    simp only [Option.some.injEq, Prod.mk.injEq] at hg'
    exact hg'.1.symm
  | [b0], hrf =>
    simp only [refO, Option.some.injEq, Prod.mk.injEq] at hrf
    obtain ⟨rfl, h⟩ := hrf
    -- a one-operand `refO` has offset `imm 0`; a locative takes two operands
    unfold Scc.Lower.bufElem at hb
    split at hb <;> simp_all [grp]

/-- **An atom's placements at a grouped lowering environment** (`GrpL`: the
bindings found group). -/
theorem sevalAt_ofEnv2G {env : Scc.Lower.Env} (hg : GrpL env) {a : At} {t : Ty} {ws : List Scc.IR.Operand}
    (h : atomV env a = some (t, ws)) : ∃ pls, group t ws = some pls ∧ sevalAt (ofEnv2 env) a = some (t, pls) := by
  cases a with
  | var x =>
    simp only [atomV, Option.map_eq_some_iff] at h
    obtain ⟨⟨y, u, vs⟩, hf, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨pls, hp⟩ := Option.isSome_iff_exists.mp (hg x _ hf)
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

/-- **A one-operand atom at a grouped lowering environment** is one word at
its operand. -/
theorem sevalAt_ofEnv2G_one {env : Scc.Lower.Env} (hg : GrpL env) {a : At} {t : Ty} {w : Scc.IR.Operand}
    (h : atomV env a = some (t, [w])) : sevalAt (ofEnv2 env) a = some (t, [.one w]) := by
  obtain ⟨pls, hp, hs⟩ := sevalAt_ofEnv2G hg h
  rw [group_one hp] at hs; exact hs

/-- **`ofEnv2`'s placed registers are off `regName x n`** (`Fresh`). -/
theorem fresh_ofEnv2 {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) (x : String) :
    ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ regName x n := by
  intro q hq pl hpl o ho r hr
  simp only [ofEnv2, List.mem_map] at hq
  obtain ⟨b, hb, rfl⟩ := hq
  cases hg : group b.2.1 b.2.2 with
  | none => simp [hg] at hpl
  | some pls =>
    simp only [hg, Option.getD_some] at hpl
    have hg' : grp b.2.1 b.2.2 = some (pls, []) := by
      simp only [group] at hg
      split at hg
      · rename_i q hq; simp only [Option.some.injEq] at hg; subst hg; exact hq
      · simp at hg
    have he := grp_opds _ _ _ _ hg'
    rw [List.append_nil] at he
    have hmem : o ∈ b.2.2 := he ▸ List.mem_flatMap.mpr ⟨pl, hpl, ho⟩
    exact h b hb o hmem r hr x n (Nat.le_refl n)

end Spike.Lib.LowerNode
