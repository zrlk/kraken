import Spike.Lib.Src.SstepLet

/-!
**Placements follow the layout shape** (ISA-neutral). These are two
type-shape facts about `Accepted2`'s types (`simpleTy`, no coupled pair):

- `grpL`, `groupL`, `grp_grpL`, `group_grpL`: a type compatible with a layout
  (`Compat t L`) groups operands as the layout does. A `pack` that
  `layoutOk2` admits (`layQ`: the atom's layout erased is `shapeOf τ`)
  therefore groups its operands at `τ` as at the atom's type:
  `group_pack_of_layQ` discharges `sstep_let_pack`'s premise.
- `width_simple`, `rawWords_simple`, `accs_simple`, `accsPl_simple`,
  `plLen_of_slots`, `accsPl_of_valWords`: for a
  `simpleTy` type with placements, `sstep`'s split count
  (`TermRun.accs`, whose index packages with two or more index uses count
  their closed width) equals the placements' count (`plLen`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (Env LitV shapeOf simpleTy litAt)
open Scc.Lower.Inv (atomV)
open Spike.Lib.Form (WordPl grp group)

/-! ## Grouping by layout -/

/-- **The placements of a layout** (as `grp`: a leaf one operand, a locative
two). -/
def grpL : LitV → List Operand → Option (List WordPl × List Operand)
  | .nil, os => some ([], os)
  | .leaf _, o :: os => some ([.one o], os)
  | .loc, b :: off :: os => some ([.loc b off], os)
  | .node l r, os => do
      let (p, os) ← grpL l os
      let (q, os) ← grpL r os
      pure (p ++ q, os)
  | _, _ => none

theorem grpL_erase : ∀ (L : LitV) (os : List Operand), grpL L.erase os = grpL L os := by
  intro L
  induction L with
  | nil => intro os; rfl
  | leaf o => intro os; cases os <;> rfl
  | loc => intro os; rfl
  | node l r ihl ihr => intro os; simp only [LitV.erase, grpL, ihl, ihr]

/-- **A compatible type groups as its layout.** -/
theorem grp_grpL : ∀ (t : Ty) (L : LitV), Compat t L = true → ∀ os, grp t os = grpL L os := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L hc os
    cases L <;> simp only [Compat, Bool.false_eq_true] at hc
    rename_i l r
    simp only [Bool.and_eq_true] at hc
    simp only [grp, grpL, iha l hc.1, ihb r hc.2]
  | refine t _ ih => intro L hc os; exact ih L hc os
  | iall t ih => intro L hc os; exact ih L hc os
  | mu t ih => intro L hc os; exact ih L hc os
  | iex b ih =>
    intro L hc os
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at hc
    simp only [grp, hc.1]
    exact ih L hc.2 os
  | tex k b ih =>
    intro L hc os
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at hc
    simp only [grp, hc.1]
    exact ih L hc.2 os
  | _ =>
    intro L hc os
    cases L <;> simp only [Compat, Bool.false_eq_true] at hc <;> cases os <;> try rfl
    all_goals (rename_i o os; cases os <;> rfl)

/-- The placements of a layout with operands exactly `os`. -/
def groupL (L : LitV) (os : List Operand) : Option (List WordPl) :=
  match grpL L os with
  | some (pls, []) => some pls
  | _ => none

theorem groupL_erase (L : LitV) (os : List Operand) : groupL L.erase os = groupL L os := by
  simp only [groupL, grpL_erase]

theorem group_grpL {t : Ty} {L : LitV} (hc : Compat t L = true) (os : List Operand) :
    group t os = groupL L os := by
  unfold group groupL
  rw [grp_grpL t L hc os]
  rcases grpL L os with _ | ⟨p, _ | _⟩ <;> rfl

/-- **`layoutOk2`'s `pack` check makes the packed type group as the atom's
type**, where the atom's binding agrees with the walk's layout
(`RelE`, the atom's variable with a layout). -/
theorem group_pack_of_layQ {x w : String} {a : At} {τ : Ty} {e : Expr} {lits : List (String × LitV)}
    {env : Env} (hL : layQ (.let_ x (.pack a w τ) e, lits) = true) (hR : RelE env lits)
    (ha : ∀ y, a = .var y → (lits.lookup y).isSome = true) :
    ∀ ta wa, atomV env a = some (ta, wa) → group τ wa = group ta wa := by
  intro ta wa hv
  simp only [layQ, Bool.and_eq_true, beq_iff_eq] at hL
  obtain ⟨⟨hsh, hs⟩, hw⟩ := hL
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hw
  have hcτ : Compat τ (shapeOf τ) = true := compat_shapeOf τ 0 0 hs (slots_of_valWords hk)
  have hca : Compat ta (litAt lits a) = true := by
    cases a with
    | var y =>
      simp only [atomV, Option.map_eq_some_iff] at hv
      obtain ⟨b, hb, hbe⟩ := hv
      obtain ⟨L, hl⟩ := Option.isSome_iff_exists.1 (ha y rfl)
      have hi := (hR y b hb).1 L hl
      simp only [Prod.mk.injEq] at hbe
      obtain ⟨rfl, rfl⟩ := hbe
      simp only [litAt, hl, Option.getD_some]
      exact hi.1
    | lit n =>
      simp only [atomV] at hv
      split at hv
      · cases hv
      · simp only [Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        rfl
    | unit =>
      simp only [atomV, Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      rfl
  rw [group_grpL hcτ, group_grpL hca, ← hsh, groupL_erase]

/-! ## `sstep`'s split count is the placements' -/

theorem closed_mentions : ∀ (w : Idx) (n k : Nat), w.closed = some n → w.mentions k = false := by
  intro w
  induction w with
  | lit m => intro n k _; rfl
  | var j => intro n k h; simp [Idx.closed] at h
  | add i j ihi ihj =>
    intro n k h
    simp only [Idx.closed, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, -⟩ := h
    simp [Idx.mentions, ihi a k ha, ihj b k hb]
  | sub i j ihi ihj =>
    intro n k h
    simp only [Idx.closed, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, -⟩ := h
    simp [Idx.mentions, ihi a k ha, ihj b k hb]
  | smul m i ih =>
    intro n k h
    simp only [Idx.closed, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, -⟩ := h
    simp [Idx.mentions, ih a k ha]

theorem closed_lower : ∀ (w : Idx) (c : Nat), (w.lower c).closed = w.closed := by
  intro w
  induction w with
  | lit m => intro c; rfl
  | var j => intro c; simp only [Idx.lower]; split <;> rfl
  | add i j ihi ihj => intro c; simp [Idx.lower, Idx.closed, ihi, ihj]
  | sub i j ihi ihj => intro c; simp [Idx.lower, Idx.closed, ihi, ihj]
  | smul m i ih => intro c; simp [Idx.lower, Idx.closed, ih]

/-- **A `simpleTy` type has a closed width**, its placements' count where
it has placements. -/
theorem width_simple : ∀ (t : Ty), simpleTy t = true → ∀ ρ : CoreLang.Ctx,
    ∃ w n, (info ρ t).width = some w ∧ w.closed = some n ∧ ∀ m, plLen t = some m → m = n := by
  intro t
  induction t with
  | unit => intro _ ρ; exact ⟨_, 0, rfl, rfl, fun m h => by simp [plLen] at h; omega⟩
  | void => intro _ ρ; exact ⟨_, 0, rfl, rfl, fun m h => by simp [plLen] at h; omega⟩
  | int => intro _ ρ; exact ⟨_, 1, rfl, rfl, fun m h => by simp [plLen] at h; omega⟩
  | intS _ => intro _ ρ; exact ⟨_, 1, rfl, rfl, fun m h => by simp [plLen] at h; omega⟩
  | fix _ _ => intro _ ρ; exact ⟨_, 1, rfl, rfl, fun m h => by simp [plLen] at h; omega⟩
  | lanes _ _ => intro _ ρ; exact ⟨_, 1, rfl, rfl, fun m h => by simp [plLen] at h; omega⟩
  | ptr _ _ => intro _ ρ; exact ⟨_, 1, rfl, rfl, fun m h => by simp [plLen] at h; omega⟩
  | loc _ _ => intro _ ρ; exact ⟨_, 1, rfl, rfl, fun m h => by simp [plLen] at h; omega⟩
  | prod a b iha ihb =>
    intro ht ρ
    simp only [simpleTy, Bool.and_eq_true] at ht
    obtain ⟨wa, na, hwa, hca, hpa⟩ := iha ht.1 ρ
    obtain ⟨wb, nb, hwb, hcb, hpb⟩ := ihb ht.2 ρ
    refine ⟨.add wa wb, na + nb, by simp [info, Info.leaf, hwa, hwb], by simp [Idx.closed, hca, hcb], ?_⟩
    intro m hm
    simp only [plLen, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨ma, hma, mb, hmb, rfl⟩ := hm
    rw [hpa ma hma, hpb mb hmb]
  | refine t _ ih =>
    intro ht ρ
    obtain ⟨w, n, hw, hc, hp⟩ := ih ht ρ
    exact ⟨w, n, hw, hc, fun m hm => hp m hm⟩
  | iex b ih =>
    intro ht ρ
    obtain ⟨w, n, hw, hc, hp⟩ := ih ht ρ.shiftI
    refine ⟨w.lower 0, n, ?_, by rw [closed_lower, hc], ?_⟩
    · simp [info, lowerW, hw, closed_mentions w n 0 hc]
    · intro m hm
      simp only [plLen] at hm
      split at hm
      · cases hm
      · exact hp m hm
  | _ => intro ht; simp [simpleTy] at ht

theorem rawWords_simple {t : Ty} (ht : simpleTy t = true) :
    ∃ n, t.rawWords = some n ∧ ∀ m, plLen t = some m → m = n := by
  obtain ⟨w, n, hw, hc, hp⟩ := width_simple t ht Ty.top
  exact ⟨n, by simp [Ty.rawWords, Ty.width, hw, hc], hp⟩

/-- **`sstep`'s split count of a `simpleTy` type is its placements' count.** -/
theorem accs_simple : ∀ (t : Ty), simpleTy t = true → ∀ m, plLen t = some m →
    (TermRun.accs t).map TermRun.nWords = some m := by
  intro t
  induction t with
  | unit => intro _ m h; simp [plLen] at h; subst h; rfl
  | void => intro _ m h; simp [plLen] at h; subst h; rfl
  | int => intro _ m h; simp [plLen] at h; subst h; rfl
  | intS _ => intro _ m h; simp [plLen] at h; subst h; rfl
  | fix _ _ => intro _ m h; simp [plLen] at h; subst h; rfl
  | lanes _ _ => intro _ m h; simp [plLen] at h; subst h; rfl
  | ptr _ _ => intro _ m h; simp [plLen] at h; subst h; rfl
  | loc _ _ => intro _ m h; simp [plLen] at h; subst h; rfl
  | prod a b iha ihb =>
    intro ht m hm
    simp only [simpleTy, Bool.and_eq_true] at ht
    simp only [plLen, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨ma, hma, mb, hmb, rfl⟩ := hm
    have h1 := iha ht.1 ma hma
    have h2 := ihb ht.2 mb hmb
    rcases hua : TermRun.accs a with _ | ua <;> rw [hua] at h1 <;> simp at h1
    rcases hub : TermRun.accs b with _ | ub <;> rw [hub] at h2 <;> simp at h2
    simp [TermRun.accs, hua, hub, TermRun.nWords, ← h1, ← h2]
  | refine t _ ih => intro ht m hm; exact ih ht m hm
  | iex b ih =>
    intro ht m hm
    have hp := hm
    simp only [plLen] at hm
    split at hm
    · cases hm
    rename_i hcp
    obtain ⟨n, hn, hpn⟩ := rawWords_simple (t := .iex b) ht
    have hmn := hpn m hp
    subst hmn
    simp only [TermRun.accs]
    split
    · rename_i hcnt
      rw [hn]
      split
      · rename_i h0; cases h0; rfl
      · rename_i h1; cases h1; rfl
      · rename_i h2
        cases h2
        exact absurd (by simp [Scc.Obj.coupledPair, hcnt, hn]) hcp
      · exact ih ht _ hm
    · exact ih ht _ hm
  | _ => intro ht; simp [simpleTy] at ht

theorem accsPl_simple {t : Ty} (ht : simpleTy t = true) (hp : (plLen t).isSome = true) : accsPl t = true := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hp
  simp [accsPl, accs_simple t ht m hm, hm]

/-- **A type with a runtime layout has placements.** -/
theorem plLen_of_slots : ∀ (t : Ty) (s r : Nat), (Scc.Obj.slots t s r).isSome = true → (plLen t).isSome = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro s r h
    simp only [Scc.Obj.slots] at h
    rcases ha : Scc.Obj.slots a s r with _ | la
    · simp [ha] at h
    rcases hb : Scc.Obj.slots b (s + la.countP (!·.1)) (r + la.countP (·.1)) with _ | lb
    · simp [ha, hb] at h
    obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.1 (iha s r (by rw [ha]; rfl))
    obtain ⟨mb, hmb⟩ := Option.isSome_iff_exists.1 (ihb _ _ (by rw [hb]; rfl))
    simp [plLen, hma, hmb]
  | refine t _ ih => intro s r h; exact ih s r h
  | iall t ih => intro s r h; exact ih s r h
  | mu t ih => intro s r h; exact ih s r h
  | iex b ih =>
    intro s r h
    simp only [Scc.Obj.slots] at h
    split at h
    · simp at h
    · rename_i hc; simp only [plLen, hc]; exact ih s r h
  | tex k b ih =>
    intro s r h
    simp only [Scc.Obj.slots] at h
    split at h
    · simp at h
    · rename_i hc; simp only [plLen, hc]; exact ih s r h
  | _ => intro s r h; first | rfl | simp [Scc.Obj.slots] at h

/-- **Every `simpleTy` type with a runtime layout has `accsPl`.** -/
theorem accsPl_of_valWords {t : Ty} (ht : simpleTy t = true) {k : Nat} (hk : Scc.Obj.valWords t = some k) :
    accsPl t = true :=
  accsPl_simple ht (plLen_of_slots t 0 0 (slots_of_valWords hk))

end Spike.Lib.LowerNode
