/-
**The ISA-neutral part of the mask machinery**. `EnvG/X64MaskCore.lean` and
`EnvG/A64MaskCore.lean` are copies of each other, over the two ISAs' `Directive`; the
statements that do not mention a directive are stated here once, and the two
files' names are aliases (`hoist_alias`):

- `Forall2`, `Forall2.imp`, `Forall2.map`: two lists related cell by cell
  (core Lean has no `List.Forall₂`);
- `forall₂_dropWhile`, `forall₂_findSome?`, `forall₂_of_getElem`,
  `forall₂_getElem?`: `Forall2` through the list operations the mask proofs
  use (the cells from an address, the labels, the cells by index);
- `evTree_map_map`: `EvTree.map` composes (the thread's tree at a cell the
  mask shares, up to the executable in its states).

The directive-specific part (`CellMask`, `MaskOf`, `labels_mask`,
`instrStepEnv_of_mask`, `exec_of_mask`, `Program.maskKeep`, …) stays in the
two ISA files: `Executable.labels`, `codeAt`, `instrStepEnv` and `Program`
are per-ISA constants.
-/
import Kraken.Promising.Basic
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.SLR.EnvG.MaskCommon

open Kraken.Promising

/-! ## Two lists related cell by cell -/

/-- Two lists related cell by cell (core Lean has no `List.Forall₂`). -/
inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {x y l l'} : R x y → Forall2 R l l' → Forall2 R (x :: l) (y :: l')

theorem Forall2.imp {α β : Type} {R S : α → β → Prop} (h : ∀ x y, R x y → S x y) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 S l l'
  | _, _, .nil => .nil
  | _, _, .cons hxy hl => .cons (h _ _ hxy) (hl.imp h)

theorem Forall2.map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (h : ∀ x y, R x y → S (f x) (g y)) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 S (l.map f) (l'.map g)
  | _, _, .nil => .nil
  | _, _, .cons hxy hl => .cons (h _ _ hxy) (hl.map h)

/-! ## List helpers -/

theorem forall₂_dropWhile {α β : Type} {R : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ x y, R x y → p x = q y) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 R (l.dropWhile p) (l'.dropWhile q)
  | _, _, .nil => .nil
  | x :: _, y :: _, .cons hxy h => by
    simp only [List.dropWhile_cons, hpq x y hxy]
    split
    · exact forall₂_dropWhile hpq h
    · exact .cons hxy h

theorem forall₂_findSome? {α β γ : Type} {R : α → β → Prop} {f : α → Option γ} {g : β → Option γ}
    (hfg : ∀ x y, R x y → f x = g y) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → l.findSome? f = l'.findSome? g
  | _, _, .nil => rfl
  | x :: _, y :: _, .cons hxy h => by
    simp only [List.findSome?_cons, hfg x y hxy]
    split
    · rfl
    · exact forall₂_findSome? hfg h

theorem forall₂_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length → (∀ i (h : i < l.length) (h' : i < l'.length), R l[i] l'[i]) →
      Forall2 R l l'
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: l, y :: l', h, hR =>
    .cons (hR 0 (by simp) (by simp))
      (forall₂_of_getElem (by simpa using h) fun i h1 h2 => hR (i + 1) (by simpa using h1) (by simpa using h2))

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → ∀ (i : Nat) {y : β}, l'[i]? = some y →
      ∃ x, l[i]? = some x ∧ R x y
  | _, _, .nil, _, _, h => by simp at h
  | x :: _, _ :: _, .cons hxy _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨x, rfl, hxy⟩
  | _ :: _, _ :: _, .cons _ hl, i + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem? hl i h

/-! ## Trees -/

/-- `EvTree.map` composes. -/
theorem evTree_map_map {σ τ υ : Type} (f : σ → τ) (g : τ → υ) :
    ∀ t : EvTree σ, (t.map f).map g = t.map (g ∘ f)
  | .done _ => rfl
  | .fault _ => rfl
  | .choose _ k => by simp only [EvTree.map]; congr 1; funext i; exact evTree_map_map f g (k i)
  | .load _ _ _ ret => by simp only [EvTree.map]; congr 1; funext v; exact evTree_map_map f g (ret v)
  | .store _ _ _ _ ret => by simp only [EvTree.map]; congr 1; funext v; exact evTree_map_map f g (ret v)
  | .rmw _ _ _ _ ret => by simp only [EvTree.map]; congr 1; funext v; exact evTree_map_map f g (ret v)
  | .fence _ ret => by simp only [EvTree.map]; congr 1; funext v; exact evTree_map_map f g (ret v)

end Kraken.Promising.SLR.EnvG.MaskCommon
