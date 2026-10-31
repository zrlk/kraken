import WeakCore.PairNat
import WeakCore.CopyPlan
namespace TermSound.Flat

/-! **EtaC**: codes of per-position label maps, for the box variants.

A payload position map sends each position to one of `σ`, `cpy`, or `fun y => bv y k` (a nested variant with
code `k`).  `enc` codes the map on the first `len` positions as a `Nat`; `dec` recovers it.  Only the round trip
`dec (enc G len) j = G j` (for `j < len` and `G` of the three-way shape) is needed. -/

namespace PCode
open NatPair

theorem pr_ge (x m : Nat) : m ≤ pr x m := by
  unfold pr
  have h2 : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have := Nat.mul_le_mul_right (2 * m + 1) h2
  omega

open Classical in
noncomputable def unpair (e : Nat) : Nat × Nat :=
  if h : ∃ p : Nat × Nat, pr p.1 p.2 = e then Classical.choose h else (0, 0)

theorem unpair_pr (x m : Nat) : unpair (pr x m) = (x, m) := by
  unfold unpair
  have h : ∃ p : Nat × Nat, pr p.1 p.2 = pr x m := ⟨(x, m), rfl⟩
  rw [dif_pos h]
  obtain ⟨e1, e2⟩ := pr_inj (Classical.choose_spec h)
  exact Prod.ext e1 e2

/-- A list of tags as one number (`0` = empty). -/
def encL : List Nat → Nat
  | [] => 0
  | t :: ts => pr t (encL ts) + 1

/-- Fuelled decoder (`encL ts` is enough fuel). -/
noncomputable def decLf : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, k + 1 => (unpair k).1 :: decLf f (unpair k).2

noncomputable def decL (k : Nat) : List Nat := decLf k k

theorem encL_ge_length : ∀ ts : List Nat, ts.length ≤ encL ts
  | [] => Nat.le_refl _
  | t :: ts => by
    show ts.length + 1 ≤ pr t (encL ts) + 1
    have := encL_ge_length ts; have := pr_ge t (encL ts); omega

theorem decLf_encL : ∀ (ts : List Nat) (f : Nat), ts.length ≤ f → decLf f (encL ts) = ts
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | t :: ts, f + 1, h => by
    show decLf (f + 1) (pr t (encL ts) + 1) = t :: ts
    simp only [decLf, unpair_pr]
    exact congrArg _ (decLf_encL ts f (by simpa using h))

theorem decL_encL (ts : List Nat) : decL (encL ts) = ts := decLf_encL ts _ (encL_ge_length ts)

section
variable (σ cpy : WeakMem.AllocLabel → WeakMem.AllocLabel) (bv : Nat → Nat → WeakMem.AllocLabel)

/-- One tag back to a label map. -/
noncomputable def entry : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel
  | 0 => σ
  | 1 => cpy
  | e + 2 => fun y => bv y (unpair e).2

open Classical in
noncomputable def tagOf (g : WeakMem.AllocLabel → WeakMem.AllocLabel) : Nat :=
  if g = σ then 0 else if g = cpy then 1 else
    if h : ∃ k, g = fun y => bv y k then pr 0 (Classical.choose h) + 2 else 0

noncomputable def enc (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (len : Nat) : Nat :=
  encL ((List.range len).map (fun j => tagOf σ cpy bv (G j)))

noncomputable def dec (k : Nat) : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel :=
  fun j => match (decL k)[j]? with
    | some e => entry σ cpy bv e
    | none => σ

/-- The three-way shape of a position map. -/
def Ok3 (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (len : Nat) : Prop :=
  ∀ j, j < len → G j = σ ∨ G j = cpy ∨ ∃ k, G j = fun y => bv y k

theorem entry_tagOf {g : WeakMem.AllocLabel → WeakMem.AllocLabel}
    (h : g = σ ∨ g = cpy ∨ ∃ k, g = fun y => bv y k) : entry σ cpy bv (tagOf σ cpy bv g) = g := by
  unfold tagOf
  by_cases h0 : g = σ
  · rw [if_pos h0]; exact h0.symm
  rw [if_neg h0]
  by_cases h1 : g = cpy
  · rw [if_pos h1]; exact h1.symm
  rw [if_neg h1]
  have hex : ∃ k, g = fun y => bv y k := by
    rcases h with h | h | h
    · exact absurd h h0
    · exact absurd h h1
    · exact h
  rw [dif_pos hex]
  show (fun y => bv y (unpair (pr 0 (Classical.choose hex))).2) = g
  rw [unpair_pr]
  exact (Classical.choose_spec hex).symm

theorem dec_enc {G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} {len : Nat} (hG : Ok3 σ cpy bv G len)
    {j : Nat} (hj : j < len) : dec σ cpy bv (enc σ cpy bv G len) j = G j := by
  unfold dec enc
  rw [decL_encL]
  have hr : (List.range len)[j]? = some j := by
    rw [List.getElem?_eq_getElem (by simpa using hj)]; simp
  rw [List.getElem?_map, hr]
  simp only [Option.map_some]
  exact entry_tagOf σ cpy bv (hG j hj)

end
end PCode
end TermSound.Flat
