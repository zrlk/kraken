import WeakCore.TermOwnG0Defs

/-!
# TermPubCons: `PubCons` in `PubAt` form (route B)

`TermStep.PubCons th C` (exported by the thread step through `ClaimAtP`) says the step at a
`publish` consumes the published cell's own key; here it is restated over `PubAt th`.
-/

namespace TermPubCons

open CoreLang CoreTerm TermRun TermSound TermStep TermOwnG0Defs
open WeakMem (AllocLabel)

theorem pubCons_iff {th : TTh} {C : Res} : PubCons th C ↔ ∀ l, PubAt th l → 1 ≤ C (.own l) := by
  constructor
  · intro h l hl
    obtain ⟨y, a, e, rt, ws, ad, h1, h2, h3, rfl⟩ := hl
    exact h y a e rt ws ad h1 h2 h3
  · intro h y a e rt ws ad h1 h2 h3
    exact h ad.label ⟨y, a, e, rt, ws, ad, h1, h2, h3, rfl⟩

theorem pubAt_consume {th : TTh} {C : Res} (h : PubCons th C) {l : AllocLabel} (hl : PubAt th l) :
    1 ≤ C (.own l) :=
  pubCons_iff.1 h l hl

end TermPubCons

#print axioms TermPubCons.pubCons_iff
#print axioms TermPubCons.pubAt_consume
