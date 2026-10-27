/-
**The greatest closed invariant inside a fragment** (AArch64): the union of
every explicit-invariant segment (`SegInvS`, `Spike/Lib/A64SegInstA.lean`)
inside `W`, itself one (`GfpS`). The levels' `inv0`
(`Spike/Test/A64Hello1LevelsA.lean`) is it, so every closed invariant inside
`W0` (a segment from any pair, not only from the level's start) lies in it.

- `closeS_mono`: a pair's closure (`SegInvS`'s rows and outside moves into
  `inv`) moved along `inv ⊆ inv'` (`OutS.mono`, `Pend.mono`, `KOutS.mono`).
- `GfpS`: the pairs of some explicit-invariant segment inside `W`.
- `le_gfpS`: every explicit-invariant segment's pairs are `GfpS`'s.
- `segInvS_gfpS`: `GfpS` is an explicit-invariant segment.
- `gfpS_of_segWS`: the start of a segment with no exit is in `GfpS`.
-/
import Spike.Lib.A64SegInstA

namespace Spike.Test.A64Hello1Gfp

open CoreTerm
open Kraken.Promising.AArch64
open Spike.Lib (FragS OutS KOutS SegWS MemSide Pend)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerA (SegInvS SegInvS.ofSegWS)

variable {p : Prog} {W : FragS isaLSE2} {K : State → State → Prop} {lbl : Lbl}
  {ms : List TermRun.Frame → MemSide isaLSE2}

/-- **A pair's closure moved along `inv ⊆ inv'`**: its rows off `K` into
`Pend p inv` and its outside moves into `inv` give the same into `inv'`. -/
theorem closeS_mono {inv inv' : FragS isaLSE2} (hI : ∀ s c fs, inv s c fs → inv' s c fs) {s : State}
    {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : ((∀ s', ¬ K s s') → OutS p lbl ms (Pend p inv) s c fs) ∧ KOutS K p inv s c fs) :
    ((∀ s', ¬ K s s') → OutS p lbl ms (Pend p inv') s c fs) ∧ KOutS K p inv' s c fs :=
  ⟨fun hk => (h.1 hk).mono fun _ _ _ hp => hp.mono hI, h.2.mono hI⟩

/-- **The greatest closed invariant inside `W`**: the pairs of some
explicit-invariant segment inside `W`. -/
def GfpS (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : Lbl)
    (ms : List TermRun.Frame → MemSide isaLSE2) : FragS isaLSE2 :=
  fun s c fs => ∃ inv, SegInvS W K p lbl ms inv ∧ inv s c fs

/-- Every explicit-invariant segment's pairs are `GfpS`'s. -/
theorem le_gfpS {inv : FragS isaLSE2} (h : SegInvS W K p lbl ms inv) :
    ∀ s c fs, inv s c fs → GfpS W K p lbl ms s c fs :=
  fun _ _ _ hi => ⟨inv, h, hi⟩

/-- **`GfpS` is an explicit-invariant segment**: a pair of one inside `W`
is in `W`, and its closure into that one is a closure into `GfpS`
(`closeS_mono`). -/
theorem segInvS_gfpS : SegInvS W K p lbl ms (GfpS W K p lbl ms) := by
  rintro s c fs ⟨inv, h, hi⟩
  obtain ⟨hw, hcl⟩ := h s c fs hi
  exact ⟨hw, closeS_mono (le_gfpS h) hcl⟩

/-- **The start of a segment with no exit is in `GfpS`** (its witness,
`SegInvS.ofSegWS`). -/
theorem gfpS_of_segWS {P : FragS isaLSE2} (h : SegWS W K p lbl ms P (fun _ _ _ => False)) :
    ∀ s c fs, P s c fs → GfpS W K p lbl ms s c fs := by
  obtain ⟨inv, hP, hS⟩ := SegInvS.ofSegWS h
  exact fun s c fs hp => le_gfpS hS s c fs (hP s c fs hp)

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.A64Hello1Gfp.segInvS_gfpS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms segInvS_gfpS

/--
info: 'Spike.Test.A64Hello1Gfp.gfpS_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms gfpS_of_segWS

end Spike.Test.A64Hello1Gfp
