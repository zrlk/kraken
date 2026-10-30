/-
**The greatest closed invariant inside a fragment, and segments under a
larger allocation fragment** (AArch64; library copy for wake.w's levels):
the generic statements of `Spike/Test/A64Hello1Gfp.lean` (`closeS_mono`,
`GfpS`, `le_gfpS`, `segInvS_gfpS`, `gfpS_of_segWS`) and of
`Spike/Test/A64Hello1LevelsA.lean` (`segInvS_mono_xa`, `msOfA_with_xa`,
`msOfA_xa_mono`), verbatim, so that `Spike/Lib` modules may use them
without importing `Spike/Test`. The hello1 originals stay as they are.

- `closeS_mono`: a pair's closure moved along `inv ⊆ inv'`.
- `GfpS`: the pairs of some explicit-invariant segment inside `W`.
- `le_gfpS`: every explicit-invariant segment's pairs are `GfpS`'s.
- `segInvS_gfpS`: `GfpS` is an explicit-invariant segment.
- `gfpS_of_segWS`: the start of a segment with no exit is in `GfpS`.
- `segInvS_mono_xa`: a segment under a memory side with a larger allocation
  fragment.
- `msOfA_with_xa`, `msOfA_xa_mono`: `msOfA` at two fragments differs only in
  `xa`, monotone in the fragment.
-/
import Spike.Lib.A64SegInstA

namespace Spike.Lib.A64GfpS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Arena FragS OutS KOutS SegWS MemSide Pend)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA

/-! ## The greatest closed invariant -/

section Gfp

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

end Gfp

/-! ## Segments under a larger allocation fragment -/

/-- **A segment under a memory side with a larger allocation fragment**:
`ms'` is `ms` but for `xa`, which contains `ms`'s at every frame list. -/
theorem segInvS_mono_xa {p : Prog} {W inv : FragS isaLSE2} {K : State → State → Prop} {lbl : Lbl}
    {ms ms' : List TermRun.Frame → MemSide isaLSE2} (h : SegInvS W K p lbl ms inv)
    (he : ∀ fs, ms' fs = { ms fs with xa := (ms' fs).xa })
    (hxa : ∀ fs l b n s c, (ms fs).xa l b n s c → (ms' fs).xa l b n s c) : SegInvS W K p lbl ms' inv :=
  fun s c fs hi =>
    have h := h s c fs hi
    ⟨h.1, fun hk => OutS.mono_xa (h.2.1 hk) he hxa, h.2.2⟩

/-- `msOfA` at two fragments differs only in `xa`. -/
theorem msOfA_with_xa {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {ar : Arena} {I I' : InvS} {lbl : Lbl} {lsize : Lsize} (fs : List TermRun.Frame) :
    msOfA Λ μ rd G own ar I' lbl lsize fs = { msOfA Λ μ rd G own ar I lbl lsize fs with
      xa := (msOfA Λ μ rd G own ar I' lbl lsize fs).xa } := rfl

/-- `msOfA`'s `xa` is monotone in the fragment. -/
theorem msOfA_xa_mono {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {ar : Arena} {I I' : InvS} {lbl : Lbl} {lsize : Lsize}
    (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → I' lbl lsize s c fs) (fs : List TermRun.Frame)
    {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : (msOfA Λ μ rd G own ar I lbl lsize fs).xa l b n s c) :
    (msOfA Λ μ rd G own ar I' lbl lsize fs).xa l b n s c :=
  ⟨h.1, hI _ _ _ _ _ h.2⟩

end Spike.Lib.A64GfpS

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64GfpS.segInvS_gfpS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64GfpS.segInvS_gfpS

/-- info: 'Spike.Lib.A64GfpS.gfpS_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64GfpS.gfpS_of_segWS

/-- info: 'Spike.Lib.A64GfpS.segInvS_mono_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64GfpS.segInvS_mono_xa
