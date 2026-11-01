/-
**hello.w's worker side: the closed invariant inside a landing fact** (row 5j-wit-W; the `SegTCSX` twin of
`Spike/Lib/HelloWorkerSide.lean`'s `wi_existsH`): from a frame-aware segment of the worker whose invariant and
row landings lie in a fragment `X` (`HelloSegTCSX.SegTCSX`), an invariant closed under `OutTS` at `helloSrc`,
inside `NNH ∧ WideX`, `Z` up to a pending frame run, **and `X`**. At `X := PlacedSE …` the invariant places
every frame (`HelloPostWit.post_wit_hello`'s `hplW` by projection).

- `wi_existsHX`: `wi_existsH` with the fourth conjunct `X`.
-/
import Spike.Lib.HelloWorkerSide
import Spike.Lib.HelloSegTCSX

namespace Spike.Lib.HelloWorkerSideX

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.HelloSegThrS Spike.Lib.HelloSegTCS Spike.Lib.HelloSegTCSX
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.WideKeep (WideX wideX_exec wideX_kern)
open Spike.Lib.HelloSrc (helloSrc)

variable {exe : _root_.Executable} {endPc : Int64}

/-- **The worker's closed invariant inside `NNH ∧ WideX` and `X`**, with `Z` up to a pending frame run, of its
segment to the empty fragment landing in `X`, from its entry's `P` pairs in `WideX exe`. -/
theorem wi_existsHX {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {P Z X : FragS isaLSE2} (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    (h : SegTCSX (fun s c fs => NNH exe endPc s ∧ Z s c fs) X helloSrc lbl ms P (fun _ _ _ => False)) :
    ∃ Wi : FragS isaLSE2, (∀ s c fs, P s c fs → WideX exe s → Wi s c fs) ∧
      (∀ s c fs, Wi s c fs → NNH exe endPc s ∧ WideX exe s ∧ Pend helloSrc Z s c fs ∧ X s c fs) ∧
      ∀ s c fs, Wi s c fs → OutTS helloSrc lbl ms Wi s c fs := by
  obtain ⟨Wi, hP, hS, ho⟩ := h.closed_conjSX (wideX_exec exe) fun fs => wideX_kern (hK fs) exe
  exact ⟨Wi, hP, fun s c fs hw =>
    ⟨Pend.state ((hS s c fs hw).1.mono fun _ _ _ h => h.1), (hS s c fs hw).2.1,
      (hS s c fs hw).1.mono fun _ _ _ h => h.2, (hS s c fs hw).2.2⟩, ho⟩

end Spike.Lib.HelloWorkerSideX

/-- info: 'Spike.Lib.HelloWorkerSideX.wi_existsHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerSideX.wi_existsHX
