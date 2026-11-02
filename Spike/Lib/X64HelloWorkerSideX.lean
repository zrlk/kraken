/-
**hello.w's worker side on x86-64: the closed invariant inside a landing fact** (the twin of
`Spike/Lib/HelloWorkerSideX.lean`): from a frame-aware segment of the worker whose invariant and row landings lie
in a fragment `X` (`HelloSegTCSX.SegTCSX`), an invariant closed under `OutTS` at hello's source, inside
`NNH ∧ WideX`, `Z` up to a pending frame run, **and `X`**.

- `wi_existsHX`: the closed invariant, its fourth conjunct `X`.

## Differences from the AArch64 version

- Over x86-64's `NNH` (`Spike/Lib/X64HelloNN.lean`), `WideX`/`wideX_exec`/`wideX_kern`
  (`Spike/Lib/X64WideKeep.lean`) and source (`X64HelloSrc.helloSrc`); the proof is the original's.
- The original imports `HelloWorkerSide` for its dependencies only; that module (`wi_existsH`) is dead and has
  no x86-64 twin, so this one imports the pieces directly.
-/
import Spike.Lib.X64HelloNN
import Spike.Lib.X64WideKeep
import Spike.Lib.X64HelloSrc
import Spike.Lib.HelloSegTCSX

namespace Spike.Lib.X64HelloWorkerSideX

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.HelloSegThrS Spike.Lib.HelloSegTCS Spike.Lib.HelloSegTCSX
open Spike.Lib.X64.Flow.Worker (NNH)
open Spike.Lib.X64.WideKeep (WideX wideX_exec wideX_kern)
open Spike.Lib.X64HelloSrc (helloSrc)

variable {exe : _root_.Executable} {endPc : Int64}

/-- **The worker's closed invariant inside `NNH ∧ WideX` and `X`**, with `Z` up to a pending frame run, of its
segment to the empty fragment landing in `X`, from its entry's `P` pairs in `WideX exe`. -/
theorem wi_existsHX {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {P Z X : FragS isa} (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    (h : SegTCSX (fun s c fs => NNH exe endPc s ∧ Z s c fs) X helloSrc lbl ms P (fun _ _ _ => False)) :
    ∃ Wi : FragS isa, (∀ s c fs, P s c fs → WideX exe s → Wi s c fs) ∧
      (∀ s c fs, Wi s c fs → NNH exe endPc s ∧ WideX exe s ∧ Pend helloSrc Z s c fs ∧ X s c fs) ∧
      ∀ s c fs, Wi s c fs → OutTS helloSrc lbl ms Wi s c fs := by
  obtain ⟨Wi, hP, hS, ho⟩ := h.closed_conjSX (wideX_exec exe) fun fs => wideX_kern (hK fs) exe
  exact ⟨Wi, hP, fun s c fs hw =>
    ⟨Pend.state ((hS s c fs hw).1.mono fun _ _ _ h => h.1), (hS s c fs hw).2.1,
      (hS s c fs hw).1.mono fun _ _ _ h => h.2, (hS s c fs hw).2.2⟩, ho⟩

end Spike.Lib.X64HelloWorkerSideX

/-- info: 'Spike.Lib.X64HelloWorkerSideX.wi_existsHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerSideX.wi_existsHX
