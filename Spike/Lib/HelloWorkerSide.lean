/-
**hello.w's worker side: the closed invariant** (the
twin of `Spike/Lib/WakeWorkerSide.lean`'s `wi_exists`, AArch64): from a
frame-aware segment of the worker (`HelloSegTCS.SegTCS`) whose states are
`NNH` (off the transfer sites, system calls `WCompatH.sysOkH`'s) and whose
pairs satisfy `Z` (at a frame run's end), an invariant of thread states,
source controls and frames closed under `OutTS` at `helloSrc`, inside
`NNH ∧ WideX` and `Z` up to a pending frame run.

- `wi_existsH`: the interface to the per-record layer (`helloDR`:
  `Wi w := Classical.choose (wi_existsH …)`, `WSideH.closed` the third
  conjunct; the `WCompatH` fields `wide`, `noSite`, `sysExec`, `sysOkH`
  from the second).
-/
import Spike.Lib.A64HelloNN
import Spike.Lib.A64WideKeep
import Spike.Lib.HelloSrc

namespace Spike.Lib.HelloWorkerSide

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.HelloSegThrS Spike.Lib.HelloSegTCS
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.WideKeep (WideX wideX_exec wideX_kern)
open Spike.Lib.HelloSrc (helloSrc)

variable {exe : _root_.Executable} {endPc : Int64}

/-- **The worker's closed invariant inside `NNH ∧ WideX`**, with `Z` up to
a pending frame run, of its frame-aware segment to the empty fragment, from
its entry's `P` pairs in `WideX exe` (under the kernel model `hK` at every
stack of frames). -/
theorem wi_existsH {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {P Z : FragS isaLSE2} (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi)
    (h : SegTCS (fun s c fs => NNH exe endPc s ∧ Z s c fs) helloSrc lbl ms P (fun _ _ _ => False)) :
    ∃ Wi : FragS isaLSE2, (∀ s c fs, P s c fs → WideX exe s → Wi s c fs) ∧
      (∀ s c fs, Wi s c fs → NNH exe endPc s ∧ WideX exe s ∧ Pend helloSrc Z s c fs) ∧
      ∀ s c fs, Wi s c fs → OutTS helloSrc lbl ms Wi s c fs := by
  obtain ⟨Wi, hP, hS, ho⟩ := h.closed_conjS (wideX_exec exe) fun fs => wideX_kern (hK fs) exe
  exact ⟨Wi, hP, fun s c fs hw =>
    ⟨Pend.state ((hS s c fs hw).1.mono fun _ _ _ h => h.1), (hS s c fs hw).2,
      (hS s c fs hw).1.mono fun _ _ _ h => h.2⟩, ho⟩

end Spike.Lib.HelloWorkerSide
