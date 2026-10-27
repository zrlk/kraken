/-
**The allocator's heap obligations on AArch64**: the way to the heap abort
discharges the abort site's heap disjunct (`HeapAbortObl`,
`Spike/Lib/HeapObl.lean`), and the counter's add keeps the relation's heap
clause (`HeapCtr`).

- `Jfull.heapAbortObl`: at a control of `Jfull` (`Jfull.heapReady`; the
  control is at the call's `newBuf`, its hold none or the counter's).
- `nbX_abort_heapAbortObl`: at the heap abort exit of a buffer allocation's
  call (`nbX … .abort`, `Spike/Lib/A64NewBuf.lean`).
- `heapCtr_holdCtr`: holding the old count `hu` keeps `HeapCtr` at `hu`.
-/
import Spike.Lib.A64HeapAbort
import Spike.Lib.HeapObl

namespace Spike.Lib.A64.Flow

namespace NewBuf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib
open Spike.Lib.A64.Alloc (Call Jfull)

/-- **`Jfull` discharges the heap disjunct**: at a control of `Jfull` for a
call with its premises (and the call's source units, `hu`), every `old`
the control allows is `HeapReady`. -/
theorem Jfull.heapAbortObl {ms : MemSide isaLSE2} {lab : Label → Int64} {q : Call} {c : Ctl}
    (hq : q.OK ms lab)
    (hu : ∀ us, TermRun.accs (TermRun.close [] q.τ) = some us →
      ms.units q.n q.τ = q.n * TermRun.nWords us + 1 ∧ 1 ≤ TermRun.nWords us)
    (hJ : Jfull ms q c) : HeapAbortObl ms.cells ms.ctr c := by
  intro old h
  have hnb : AtNewBuf c := by
    rcases hJ with ⟨rfl, -⟩ | ⟨o, rfl, -⟩
    · exact ⟨_, _, _, _, hq.term⟩
    · exact ⟨_, _, _, _, hq.term⟩
  obtain ⟨hle, hw⟩ := h hnb
  refine Jfull.heapReady hq hu hJ ?_ hle
  rcases hJ with ⟨rfl, -⟩ | ⟨o, rfl, -⟩
  · exact .inl hq.hold
  · refine .inr ?_
    have e := hw _ rfl
    simp only [holdCtr] at e ⊢
    rw [e]

/-- **The heap abort exit of a buffer allocation's call discharges the heap
disjunct** (`Jfull.heapAbortObl` at a state of `nbX … .abort`). -/
theorem nbX_abort_heapAbortObl {ms : MemSide isaLSE2} {lab : Label → Int64}
    {lbl : WeakMem.AllocLabel → Option Nat} {R : Region} {fs : Int} {pcR : Int64} {Jc : AS → Ctl → Prop}
    {σ : AS} {c : Ctl}
    (hu : ∀ q : Call, q.OK ms lab → ∀ us, TermRun.accs (TermRun.close [] q.τ) = some us →
      ms.units q.n q.τ = q.n * TermRun.nWords us + 1 ∧ 1 ≤ TermRun.nWords us)
    (hJ : (nbX ms lab lbl R fs pcR Jc .abort).J σ c) : HeapAbortObl ms.cells ms.ctr c := by
  obtain ⟨-, q, hf, -⟩ := hJ
  exact Jfull.heapAbortObl q.2 (hu q.1 q.2) hf

/-- **The counter's add keeps the heap clause** at the same heap use: the
control holding the old count `hu`. -/
theorem heapCtr_holdCtr {I : ISA} {ms : MemSide I} {c : Ctl} {hu : Nat} (hle : hu ≤ ms.cells) (o : BitVec 64)
    (ho : o.toNat = hu) : HeapCtr ms.cells ms.ctr hu (holdCtr ms c o) := by
  intro _
  refine ⟨hle, fun w hw => ?_⟩
  simp only [holdCtr, Option.some.injEq, Prod.mk.injEq, true_and] at hw
  rw [← hw, ho]

end NewBuf

end Spike.Lib.A64.Flow
