/-
**A buffer allocation's heap abort on x64 discharges the heap disjunct**:
at the heap abort exit of `Spike/Lib/X64NewBuf.lean` (`nbX … .abort`), the
control is `HeapReady` at every count it allows (`Jfull.heapReady`,
`Jfull.heapAbortObl`, `Spike/Lib/X64HeapObl.lean`).

- `nbX_abort_heapReady`: as `Spike/Lib/A64HeapAbort.lean`'s.
- `nbX_abort_heapAbortObl`: as `Spike/Lib/A64HeapObl.lean`'s.
-/
import Spike.Lib.X64NewBuf
import Spike.Lib.X64HeapObl

namespace Spike.Lib.X64.Flow

namespace NewBuf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Alloc (Call Jfull)

/-- **The heap abort exit of a buffer allocation's call is `HeapReady`**:
`Jfull.heapReady` at a state of `nbX … .abort`, for every call's source
units (`hu`). -/
theorem nbX_abort_heapReady {ms : MemSide isa} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {R : Region} {fs : Int} {pcR : Int64} {Jc : AS → Ctl → Prop} {σ : AS} {c : Ctl}
    (hu : ∀ q : Call, q.OK ms lab → ∀ us, TermRun.accs (TermRun.close [] q.τ) = some us →
      ms.units q.n q.τ = q.n * TermRun.nWords us + 1 ∧ 1 ≤ TermRun.nWords us)
    (hJ : (nbX ms lab lbl R fs pcR Jc .abort).J σ c) {old : Nat}
    (hold : c.hold = none ∨ c.hold = some (ms.ctr, TermRun.cst (.num old))) (hle : old ≤ ms.cells) :
    HeapReady ms.cells old c := by
  obtain ⟨-, q, hf, -⟩ := hJ
  exact Jfull.heapReady q.2 (hu q.1 q.2) hf hold hle

/-- **The heap abort exit of a buffer allocation's call discharges the heap
disjunct** (`Jfull.heapAbortObl` at a state of `nbX … .abort`). -/
theorem nbX_abort_heapAbortObl {ms : MemSide isa} {lab : Label → Int64}
    {lbl : WeakMem.AllocLabel → Option Nat} {R : Region} {fs : Int} {pcR : Int64} {Jc : AS → Ctl → Prop}
    {σ : AS} {c : Ctl}
    (hu : ∀ q : Call, q.OK ms lab → ∀ us, TermRun.accs (TermRun.close [] q.τ) = some us →
      ms.units q.n q.τ = q.n * TermRun.nWords us + 1 ∧ 1 ≤ TermRun.nWords us)
    (hJ : (nbX ms lab lbl R fs pcR Jc .abort).J σ c) : HeapAbortObl ms.cells ms.ctr c := by
  obtain ⟨-, q, hf, -⟩ := hJ
  exact Jfull.heapAbortObl q.2 (hu q.1 q.2) hf

end NewBuf

end Spike.Lib.X64.Flow
