/-
**A buffer allocation's heap abort on AArch64 is `HeapReady`**: the
allocator's facts on the way to the heap abort (`Jfull`: the count past
`2 ^ 28`, or the counter's add past the cells) give the source facts of
`Spike/Lib/HeapAbort.lean` that justify the abort.

- `Jfull.heapReady`: from `Jfull`, for every `old` within the cells that
  the control's hold allows (any when it holds nothing, the held count
  otherwise), the control is `HeapReady` at `old`, given the source units
  of the call's element type (`hu`: `ms.units n τ = n · nWords us + 1`, one
  word or more per element).
- `nbX_abort_heapReady`: the same at the heap abort exit of
  `Spike/Lib/A64NewBuf.lean` (`nbX … .abort`).
-/
import Spike.Lib.A64NewBuf
import Spike.Lib.HeapAbort

namespace Spike.Lib.A64.Flow

namespace NewBuf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib
open Spike.Lib.A64.Alloc (Call Jfull)

/-- **The way to the heap abort is `HeapReady`**: a control of `Jfull` for
a call with its premises, at every `old` within the cells that its hold
allows (nothing held: the count past `2 ^ 28`; the counter's address held
with `old`), given the call's source units (`hu`). -/
theorem Jfull.heapReady {ms : MemSide isaLSE2} {lab : Label → Int64} {q : Call} {c : Ctl} (hq : q.OK ms lab)
    (hu : ∀ us, TermRun.accs (TermRun.close [] q.τ) = some us →
      ms.units q.n q.τ = q.n * TermRun.nWords us + 1 ∧ 1 ≤ TermRun.nWords us)
    (hJ : Jfull ms q c) {old : Nat}
    (hold : c.hold = none ∨ c.hold = some (ms.ctr, TermRun.cst (.num old))) (hle : old ≤ ms.cells) :
    HeapReady ms.cells old c := by
  obtain ⟨us, hus⟩ := hq.accs
  obtain ⟨hun, hw⟩ := hu us hus
  rcases hJ with ⟨rfl, hbig⟩ | ⟨o, rfl, -, ho⟩
  · refine ⟨q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, us, hq.term, hq.ev, hq.num, hus, hle, ?_⟩
    have := Nat.le_mul_of_pos_right q.n hw
    have := hq.cells
    omega
  · have hold' : old = o.toNat := by
      rcases hold with h | h
      · simp [Spike.Lib.A64.Flow.holdCtr] at h
      · simp only [Spike.Lib.A64.Flow.holdCtr, Option.some.injEq, Prod.mk.injEq, true_and] at h
        have := congrArg (·.val) h
        simp only [TermRun.cst, Promises.TVal.mk0] at this
        injection this with h'
        omega
    subst hold'
    refine ⟨q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, us, hq.term, hq.ev, hq.num, hus, hle, ?_⟩
    rw [← hun]; exact ho

/-- **The heap abort exit of a buffer allocation's call is `HeapReady`**:
`Jfull.heapReady` at a state of `nbX … .abort`, for every call's source
units (`hu`). -/
theorem nbX_abort_heapReady {ms : MemSide isaLSE2} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {R : Region} {fs : Int} {pcR : Int64} {Jc : AS → Ctl → Prop} {σ : AS} {c : Ctl}
    (hu : ∀ q : Call, q.OK ms lab → ∀ us, TermRun.accs (TermRun.close [] q.τ) = some us →
      ms.units q.n q.τ = q.n * TermRun.nWords us + 1 ∧ 1 ≤ TermRun.nWords us)
    (hJ : (nbX ms lab lbl R fs pcR Jc .abort).J σ c) {old : Nat}
    (hold : c.hold = none ∨ c.hold = some (ms.ctr, TermRun.cst (.num old))) (hle : old ≤ ms.cells) :
    HeapReady ms.cells old c := by
  obtain ⟨-, q, hf, -⟩ := hJ
  exact Jfull.heapReady q.2 (hu q.1 q.2) hf hold hle

end NewBuf

end Spike.Lib.A64.Flow
