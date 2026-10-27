/-
**The allocator's heap obligations on x64**, the twin of
`Spike/Lib/A64HeapAbort.lean` and `Spike/Lib/A64HeapObl.lean` over the x64
allocator (`Spike/Lib/X64Alloc.lean`): the way to the heap abort is
`HeapReady` and discharges the abort site's heap disjunct
(`HeapAbortObl`, `Spike/Lib/HeapObl.lean`), and the counter's add keeps the
relation's heap clause (`HeapCtr`).

- `Jfull.heapReady`: from `Jfull`, for every `old` within the cells that
  the control's hold allows, the control is `HeapReady` at `old`, given the
  call's source units (`hu`).
- `Jfull.heapAbortObl`: the same as the heap disjunct.
- `heapCtr_holdCtr`: holding the old count `hu` keeps `HeapCtr` at `hu`.
-/
import Spike.Lib.X64Alloc
import Spike.Lib.HeapObl

namespace Spike.Lib.X64.Flow

namespace NewBuf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Alloc (Call Jfull)

/-- **The way to the heap abort is `HeapReady`**: a control of `Jfull` for
a call with its premises, at every `old` within the cells that its hold
allows (nothing held: the count past `2 ^ 28`; the counter's address held
with `old`), given the call's source units (`hu`). -/
theorem Jfull.heapReady {ms : MemSide isa} {lab : Label → Int64} {q : Call} {c : Ctl} (hq : q.OK ms lab)
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
      · simp [holdCtr] at h
      · simp only [holdCtr, Option.some.injEq, Prod.mk.injEq, true_and] at h
        have := congrArg (·.val) h
        simp only [TermRun.cst, Promises.TVal.mk0] at this
        injection this with h'
        omega
    subst hold'
    refine ⟨q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, us, hq.term, hq.ev, hq.num, hus, hle, ?_⟩
    rw [← hun]; exact ho

/-- **`Jfull` discharges the heap disjunct**: at a control of `Jfull` for a
call with its premises (and the call's source units, `hu`), every `old`
the control allows is `HeapReady`. -/
theorem Jfull.heapAbortObl {ms : MemSide isa} {lab : Label → Int64} {q : Call} {c : Ctl}
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

/-- **The counter's add keeps the heap clause** at the same heap use: the
control holding the old count `hu`. -/
theorem heapCtr_holdCtr {I : ISA} {ms : MemSide I} {c : Ctl} {hu : Nat} (hle : hu ≤ ms.cells) (o : BitVec 64)
    (ho : o.toNat = hu) : HeapCtr ms.cells ms.ctr hu (holdCtr ms c o) := by
  intro _
  refine ⟨hle, fun w hw => ?_⟩
  simp only [holdCtr, Option.some.injEq, Prod.mk.injEq, true_and] at hw
  rw [← hw, ho]

end NewBuf

end Spike.Lib.X64.Flow
