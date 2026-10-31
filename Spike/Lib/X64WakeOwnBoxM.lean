/-
**Main's TCB word off the box cell and the second TCB's tid word**
(x86-64; X64-boxM / X64-htM): the carried premises
`hboxM` of `OwnWc.wcSp0W_wcGX` (`Spike/Lib/X64WakeOwnWcPreX.lean`) and
`htM` of `OwnSp4.wcSp4W_wcGX` / `OwnMid.wcMidW_wcGX`
(`Spike/Lib/X64WakeOwnWcSp4X.lean`, `Spike/Lib/X64WakeOwnWcMidX.lean`),
discharged from the layout.

`tcbM = pinA + 8` is the TCB's field `0`, a runtime word (`fld_mem`), so its
first byte lies in `data` or `pinned` (`words_mapped`); in a well-formed
layout both are disjoint from the heap. A box cell the allocator may return
lies in the heap: the memory side's cells in `Λ.heap` (`hH`, `hHi`, `hroom`,
as `StartGlue.hcellB_of_wordsNone`) and the box's word inside its block
(`hoB`). The tid word `t2 + 56 = pinA + 160` is `152` bytes past `tcbM`.

- `tcbM_byte`: `tcbM`'s first byte in `data` or `pinned`.
- `ne_tcbM_of_heap`: a heap address is not `tcbM`.
- `box_heap`: a box cell lies in the heap.
- `hboxM_of`: `hboxM` from the heap facts.
- `tid_ne_tcbM`: `htM` at `t = t2`.

**Deviations.** None: new lemmas. The producers keep `hboxM` and `htM` as
premises (their statements unchanged); the assembly supplies them with
`hboxM_of` (from `MainGlue`'s `hH`, `hHi`, `hroom`, `hoB`) and
`tid_ne_tcbM`.
-/
import Spike.Lib.X64WakeOwnWcMidX
import Spike.Lib.X64WakeOwnWSep

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.WakeWc (AGB t2)

variable {L : RuntimeLayout}

/-- **`tcbM`'s first byte is in `data` or `pinned`**: `tcbM` is the TCB's
field `0`, a runtime word. -/
theorem tcbM_byte (L : RuntimeLayout) :
    L.Λ.data.contains (tcbM L).toNat ∨ L.Λ.pinned.contains (tcbM L).toNat := by
  have h := (L.words_mapped _ (L.fld_mem (i := 0) (by decide))).2.2 0 (by decide)
  simpa using h

/-- **A heap address is not `tcbM`** in a well-formed layout. -/
theorem ne_tcbM_of_heap (hwf : L.Λ.WF) {c : Nat} (hc64 : c < 2 ^ 64) (hc : L.Λ.heap.contains c) :
    BitVec.ofNat 64 c ≠ tcbM L := by
  intro he
  have hcW : c = (tcbM L).toNat := by rw [← he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc64]
  have h0 := tcbM_byte L
  rw [← hcW] at h0
  obtain ⟨-, -, -, hdh, -, -, -, -, hhp, -⟩ := hwf.disjoint
  simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hc hdh hhp h0
  omega

/-- **A box cell lies in the heap**: the memory side's cells in `Λ.heap`,
the box's word inside its block. -/
theorem box_heap {ms : Spike.Lib.MemSide isa} {lab : Label → Int64}
    (hH : L.Λ.heap.lo ≤ ms.heap) (hHi : ms.heap + 16 * ms.cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    (hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64) {q : AGB ms lab}
    (hoB : ms.off 1 q.1.τ + 16 ≤ 16 * ms.units 1 q.1.τ) {o : Nat} (ho : o + ms.units 1 q.1.τ ≤ ms.cells) :
    ms.heap + 16 * o + ms.off 1 q.1.τ < 2 ^ 64 ∧ L.Λ.heap.contains (ms.heap + 16 * o + ms.off 1 q.1.τ) := by
  simp only [Scc.Sem.Range.contains]
  omega

/-- **`hboxM` from the heap facts** (`wcSp0W_wcGX`'s form, at any guard
`P` on the allocations): every cell the allocator may return is off
`tcbM`. -/
theorem hboxM_of (hwf : L.Λ.WF) {ms : Spike.Lib.MemSide isa} {lab : Label → Int64}
    (hH : L.Λ.heap.lo ≤ ms.heap) (hHi : ms.heap + 16 * ms.cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    (hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64) {P : AGB ms lab → Prop}
    (hoB : ∀ q : AGB ms lab, P q → ms.off 1 q.1.τ + 16 ≤ 16 * ms.units 1 q.1.τ) :
    ∀ (q : AGB ms lab) (o : Nat), P q → ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ) ≠ tcbM L := fun q _ hP _ ho =>
  have h := box_heap hH hHi hroom (hoB q hP) ho
  ne_tcbM_of_heap hwf h.1 h.2

/-- **The second TCB's tid word is not `tcbM`**: `t2 + 56 = pinA + 160`,
`tcbM = pinA + 8`. -/
theorem tid_ne_tcbM (L : RuntimeLayout) : t2 L.lab + 56#64 ≠ tcbM L := by
  show Spike.Lib.X64.Flow.Ret0.pinA L.lab + 104#64 + 56#64 ≠ L.pinA + 8#64
  rw [L.lab_pin]
  bv_omega

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.ne_tcbM_of_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ne_tcbM_of_heap

/-- info: 'Spike.Lib.X64.WakePh.hboxM_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.hboxM_of

/-- info: 'Spike.Lib.X64.WakePh.tid_ne_tcbM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tid_ne_tcbM
