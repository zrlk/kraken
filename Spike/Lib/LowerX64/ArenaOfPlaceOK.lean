/-
**The heap arena below `2 ^ 64` from `PlaceOK`** (x86-64): the layout bound
of A1 (`below32_of_placeOKAt`) through `Spike/Lib/ArenaBound.lean`: a buffer
ending in the heap arena, or at most a placed label's bytes from its base, does
not wrap (`hov` of `print_call_segWB`).
-/
import Scc.Cert.PlaceOKX64
import Spike.Lib.ArenaBound

namespace Scc.Cert.PlaceOK.X64

open Scc.Sem

variable {cfg : Config} {Λ : Scc.Sem.Layout} {o : Out}

/-- **The heap arena lies below `2 ^ 64`** on an output passing
`placeOKAt`. -/
theorem heap_end_lt_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.heap.lo + Λ.heap.size < 2 ^ 64 :=
  heap_end_lt (below32_of_placeOKAt h)

/-- **A buffer ending in the heap arena does not wrap** on an output passing
`placeOKAt`. -/
theorem heap_hov_of_placeOKAt (h : placeOKAt cfg Λ o = true) {a nb : Nat}
    (ha : a + nb ≤ Λ.heap.lo + Λ.heap.size) : a + nb < 2 ^ 64 :=
  heap_hov (below32_of_placeOKAt h) ha

/-- **The allocator's arena lies below `2 ^ 64`**: its `allocCells`
16-byte cells from the heap arena's base (A8's `heapSize_of_placeOKAt`). -/
theorem arena_end_lt_of_placeOKAt (h : placeOKAt cfg Λ o = true) : Λ.heap.lo + 16 * allocCells < 2 ^ 64 :=
  heap_hov_of_placeOKAt h (by have := heapSize_of_placeOKAt h; omega)

/-- **`hov` for a placed label** on an output passing `placeOKAt`: at most
`8 * lsize l` bytes from the base of a label placed by the memory relation do
not wrap. -/
theorem memRel_hov_of_placeOKAt (h : placeOKAt cfg Λ o = true)
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {tm : Kraken.Promising.Memory} {sm : WeakMem.Memory} {pairs : List Nat}
    (hM : MemRel Λ lbl lsize ts tm sm pairs) {l : WeakMem.AllocLabel} {b nb : Nat}
    (hl : lbl l = some b) (hn : nb ≤ 8 * lsize l) : b + nb < 2 ^ 64 :=
  memRel_hov (below32_of_placeOKAt h) hM hl hn

end Scc.Cert.PlaceOK.X64
