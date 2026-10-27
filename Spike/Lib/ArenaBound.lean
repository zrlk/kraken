/-
**The heap arena and `.data` below `2 ^ 64`, from the layout bound**: A1's
`below32` (`.rodata` and every region end at or below `2 ^ 32`) puts every
byte of a placed label, and every byte of the heap arena or `.data`, strictly
below `2 ^ 64`, so a buffer of `nb` bytes at a placed label's base does not
wrap (`hov` of `print_call_segWB`).

- `lbl_end_le32`, `lbl_hov`: a label range inside the heap or `.data`;
- `memRel_hov`: a label placed by the memory relation (`MemRel.lbl_range`);
- `heap_hov`, `data_hov`: an address range ending inside the region (the
  cell form `Λ.heap.lo + 16 * cells`).

ISA-free; the per-ISA wrappers from `placeOKAt` are in
`Spike/Lib/Lower{A64,X64}/ArenaOfPlaceOK.lean`.
-/
import Scc.Sem.MemRel

namespace Scc.Cert.PlaceOK

open Scc.Sem

variable {Λ : Layout}

/-- The heap arena ends at or below `2 ^ 32`. -/
theorem heap_end_le32 (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) :
    Λ.heap.lo + Λ.heap.size ≤ 2 ^ 32 :=
  hb32 _ (by simp [Layout.regions])

/-- `.data` ends at or below `2 ^ 32`. -/
theorem data_end_le32 (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) :
    Λ.data.lo + Λ.data.size ≤ 2 ^ 32 :=
  hb32 _ (by simp [Layout.regions])

/-- **The heap arena lies below `2 ^ 64`** (the arena's end, for an arena
`heap + 16 * cells` inside `Λ.heap`). -/
theorem heap_end_lt (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) :
    Λ.heap.lo + Λ.heap.size < 2 ^ 64 := by
  have := heap_end_le32 hb32; omega

/-- **A buffer ending in the heap arena does not wrap.** -/
theorem heap_hov (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) {a nb : Nat}
    (ha : a + nb ≤ Λ.heap.lo + Λ.heap.size) : a + nb < 2 ^ 64 := by
  have := heap_end_le32 hb32; omega

/-- **A buffer ending in `.data` does not wrap.** -/
theorem data_hov (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) {a nb : Nat}
    (ha : a + nb ≤ Λ.data.lo + Λ.data.size) : a + nb < 2 ^ 64 := by
  have := data_end_le32 hb32; omega

/-- **A label's range inside the heap or `.data` ends at or below
`2 ^ 32`.** -/
theorem lbl_end_le32 (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    {lsize : WeakMem.AllocLabel → Nat} {l : WeakMem.AllocLabel} {b : Nat}
    (hr : (lrange lsize l b).Sub Λ.heap ∨ (lrange lsize l b).Sub Λ.data) : b + 8 * lsize l ≤ 2 ^ 32 := by
  have hh := heap_end_le32 hb32
  have hd := data_end_le32 hb32
  rcases hr with hs | hs <;> simp only [lrange, Range.Sub] at hs <;> omega

/-- **At most a label's bytes from its base do not wrap.** -/
theorem lbl_hov (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    {lsize : WeakMem.AllocLabel → Nat} {l : WeakMem.AllocLabel} {b nb : Nat}
    (hr : (lrange lsize l b).Sub Λ.heap ∨ (lrange lsize l b).Sub Λ.data) (hn : nb ≤ 8 * lsize l) :
    b + nb < 2 ^ 64 := by
  have := lbl_end_le32 hb32 hr; omega

/-- **`hov` for a label placed by the memory relation**: at most `8 * lsize
l` bytes from the base `b` of a placed label `l` do not wrap. -/
theorem memRel_hov (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {tm : Kraken.Promising.Memory} {sm : WeakMem.Memory} {pairs : List Nat}
    (h : MemRel Λ lbl lsize ts tm sm pairs) {l : WeakMem.AllocLabel} {b nb : Nat}
    (hl : lbl l = some b) (hn : nb ≤ 8 * lsize l) : b + nb < 2 ^ 64 :=
  lbl_hov hb32 (h.lbl_range l b hl).2 hn

end Scc.Cert.PlaceOK
