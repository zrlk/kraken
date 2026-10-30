/-
**Room after every placed label, from the layout bound** (`lblRoom_of_memRel`):
A1's `below32` (`.rodata` and every region end at or below `2 ^ 32`) puts
every label the memory relation places inside the heap or `.data`
(`MemRel.lbl_range`), so its base is at most `2 ^ 32` and `2 ^ 31` bytes after
it stay below `2 ^ 64` (`LblRoom`, the lane store's no-wrap premise).

- `lblRoom_of_range`: from every placed label's range inside the heap or
  `.data`;
- `lblRoom_of_memRel`: from the memory relation.

ISA-free; `below32` from `placeOKAt` is `Scc.Cert.PlaceOK.{A64,X64}.below32_of_placeOKAt`.
-/
import Spike.Lib.Src.XchgB
import Spike.Lib.ArenaBound

namespace Spike.Lib.LowerNode

open Scc.Sem

variable {Λ : Layout}

/-- **`LblRoom` from every placed label's range inside the heap or
`.data`, or (a zero-word `ThreadId` box) the pinned region**, the layout
below `2 ^ 32`. -/
theorem lblRoom_of_range (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    (hr : ∀ l b, lbl l = some b → (lrange lsize l b).Sub Λ.heap ∨ (lrange lsize l b).Sub Λ.data ∨
      (lsize l = 0 ∧ (lrange lsize l b).Sub Λ.pinned)) :
    LblRoom lbl := fun l A hl => by
  have := Scc.Cert.PlaceOK.lbl_end_le32 hb32 (hr l A hl)
  omega

/-- **`LblRoom` from the memory relation**, the layout below `2 ^ 32`. -/
theorem lblRoom_of_memRel (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {tm : Kraken.Promising.Memory} {sm : WeakMem.Memory} {pairs : List Nat}
    (h : MemRel Λ lbl lsize ts tm sm pairs) : LblRoom lbl :=
  lblRoom_of_range hb32 fun l b hl => (h.lbl_range l b hl).2

/--
info: 'Spike.Lib.LowerNode.lblRoom_of_memRel' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms lblRoom_of_memRel

end Spike.Lib.LowerNode
