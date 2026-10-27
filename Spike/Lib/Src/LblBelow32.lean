/-
**A placed label's base is below `2 ^ 32`** (ISA-neutral): every label the
placement places lies in the heap or `.data` (`LblRange`), and PlaceOK puts
`.rodata` and every region at or below `2 ^ 32` (`below32_of_placeOKAt`'s
statement, `hb32`). So `print`'s buffer bytes, a label's base plus a count
below `2 ^ 63`, do not wrap.

- `lbl_lt32`: the base of a placed label at most `2 ^ 32`.
-/
import Spike.Lib.Src.LblRange

namespace Spike.Lib.LowerNode

open Scc.Sem

/-- **A placed label's base is below `2 ^ 32`**: it lies in the heap or
`.data` (`LblRange`), both ending at or below `2 ^ 32` (`hb32`). -/
theorem lbl_lt32 {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    {l : WeakMem.AllocLabel} {b : Nat} (hl : lbl l = some b) : b ≤ 2 ^ 32 := by
  have hh := hb32 Λ.heap (by simp [Layout.regions])
  have hd := hb32 Λ.data (by simp [Layout.regions])
  rcases hrg l b hl with h | h
  · unfold Range.Sub lrange at h; simp only at h; omega
  · unfold Range.Sub lrange at h; simp only at h; omega

end Spike.Lib.LowerNode

/-- info: 'Spike.Lib.LowerNode.lbl_lt32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.lbl_lt32
