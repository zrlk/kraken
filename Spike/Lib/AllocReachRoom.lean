/-
**Room after every placed label at every reachable placement**
(`Reach.lblRoom`): a label placed at a placement reachable by allocations
(`AllocReach.Reach`) is placed at the start's placement or lands in the
arena (`Reach.placed`); with the arena inside the heap and the layout below
`2 ^ 32` (A1's `below32`), its base is at most `2 ^ 32`, so `2 ^ 31` bytes
after it stay below `2 ^ 64` (`LblRoom`, the lane store's no-wrap premise of
`laneC_of`, taken at each level's placement of the multi-level fragment
`IN`).

- `lblRoom_none`: no label placed (the load's placement);
- `Reach.lblRoom`: at every reachable placement.

ISA-free; `below32` from `placeOKAt` is
`Scc.Cert.PlaceOK.{A64,X64}.below32_of_placeOKAt`, the arena's inclusion
`Spike.Lib.{A64,X64}.Rt.arOf_sub`.
-/
import Spike.Lib.AllocReach
import Spike.Lib.Src.LblRoomOf

namespace Spike.Lib.AllocReach

open Scc.Sem
open Spike.Lib.LowerNode (LblRoom)

/-- **No label placed** has room after every placed label. -/
theorem lblRoom_none : LblRoom (fun _ => none) := fun _ _ h => by cases h

/-- **Room after every label placed at a reachable placement**, from room
at the start's placement, the arena inside the heap and the layout below
`2 ^ 32`. -/
theorem Reach.lblRoom {Λ : Layout} {ar : Arena} {L0 L : WeakMem.AllocLabel → Option Nat}
    {ls0 ls : WeakMem.AllocLabel → Nat} (h : Reach ar L0 ls0 L ls) (h0 : LblRoom L0)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32) : LblRoom L := fun l A hl => by
  rcases h.placed hl with ⟨h1, -⟩ | hland
  · exact h0 l A h1
  · have hh := Scc.Cert.PlaceOK.heap_end_le32 hb32
    obtain ⟨-, hb, -⟩ := hland
    simp only [Range.Sub] at hsub
    omega

/--
info: 'Spike.Lib.AllocReach.Reach.lblRoom' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Reach.lblRoom

end Spike.Lib.AllocReach
