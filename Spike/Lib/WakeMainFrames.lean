/-
**wake.w on AArch64: main's frame family past the clone**: the ghost frame family `Rg`, `Fg`, `fp` over `γ` that
`A64WakeMainClosedWS.main_closed_ws` (`WakeSpawnR.MainWS`) asks for.

The family only moves at calls that return to a different frame; in
`main_closed_ws` the wait loop's park returns to the same ghost
(`WaitLoop.seg_waitLoopP` discharges `seg_waitLoop`'s `hpark` with `⟨g, h⟩`)
and the exit keeps it, so one frame suffices: `γ := Unit`, the region the
clone's `⟨base, -96, 16⟩`, the frame condition `DFrame` of it from main's
memory `m0` after the clone, the frame pointer `x29`. `frames_unit` gives
all of the family's fields from the region's `OK` and alignment and the
flag's word `A` off the region and unmapped in `m0`'s private memory.
-/
import Spike.Lib.WakeSpawnR

namespace Spike.Lib.WakeMainFrames

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow

/-- **The one-frame family** (see the module doc): with `Rg`, `Fg`, `fp`
constant at the region `⟨b, -96, 16⟩`, `DFrame` of it from `m0` and `x29`,
the fields `hRg`, `hfp`, `hFg`, `hF`, `hRo`, `hal`, `hlo`, `hhi`, `hdm` of
`MainWS`. -/
theorem frames_unit {b : BitVec 64} {m0 : MachineData} {x29 A : BitVec 64}
    (hR : (⟨b, -96, 16⟩ : Region).OK) (hal : b.toNat % 16 = 0)
    (hA0 : Mem.loadInt m0.dmem A 8 = none) (hA8 : A.toNat + 8 ≤ 2 ^ 64)
    (hAoff : (A.toNat : Int) + 8 ≤ b.toNat + -96 ∨ (b.toNat : Int) + 16 ≤ A.toNat) :
    let Rg : Unit → Region := fun _ => ⟨b, -96, 16⟩
    let Fg : Unit → MachineData → Prop := fun _ => DFrame ⟨b, -96, 16⟩ m0
    let fp : Unit → BitVec 64 := fun _ => x29
    Rg () = ⟨b, -96, 16⟩ ∧ fp () = x29 ∧ (∀ m, DFrame ⟨b, -96, 16⟩ m0 m → Fg () m) ∧
      (∀ g, FStable (Rg g) (Fg g)) ∧ (∀ g, (Rg g).OK) ∧ (∀ g, (Rg g).base.toNat % 16 = 0) ∧
      (∀ g, (Rg g).lo ≤ -96) ∧ (∀ g, 16 ≤ (Rg g).hi) ∧ (∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none) :=
  ⟨rfl, rfl, fun _ h => h, fun _ => FStable.dframe _ m0, fun _ => hR, fun _ => hal, fun _ => Int.le_refl _,
    fun _ => Int.le_refl _, fun _ _ hm => (hm A hA8 hAoff).trans hA0⟩

/-- info: 'Spike.Lib.WakeMainFrames.frames_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frames_unit

end Spike.Lib.WakeMainFrames
