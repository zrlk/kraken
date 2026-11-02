/-
**hello.w's `wc_main` frames on the pool from the box's facts** (x86-64 only; the hello counterpart of
`X64WakeH1GOf.band_of_box`): `BoxPureH`'s region (`R.lo ≤ -384`, `16 ≤ R.hi`, its base 96 below stack 0's top)
puts every frame address `R.addr k`, `-384 ≤ k ≤ 8`, inside the stack pool (the stacks inside it,
`RuntimeLayout.stacks_sub`). This is the band premise `hb` of the `ownGHXW` producers, at the depth each asks
(wake's `OwnMid.bandOnP_mono`).

- `band_of_boxH`: `BandOnP L R (-384) 8` from `BoxPureH`.
- `band144_of_boxH`, `band304_of_boxH`, `band320_of_boxH`: the bands of `OwnSp4`/`Wcl2X` (`-144`), `WcWfSX`
  (`-304`) and `OwnMid` (`-320`).

## Differences from the AArch64 version

AArch64 has no counterpart: its producers need no band (main owns no TCB word there). Against x86-64 wake's
`band_of_box`: hello's region is `BoxPureH`'s (base `stacksA + 16384 - 96`, depth `384`; wake `- 64`, `320`), so
the band is `[-384, 8]` (wake `[-256, 8]`).
-/
import Spike.Lib.X64HelloHMid
import Spike.Lib.X64WakeOwnWcMidX

namespace Spike.Lib.X64.HelloPh.OwnBand

open Spike.Lib (Region)
open Spike.Lib.X64.WakePh (BandOnP)
open Spike.Lib.X64.WakePh.OwnMid (bandOnP_mono)
open Spike.Lib.X64HelloHMid (BoxPureH)

variable {L : Spike.Lib.X64.Rt.RuntimeLayout} {F0 : MachineData → Prop} {n : Nat} {R : Region}
  {F : MachineData → Prop} {J1 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {t : UInt64}

/-- **Every frame of `wc_main` on the pool**: `R.addr k`, `-384 ≤ k ≤ 8`, lies in the first stack. -/
theorem band_of_boxH (hB : BoxPureH L F0 n R F J1 t) : BandOnP L R (-384) 8 := by
  obtain ⟨hR, -, -, hRlo, hhi, hbase, -⟩ := hB
  intro k h1 h2
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  simp only at hs1 hs2
  have e := Region.addr_toNat_of hR (k := k) (by omega) (by omega)
  omega

/-- `band_of_boxH` at `OwnSp4`'s and `Wcl2X`'s depth. -/
theorem band144_of_boxH (hB : BoxPureH L F0 n R F J1 t) : BandOnP L R (-144) 8 :=
  bandOnP_mono (band_of_boxH hB) (by decide) (Int.le_refl _)

/-- `band_of_boxH` at `WcWfSX`'s depth. -/
theorem band304_of_boxH (hB : BoxPureH L F0 n R F J1 t) : BandOnP L R (-304) 8 :=
  bandOnP_mono (band_of_boxH hB) (by decide) (Int.le_refl _)

/-- `band_of_boxH` at `OwnMid`'s depth. -/
theorem band320_of_boxH (hB : BoxPureH L F0 n R F J1 t) : BandOnP L R (-320) 8 :=
  bandOnP_mono (band_of_boxH hB) (by decide) (Int.le_refl _)

end Spike.Lib.X64.HelloPh.OwnBand

/-- info: 'Spike.Lib.X64.HelloPh.OwnBand.band_of_boxH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnBand.band_of_boxH

/-- info: 'Spike.Lib.X64.HelloPh.OwnBand.band320_of_boxH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnBand.band320_of_boxH
