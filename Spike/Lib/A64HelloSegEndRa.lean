/-
**hello.w on AArch64: the saved return address at `wc_main`'s clone is `.sp1`** (row 5j-segEnd-ra): the
segment end's `hra` (`HelloMainHRD.MainSegH.hra`, `Int64.ofBitVec ra = lab mainSp1`) from `wc_main`'s entry
invariant at level 1, `wcJ0 (mWC lab σC Jr).J σ1`.

The source of the pin is `wcJ0` itself: `Hello1.mWC`'s invariant has `x30 = lab ".L1_scc_rt_main.sp1"` (the
`bl`'s return; `MainPost.mainSp1` is the same label), and `wcJ0`'s `σ = enter (-80) σC` keeps the registers. The
prologue's store of `x30` into slot `-8` surviving to the clone is `HelloWc.FrMGH` (`fr` one entry state's
`x29`, `x30`), which `HelloWc.rXH_wcN3H` / `hello_wc_mid_segW` keep up to the clone's `svc`, where
`WcSp6.FrWH` has `σ.slot (-8) = fr.2`.

Differences from the existing segment end: `MainSegH.hra` was an open premise of `hMainRH_ofI`'s `hpc`; here it
is discharged from `FrMGH` at `wcJ0`, given the clone landing's `JS` slot `-8` is `fr.2`. No premise is carried
from level 1.

- `fr_ra_mainSp1`: `FrMGH` at `wcJ0 (mWC lab σC Jr).J σ1` pins the saved `x30` to `lab mainSp1`.
- `hra_of_FrMGH`: at the clone landing's `JS` with slot `-8` the saved `x30`, `MainSegH.hra`.
-/
import Spike.Lib.A64HelloWcMid
import Spike.Lib.A64HelloMain
import Spike.Lib.A64HelloMainPost
import Spike.Lib.A64HelloParent

namespace Spike.Lib.A64.HelloPh.SegEndRa

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcJ0)
open Spike.Lib.A64.Flow.HelloWc (FrMGH)
open Spike.Lib.A64.Flow.Worker.Hello.MainPost (mainSp1)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (JS)

/-- **The saved `x30` at `wc_main`'s level-1 entry is `.sp1`**: `FrMGH` at `wcJ0 (mWC lab σC Jr).J σ1` makes
`fr.2` the entry's `x30`, which `mWC` pins to the `bl`'s return. -/
theorem fr_ra_mainSp1 {lab : Label → Int64} {σC σ1 : Spike.Lib.A64.Flow.AS} {Jr : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    {fr : BitVec 64 × BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me : BitVec 64}
    (h : FrMGH (wcJ0 (mWC lab σC Jr).J σ1) fr sl me) : Int64.ofBitVec fr.2 = lab mainSp1 := by
  obtain ⟨σe, c, ⟨rfl, -, -, -, -, -, -, -, -, -, h30⟩, rfl, -, -⟩ := h
  simp only [enter]
  rw [h30]; rfl

/-- **`MainSegH.hra` at the clone landing**: `JS`'s return address `ra` (slot `-8`) is the saved `x30` `fr.2`
(`hfr`, `WcSp6.FrWH`'s), and `FrMGH` at level 1's `wcJ0` pins it to `.sp1`. -/
theorem hra_of_FrMGH {exe : _root_.Executable} {cP : Ctl} {cA x29 ra tp : BitVec 64} {c : Ctl}
    {σ σC σ1 : Spike.Lib.A64.Flow.AS} {Jr : Spike.Lib.A64.Flow.AS → Ctl → Prop}
    {fr : BitVec 64 × BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me : BitVec 64}
    (hJS : JS cP cA x29 ra tp σ c) (hfr : σ.slot (-8) = fr.2)
    (h : FrMGH (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr).J σ1) fr sl me) :
    Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1 := by
  rw [← hJS.2.2.2.1, hfr]; exact fr_ra_mainSp1 h

end Spike.Lib.A64.HelloPh.SegEndRa

/-- info: 'Spike.Lib.A64.HelloPh.SegEndRa.fr_ra_mainSp1' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.SegEndRa.fr_ra_mainSp1

/-- info: 'Spike.Lib.A64.HelloPh.SegEndRa.hra_of_FrMGH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.SegEndRa.hra_of_FrMGH
