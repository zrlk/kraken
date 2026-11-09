/-
**hello.w on x86-64: the saved return address at `wc_main`'s entry is `.x3`** (the twin of
`Spike/Lib/A64HelloSegEndRa.lean`): from `wc_main`'s entry invariant at level 1, `wcJ0 (mWC lab σC Jr).J σ1`, the
return address `FrMGH` records (`fr.2`) is `lab mainX3`, the segment end's pin of main's saved return address.

The source of the pin is `wcJ0` itself: `Hello1.mWC`'s invariant has the slot at `%rsp` (offset `-80` of the
caller's frame) holding `lab ".Lscc_rt_main.x1"` (`call wc_main`'s pushed return address; `MainPost.mainX3` is
the same label), and `wcJ0`'s `σ = enter (-80) σC` rebases the slots so that it is the entry state's `slot 0`,
which is `FrMGH`'s `fr.2`.

- `fr_ra_mainX3`: `FrMGH` at `wcJ0 (mWC lab σC Jr).J σ1` pins the saved return address to `lab mainX3`.

**Where this differs from AArch64** (forced by the x86-64 shape): the return address is pushed by `call` and read
from the entry state's `slot 0` (AArch64: the link register `x30`, `FrMGH`'s `fr.2` the entry's `x30`); the return
point is `.Lscc_rt_main.x1` (`mainX3`; AArch64: `.L1_scc_rt_main.sp1`, `mainSp1`), so the theorem is
`fr_ra_mainX3` (AArch64: `fr_ra_mainSp1`). A64's `hra_of_FrMGH` is dead and not twinned.
-/
import Spike.Lib.X64HelloWcMid
import Spike.Lib.X64HelloMain
import Spike.Lib.X64HelloMainPost

namespace Spike.Lib.X64.HelloPh.SegEndRa

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcJ0)
open Spike.Lib.X64.Flow.HelloWc (FrMGH)
open Spike.Lib.X64.Flow.Worker.Hello.MainPost (mainX3)

/-- **The saved return address at `wc_main`'s level-1 entry is `.x3`**: `FrMGH` at `wcJ0 (mWC lab σC Jr).J σ1`
makes `fr.2` the entry's `slot 0`, the caller's slot `-80`, which `mWC` pins to `call wc_main`'s return. -/
theorem fr_ra_mainX3 {lab : Label → Int64} {σC σ1 : Spike.Lib.X64.AS} {Jr : Spike.Lib.X64.AS → Ctl → Prop}
    {fr : BitVec 64 × BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me : BitVec 64}
    (h : FrMGH (wcJ0 (mWC lab σC Jr).J σ1) fr sl me) : Int64.ofBitVec fr.2 = lab mainX3 := by
  obtain ⟨σe, c, ⟨rfl, -, -, -, -, -, -, -, -, -, -, h80⟩, rfl, -, -⟩ := h
  simp only [Spike.Lib.X64.enter]
  rw [Int.add_zero, h80]; rfl

end Spike.Lib.X64.HelloPh.SegEndRa

/-- info: 'Spike.Lib.X64.HelloPh.SegEndRa.fr_ra_mainX3' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.SegEndRa.fr_ra_mainX3
