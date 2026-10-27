/-
**The abort path's write tail closed** (AArch64), for any executable and
layout: `scc_rt_abort`'s path to stub `dx` (`AbIn`, `abIn_steps`) in front
of the stub's tail (`StubDt`, `stubDt_closed`), back to front by
`ClosedC.rel` (`Spike/Lib/TailDt.lean`).

- `AbDt exe endPc RA C dx`: the abort path to stub `dx` or the stub's tail;
- `abDt_closed`: `AbDt` is closed under certification, given the
  dispatcher's and the stub's code and `AbDt` off the transfer sites;
- `abDt_noSite_write`: the `write` stub's `AbDt` off the transfer sites at
  a runtime layout's phase checks (`A64AbNoSite`).
-/
import Spike.Lib.Rt.A64AbNoSite

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem
open Scc.Sem.A64 (abi)
open Spike.Lib.A64.Flow
open Spike.Lib.A64
open Spike.Lib (ClosedC StepsTo Region)
open Spike.Lib.A64.Abort.Disp (DX)
open Spike.Lib.A64.PhRec (okPc μ)

/-- **The abort path's write tail** to stub `dx`: on the path (`AbIn`) in
the region `RA` under `C`, or in the stub's tail (`StubDt`). -/
def AbDt (exe : _root_.Executable) (endPc : Int64) (RA : Region) (C : MachineData → Prop) (dx : DX)
    (s : State) : Prop :=
  AbIn exe endPc RA C dx s ∨ StubDt exe endPc (_root_.Executable.labels exe).label dx.stub s

section Closed

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {RA : Region} {C : MachineData → Prop}

/-- **The abort path's write tail is closed under certification**,
keeping the promises, given the dispatcher's and stub `dx`'s code (any
ghosts), the region's facts, `C` kept by writes inside the region and the
tail off the transfer sites. -/
theorem abDt_closed {dx : DX} {c0 c1 : Ctl} (hd : Abort.Disp.Code c0 exe endPc)
    (hs : Abort.Code dx.stub c1 dx.b1 exe endPc) (hR : RA.OK) (hal : RA.base.toNat % 16 = 0)
    (hlo : RA.lo ≤ -48) (hhi : 0 ≤ RA.hi) (hC : FStable RA C)
    (hns : ∀ s, AbDt exe endPc RA C dx s → Kernel.siteAt abi μ s = none) (x : Kernel.KState) :
    ClosedC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x 0) 0 (AbDt exe endPc RA C dx) :=
  ClosedC.rel (abIn_steps hd hs hR hal hlo hhi hC fun s h => hns s (.inl h))
    (stubDt_closed hs rfl (fun s h => hns s (.inr h)) x)

end Closed

/-- **The `write` stub's tail is off the transfer sites** at a runtime
layout, from the phase checks of the path (`abIn_noSite_write`) and of the
stub's tail (`stubDt_noSite`'s premises). -/
theorem abDt_noSite_write (L : RuntimeLayout) {RA : Region} {C : MachineData → Prop}
    (hA : ∀ s, AbIn L.exe L.endPc RA C .write s → Kernel.siteAt abi (μ L) s = none)
    (hS : ∀ s, StubDt L.exe L.endPc L.lab Abort.write s → Kernel.siteAt abi (μ L) s = none)
    (hlab : (_root_.Executable.labels L.exe).label = L.lab) :
    ∀ s, AbDt L.exe L.endPc RA C .write s → Kernel.siteAt abi (μ L) s = none := by
  rintro s (h | h)
  · exact hA s h
  · exact hS s (by rw [← hlab]; exact h)

end Spike.Lib.A64.Rt

/-- info: 'Spike.Lib.A64.Rt.abDt_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Rt.abDt_closed
