/-
**The root's `halloc` from a control placed at every state** (AArch64; the root-halloc row): when
`wc_main`'s caller's controls are one control `c0` placed at every state (`hc0`, the root's own field), the
allocator's states are placed at every box call returning to `.sp0` (`HelloRootPrem.halloc`'s shape, any layout,
labels, region with room, memory side, invariants). `PlacedAlloc.allocW_placed_wcH` at the caller's slot `-144`: the
call node's control is the caller's (`wNH .call`'s `wcJH J1`), so `c0`, placed whatever the slot holds.

- `halloc_of_hc0`: the statement, generic in the layout `L` (any `RuntimeLayout`), the labels and `c0`.
-/
import Spike.Lib.A64HelloPlacedAlloc

namespace Spike.Lib.A64.HelloPh.HallocC0

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64.Flow.HelloWc (wARH WcCtxH)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)

/-- **`halloc` from `hc0`** (module doc). -/
theorem halloc_of_hc0 {L : RuntimeLayout} {lbl : Lbl} {c0 : Spike.Lib.Ctl}
    (hc0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 []) :
    ∀ (R : Spike.Lib.Region) (F : MachineData → Prop) (ms : Spike.Lib.MemSide isaLSE2)
      (J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop), R.OK → R.lo ≤ -144 → 0 ≤ R.hi →
      (∀ σ c, J1 σ c → c = c0) → ∀ q : Call, q.OKB ms L.lab → q.ra = (L.lab ".L22_wc_main.sp0").toBitVec →
      AllocW ms q (fun s c => Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc
        (wARH R) (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms L.lab R J0 J1 q m) := by
  intro R F ms J0 J1 hR hlo hhi hJ1 q _ _
  refine Spike.Lib.A64.HelloPh.PlacedAlloc.allocW_placed_wcH (k := -144) hR hlo hhi
    ⟨by decide, hlo, by omega⟩ (Int.le_refl _) ?_
  rintro σC - ⟨⟨σe, hj, -⟩, -⟩ s -
  rw [hJ1 σe _ hj]
  exact hc0 s

end Spike.Lib.A64.HelloPh.HallocC0

/-- info: 'Spike.Lib.A64.HelloPh.HallocC0.halloc_of_hc0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.HallocC0.halloc_of_hc0
