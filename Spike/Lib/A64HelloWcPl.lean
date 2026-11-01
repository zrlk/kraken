/-
**hello.w's `wc_main` placement up to the box's store** (AArch64,
hTop; the root-generic twin of
`Spike/Lib/A64WakeWcPl.lean`): every control of `wc_main`'s nodes from its
entry to `.sp0`'s store is one control `c0` (with a hold at the store),
placed at every state (`hc0`), so each node is placed; the allocator's
states are placed by a premise (`halloc`).

Wake states these at its root's choices (`immsW2 Λ0 wakeImms`, `c0W`,
`L0T`, `PlacedAlloc.allocW_placed_new`). hello has no root instance yet
(`HelloRootPrem`, B8 tier) and no frame-144 twin of
`PlacedAlloc` (B8 tier), so here the layout `Λ`, the labels `lbl`, the
control `c0` and its placement `hc0`, and the allocator's placement `halloc`
are premises; the root discharges `hc0` by its `placedSE_c0` and `halloc`
by the `PlacedAlloc` twin.

- `blkW_plH`, `nodeW_plH`: a node whose controls are `c0` (up to a hold) is
  placed.
- `hplP_WH`: `WcPreWH` inside the placement (`WcWfS.wcPreW_WSH`'s `hpl`).
- `hplS_WH`: `WcSp0WH` inside the placement (`WcWfS.wcSp0W_WSH`'s `hpl`).
-/
import Spike.Lib.A64HelloWcWfS
import Spike.Lib.A64WakeMainL

namespace Spike.Lib.A64.HelloPh.WcPl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64.Flow (ND BlkW NodeW holdCtr)
open Spike.Lib.A64.Flow.HelloWc (WcPreWH WcSp0WH wARH WcCtxH wcJH)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {c0 : Spike.Lib.Ctl}
  (hc0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c0 [])

set_option hygiene false in
/-- The placement at the labels `lbl`, no frame. -/
local notation "PL" => fun s c => Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c []

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
include hc0

/-- **A block whose controls are `c0` with some hold is placed.** -/
theorem blkW_plH {n : ND} {blk : List Directive} (h : ∀ σ c, n.J σ c → ∃ hd, c = { c0 with hold := hd }) :
    BlkW (PL) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.A64.AllocG.BlkW.imp (Spike.Lib.A64WakeMainL.blkW_ctl (P := fun c => ∃ hd, c = { c0 with hold := hd }) h)
    Spike.Lib.A64.Flow.BlkW.triv fun s _ ⟨_, hc⟩ _ => hc ▸ Spike.Lib.A64.WakePh.WcWf.PlacedSE.hold.2 (hc0 s)

/-- **A node whose controls are `c0` with some hold is placed.** -/
theorem nodeW_plH {n : ND} (h : ∀ σ c, n.J σ c → ∃ hd, c = { c0 with hold := hd }) :
    NodeW (PL) (fun _ _ => False) exe endPc R F n :=
  Spike.Lib.A64.AllocG.NodeW.imp (Spike.Lib.A64WakeMainL.nodeW_ctl (P := fun c => ∃ hd, c = { c0 with hold := hd }) h)
    Spike.Lib.A64.Flow.NodeW.triv fun s _ ⟨_, hc⟩ _ => hc ▸ Spike.Lib.A64.WakePh.WcWf.PlacedSE.hold.2 (hc0 s)

end Nodes

include hc0

/-- **`wc_main` up to the allocator's return inside the placement**: the
entry's controls (`hJ0`) are `c0`; the allocator's states placed at every
box allocation returning to `.sp0` (`halloc`, the frame-144 twin of wake's
`PlacedAlloc.allocW_placed_new`). -/
theorem hplP_WH {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {ms : Spike.Lib.MemSide isaLSE2} {J0 J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hJ0 : ∀ σ c, J0 σ c → c = c0)
    (halloc : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label →
      q.ra = ((_root_.Executable.labels exe).label ".L22_wc_main.sp0").toBitVec →
      AllocW ms q (PL) (fun _ _ => False) exe endPc (wARH R)
        (fun m => F m ∧ CallerCells R (-144) (-160) 0 m ∧ WcCtxH ms (_root_.Executable.labels exe).label R J0 J1 q m)) :
    WcPreWH (PL) (fun _ _ => False) exe endPc R F ms J0 J1 :=
  have h0 : ∀ σ c, J0 σ c → ∃ hd, c = { c0 with hold := hd } := fun σ c h => ⟨c0.hold, hJ0 σ c h⟩
  ⟨⟨blkW_plH hc0 fun σ c h => h0 σ c h, nodeW_plH hc0 fun _ c ⟨_, h, _⟩ => h0 _ c h,
      blkW_plH hc0 fun _ c ⟨_, _, h, _⟩ => h0 _ c h, blkW_plH hc0 fun _ c ⟨_, _, h, _⟩ => h0 _ c h⟩,
    blkW_plH hc0 fun _ c ⟨_, h, _⟩ => h0 _ c h, halloc⟩

/-- **`.sp0` inside the placement**: the allocator's caller's controls
(`hJ1`) are `c0`, so `.sp0`'s are `c0` with the counter's hold. -/
theorem hplS_WH {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {ms : Spike.Lib.MemSide isaLSE2} {J1 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hJ1 : ∀ σ c, J1 σ c → c = c0) :
    WcSp0WH (PL) (fun _ _ => False) exe endPc R F ms J1 :=
  ⟨blkW_plH hc0 fun σ c ⟨q, ⟨_, hw, _⟩, o, hc, _⟩ => ⟨some (ms.ctr, TermRun.cst (.num o.toNat)), by
      rw [hc, hJ1 _ _ hw]; rfl⟩,
    nodeW_plH hc0 fun σ c ⟨q, o, ⟨_, hw, _⟩, hc, _⟩ => ⟨some (ms.ctr, TermRun.cst (.num o.toNat)), by
      rw [hc, hJ1 _ _ hw]; rfl⟩⟩

end Spike.Lib.A64.HelloPh.WcPl

/-- info: 'Spike.Lib.A64.HelloPh.WcPl.blkW_plH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPl.blkW_plH

/-- info: 'Spike.Lib.A64.HelloPh.WcPl.hplP_WH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPl.hplP_WH

/-- info: 'Spike.Lib.A64.HelloPh.WcPl.hplS_WH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WcPl.hplS_WH
