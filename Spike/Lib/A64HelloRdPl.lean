/-
**hello.w's `wc_rodata` placement from the allocator's return** (AArch64; the
rodata-post twin of `A64HelloWcPl`): every node of `wc_rodata` from `.sp0` and `scc_rt_main`'s `.sp0`
block is placed (`PlacedSE` at no frame) once its invariants' controls are placed at every state.

`wc_main`'s controls up to the box's store are one control `c0` (`WcPl.hplP_WH`); `wc_rodata`'s from `.sp0`
are not (two local runs, two exchanges, a fence), so here the placement of each invariant's controls is the
premise (`hPl`), the instance's (as `HelloRootPrem.hc0` is `c0`'s).

- `blkW_plR`, `nodeW_plR`: a node whose controls are placed at every state is placed.
- `hplR_WH`: `RdPostW` inside the placement (`RdWfS.rdPostW_WSH`'s `hpl`).
- `hplB1_WH`: `scc_rt_main`'s `.sp0` block inside the placement (`RdWfS.mB1W_WSH`'s `hpl`).
-/
import Spike.Lib.A64HelloRdPostWfS
import Spike.Lib.A64WakeMainL

namespace Spike.Lib.A64.HelloPh.RdPl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64.Flow (ND BlkW NodeW)
open Spike.Lib.A64.Flow.HelloRd (pN RdPostW)
open Spike.Lib.A64.Flow.Hello1 (mS0 mB1)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl}

set_option hygiene false in
/-- The placement at the labels `lbl`, no frame. -/
local notation "PL" => fun s c => Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c []

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A block whose controls are placed at every state is placed.** -/
theorem blkW_plR {n : ND} {blk : List Directive}
    (h : ∀ σ c, n.J σ c → ∀ s, Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c []) :
    BlkW (PL) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.A64.AllocG.BlkW.imp
    (Spike.Lib.A64WakeMainL.blkW_ctl (P := fun c => ∀ s, Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c []) h)
    Spike.Lib.A64.Flow.BlkW.triv fun s _ hc _ => hc s

/-- **A node whose controls are placed at every state is placed.** -/
theorem nodeW_plR {n : ND} (h : ∀ σ c, n.J σ c → ∀ s, Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c []) :
    NodeW (PL) (fun _ _ => False) exe endPc R F n :=
  Spike.Lib.A64.AllocG.NodeW.imp
    (Spike.Lib.A64WakeMainL.nodeW_ctl (P := fun c => ∀ s, Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c []) h)
    Spike.Lib.A64.Flow.NodeW.triv fun s _ hc _ => hc s

end Nodes

/-- **`wc_rodata` from the allocator's return inside the placement**: every control of its eight invariants
(`.sp0`'s `Jp`, after the local runs `Jp'`, `J2'`, after the loads `J1`, `J3`, after the stores `J2`, `J4`, after
the fence `J5`) placed at every state (`hPl`). -/
theorem hplR_WH {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {Jp Jp' J1 J2 J2' J3 J4 J5 : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hPl : ∀ σ0 c, (Jp σ0 c ∨ Jp' σ0 c ∨ J1 σ0 c ∨ J2 σ0 c ∨ J2' σ0 c ∨ J3 σ0 c ∨ J4 σ0 c ∨ J5 σ0 c) →
      ∀ s, Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c []) :
    RdPostW (PL) (fun _ _ => False) exe endPc R F Jp Jp' J1 J2 J2' J3 J4 J5 :=
  ⟨blkW_plR fun σ c h => hPl σ c (.inl h),
    nodeW_plR fun _ c ⟨σ0, _, h, _⟩ => hPl σ0 c (.inr (.inl h)),
    blkW_plR fun _ c ⟨σ0, _, h, _⟩ => hPl σ0 c (.inr (.inr (.inl h))),
    nodeW_plR fun _ c ⟨σ0, _, h, _⟩ => hPl σ0 c (.inr (.inr (.inl h))),
    blkW_plR fun _ c ⟨σ0, _, h, _⟩ => hPl σ0 c (.inr (.inr (.inr (.inl h)))),
    nodeW_plR fun _ c ⟨σ0, _, h, _⟩ => hPl σ0 c (.inr (.inr (.inr (.inr (.inl h))))),
    blkW_plR fun _ c ⟨σ0, _, h, _⟩ => hPl σ0 c (.inr (.inr (.inr (.inr (.inr (.inl h)))))),
    nodeW_plR fun _ c ⟨σ0, _, h, _⟩ => hPl σ0 c (.inr (.inr (.inr (.inr (.inr (.inl h)))))),
    nodeW_plR fun _ c ⟨σ0, _, h, _⟩ => hPl σ0 c (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))),
    blkW_plR fun _ c ⟨σ0, _, h, _⟩ => hPl σ0 c (.inr (.inr (.inr (.inr (.inr (.inr (.inr h)))))))⟩

/-- **`scc_rt_main`'s `.sp0` block inside the placement**: `wc_rodata`'s return invariant's controls (`Jr`) placed
at every state (`hPl`). -/
theorem hplB1_WH {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {σC : Spike.Lib.A64.Flow.AS} {Jr : Spike.Lib.A64.Flow.AS → Spike.Lib.Ctl → Prop}
    (hPl : ∀ σ c, Jr σ c → ∀ s, Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c []) :
    BlkW (PL) (fun _ _ => False) exe endPc R F (mS0 (_root_.Executable.labels exe).label R σC Jr) mB1 :=
  blkW_plR fun _ c ⟨σx, h, _⟩ => hPl σx c h

end Spike.Lib.A64.HelloPh.RdPl

/-- info: 'Spike.Lib.A64.HelloPh.RdPl.blkW_plR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdPl.blkW_plR

/-- info: 'Spike.Lib.A64.HelloPh.RdPl.hplR_WH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdPl.hplR_WH

/-- info: 'Spike.Lib.A64.HelloPh.RdPl.hplB1_WH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdPl.hplB1_WH
