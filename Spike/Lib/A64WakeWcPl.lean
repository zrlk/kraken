/-
**`wc_main`'s placement up to the box's store** (AArch64, wake.w, at the
root's choices `IW := immsW2 Λ0 wakeImms`): every control of `wc_main`'s
nodes from its entry to `.sp0`'s store is `c0W` (with a hold at the store),
placed at the start's labels `L0T` (`WakeImmsC0.placedSE_c0WW`); the
allocator's states are placed by `PlacedAlloc.allocW_placed_new`.

- `blkW_pl`, `nodeW_pl`: a node whose controls are `c0W` (up to a hold) is
  placed.
- `hplP_W`: `WcPreW` inside the placement (`WcWfS.wcPreW_WS`'s `hpl`).
- `hplS_W`: `WcSp0W` inside the placement.
-/
import Spike.Lib.A64WakePlacedAlloc
import Spike.Lib.A64WakeMainL
import Spike.Lib.A64WakeHClW
import Spike.Lib.WakeImmsC0
import Spike.Lib.A64WakeWcWfS

namespace Spike.Lib.A64.WakePh.WcPl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (ND BlkW NodeW holdCtr)
open Spike.Lib.A64.WakePh.MainGlue (JS)
open Spike.Lib.A64.Flow.WakeM (wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W sN wN wcJ)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.WakeC0 (c0W)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o)

set_option hygiene false in
/-- The root's immediate table (`WakeFinalCAW.iW`). -/
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
/-- The placement at the start's labels, no frame. -/
local notation "PL" => fun s c => Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c []

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **A block whose controls are `c0W` with some hold is placed.** -/
theorem blkW_pl {n : ND} {blk : List Directive} (h : ∀ σ c, n.J σ c → ∃ hd, c = { c0W with hold := hd }) :
    BlkW (PL) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.A64.AllocG.BlkW.imp (Spike.Lib.A64WakeMainL.blkW_ctl (P := fun c => ∃ hd, c = { c0W with hold := hd }) h)
    Spike.Lib.A64.Flow.BlkW.triv fun s _ ⟨_, hc⟩ _ => hc ▸ Spike.Lib.A64.WakePh.WcWf.PlacedSE.hold.2
      (Spike.Lib.WakeImmsC0.placedSE_c0WW hp s)

/-- **A node whose controls are `c0W` with some hold is placed.** -/
theorem nodeW_pl {n : ND} (h : ∀ σ c, n.J σ c → ∃ hd, c = { c0W with hold := hd }) :
    NodeW (PL) (fun _ _ => False) exe endPc R F n :=
  Spike.Lib.A64.AllocG.NodeW.imp (Spike.Lib.A64WakeMainL.nodeW_ctl (P := fun c => ∃ hd, c = { c0W with hold := hd }) h)
    Spike.Lib.A64.Flow.NodeW.triv fun s _ ⟨_, hc⟩ _ => hc ▸ Spike.Lib.A64.WakePh.WcWf.PlacedSE.hold.2
      (Spike.Lib.WakeImmsC0.placedSE_c0WW hp s)

end Nodes

/-- `JW`'s controls are `c0W` (no hold). -/
theorem c0_JW {σC σ : Spike.Lib.A64.Flow.AS} {c : Spike.Lib.Ctl} (h : (JW) σC σ c) :
    ∃ hd, c = { c0W with hold := hd } :=
  ⟨c0W.hold, (Spike.Lib.A64.WakePh.WcWfS.wJ0_wNC_JS h).1⟩

/-- `wcJ JW`'s controls are `c0W`. -/
theorem c0_wcJ {σC σ : Spike.Lib.A64.Flow.AS} {c : Spike.Lib.Ctl} (h : wcJ ((JW) σC) σ c) : c = c0W :=
  let ⟨_, hJ, _⟩ := h
  (Spike.Lib.A64.WakePh.WcWfS.wJ0_wNC_JS hJ).1

/-- **`wc_main` up to the allocator's return inside the placement**, in a
region `R` with room for the allocator's call (`hR`, `hlo`, `hhi`). -/
theorem hplP_W {R : Spike.Lib.Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isaLSE2} (σC : Spike.Lib.A64.Flow.AS) :
    WcPreW (PL) (fun _ _ => False) (Ly).exe (Ly).endPc R F ms ((JW) σC) ((JW) σC) := by
  have hJc : ∀ σe c, (JW) σC σe c → L0T (Ly).Λ (Spike.Lib.WakeT1.mainTidLbl 2) = some σe.regs.X0.toNat :=
    fun σe c h => by
      rw [Spike.Lib.WakeHClW.hme_W hp IW, ← UInt64.toNat_toBitVec,
        (Spike.Lib.A64.WakePh.WcWfS.wJ0_wNC_JS h).2.2, (Ly).lab_pin]
      simp
  have hJs : ∀ σe c, (JW) σC σe c → c.term = .let_ "o" (.new (.var "z")) Spike.Lib.A64.Flow.WakeWc.boxTerm ∧
      (∃ tz, TermRun.lookupE c.env "z" = some (tz, [TermRun.cst (.num 0)])) ∧
      TermRun.evalAt c.env (.var "me") =
        some (.tid, [TermRun.cst (.loc ⟨Spike.Lib.WakeT1.mainTidLbl 2, 0⟩ 0)]) := fun σe c h => by
    rw [(Spike.Lib.A64.WakePh.WcWfS.wJ0_wNC_JS h).1]
    exact ⟨Spike.Lib.WakeC0.c0W_term, Spike.Lib.WakeC0.c0W_z, Spike.Lib.WakeC0.c0W_me⟩
  have hiz : (Ly).Λ.imms (.let_ "o" (.new (.var "z")) Spike.Lib.A64.Flow.WakeWc.boxTerm) "z" 0 = some 0 := by
    show IW _ "z" 0 = some 0
    rw [Spike.Lib.A64.WakePh.PlacedAlloc.newTerm_eq, Spike.Lib.WakeImmsC0.immsW2_of_ne (by simp) (by simp)]
    simp [SccCode.wakeImms]
  refine ⟨⟨blkW_pl hp fun σ c h => c0_JW hp h, nodeW_pl hp fun σ c ⟨_, h, _⟩ => c0_JW hp h,
      blkW_pl hp fun σ c ⟨_, _, h, _⟩ => c0_JW hp h, blkW_pl hp fun σ c ⟨_, _, h, _⟩ => c0_JW hp h⟩,
    blkW_pl hp fun σ c h => ⟨c0W.hold, c0_wcJ hp h⟩,
    fun q _ _ => Spike.Lib.A64.WakePh.PlacedAlloc.allocW_placed_new hR hlo hhi hJc hJs hiz⟩

/-- **`.sp0` inside the placement**: its controls are `c0W` with the
counter's hold. -/
theorem hplS_W {R : Spike.Lib.Region} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isaLSE2}
    (σC : Spike.Lib.A64.Flow.AS) :
    WcSp0W (PL) (fun _ _ => False) (Ly).exe (Ly).endPc R F ms ((JW) σC) :=
  ⟨blkW_pl hp fun σ c ⟨q, hw, o, hc, _⟩ => ⟨some (ms.ctr, TermRun.cst (.num o.toNat)), by
      rw [hc, c0_wcJ hp hw]; rfl⟩,
    nodeW_pl hp fun σ c ⟨q, o, hw, hc, _⟩ => ⟨some (ms.ctr, TermRun.cst (.num o.toNat)), by
      rw [hc, c0_wcJ hp hw]; rfl⟩⟩

end Spike.Lib.A64.WakePh.WcPl

/-- info: 'Spike.Lib.A64.WakePh.WcPl.hplP_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcPl.hplP_W

/-- info: 'Spike.Lib.A64.WakePh.WcPl.hplS_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.WcPl.hplS_W
