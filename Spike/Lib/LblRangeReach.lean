/-
**Every placed label in the heap at every level reachable by allocations**
(ISA-neutral): from a start placing no label (`lay2`'s `static := none`),
every placement reachable by allocations keeps its labels inside the arena
(`LblArena.reach`), so, with the arena inside the heap (`arOf_sub`), its labels
are inside the heap (`LblArena.lblRange`). This is `LblRange` (`printW_w2B`'s `hrg`,
the lane stores' `hrg`) at `nodes2_of_starts`' levels: the reachable `L ls`
and a fresh allocation's `upd L l b`, `updN ls l n`.

- `lblRange_reach`: at a reachable placement;
- `lblRange_upd`: at a fresh allocation's placement past a reachable one.
-/
import Spike.Lib.LblArena

namespace Spike.Lib

open Scc.Sem (Range Layout)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.AllocReach (upd updN Reach)
open Spike.Lib.LowerNode (LblRange)

variable {Λ : Layout} {ar : Arena} {L0 L : WeakMem.AllocLabel → Option Nat} {ls0 ls : WeakMem.AllocLabel → Nat}

/-- **Every placed label in the heap at a reachable placement**: from a
start placing no label (`hL0`), the arena inside the heap (`hs`). -/
theorem lblRange_reach (hs : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hL0 : ∀ l, L0 l = none)
    (hR : Reach ar L0 ls0 L ls) : LblRange Λ L ls :=
  (LblArena.reach (fun l b h => by rw [hL0 l] at h; cases h) hR).lblRange hs

/-- **Every placed label in the heap at a fresh allocation's placement**:
the label `l` placed at `b` with `n` words where the arena hands it out
(`hland`), past a reachable placement (`hR`). -/
theorem lblRange_upd (hs : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hL0 : ∀ l, L0 l = none)
    (hR : Reach ar L0 ls0 L ls) {l : WeakMem.AllocLabel} {b n : Nat} (hland : AllocLand ar.heap ar.cells b n) :
    LblRange Λ (upd L l b) (updN ls l n) :=
  ((LblArena.reach (fun l b h => by rw [hL0 l] at h; cases h) hR).alloc hland).lblRange hs

end Spike.Lib

/-- info: 'Spike.Lib.lblRange_upd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.lblRange_upd
