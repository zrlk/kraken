/-
**The runtime rows' phase checks** (`RtNodesOk`): every row of a block
table passes the block phase check (`blkPh`, `Spike/Lib/A64SegInst.lean`) at
its address, the premise of the runtime's node obligations inside `W`
(`Spike/Lib/Rt/A64RtW.lean`).

- **Temporary premise**: A6 (`Scc/Cert/Rt/PhasesA64.lean`, the phases of
  the placement check) discharges it per row from `placeOK`, at the phase
  index and off-site pcs it computes from the program (`phOf`, `okPcOf`), a
  row's dead targets any set holding its phase crossings (`crossOf`).
- `ra` is keyed by group (a function's return point; any pc in the entry's
  phase for a row without a `ret`), `dead` by row (`g.l`, `b.k`): a row in
  the abort's phase may branch to the abort label, so one global set does
  not fit every row.
- The `ret` targets' values and the dead targets never reached are run
  facts, not part of this premise.
- **Oracle**: `ret0.w`'s runtime groups at the hand labels, phases and
  off-site pcs (`Spike/Test/A64RtNodes.lean`).
-/
import Spike.Lib.A64SegInst
import Scc.Cert.Rt.OffsA64

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising.AArch64
open Spike.Lib.A64Consumer (blkPh)
open Scc.Cert.Rt.A64 (OGrp OBlk)

/-- **A row's phase check at its address** `lab g.l + 4·b.k`, returning to
its group's `ra`, its dead targets `dead g.l b.k`. -/
def rowPh (okPc : Nat → Bool) (ph : Nat → Nat) (dead : Label → Nat → Nat → Bool) (lab : Label → Int64)
    (ra : Label → Int64) (g : OGrp) (b : OBlk) : Bool :=
  blkPh okPc ph (dead g.l b.k) lab (lab g.l + Int64.ofNat (4 * b.k)) (ra g.l) b.blk

/-- **Every row of `gs` passes its phase check** (temporary; A6). -/
def RtNodesOk (okPc : Nat → Bool) (ph : Nat → Nat) (dead : Label → Nat → Nat → Bool) (lab : Label → Int64)
    (ra : Label → Int64) (gs : List OGrp) : Prop :=
  ∀ g ∈ gs, ∀ b ∈ g.bs, rowPh okPc ph dead lab ra g b = true

/-- `RtNodesOk`, decided. -/
def rtNodesOk (okPc : Nat → Bool) (ph : Nat → Nat) (dead : Label → Nat → Nat → Bool) (lab : Label → Int64)
    (ra : Label → Int64) (gs : List OGrp) : Bool :=
  gs.all fun g => g.bs.all fun b => rowPh okPc ph dead lab ra g b

theorem rtNodesOk_sound {okPc : Nat → Bool} {ph : Nat → Nat} {dead : Label → Nat → Nat → Bool}
    {lab ra : Label → Int64} {gs : List OGrp} (h : rtNodesOk okPc ph dead lab ra gs = true) :
    RtNodesOk okPc ph dead lab ra gs := by
  intro g hg b hb
  exact List.all_eq_true.mp (List.all_eq_true.mp h g hg) b hb

/-- A row of a group of `gs`: its phase check. -/
theorem RtNodesOk.row {okPc : Nat → Bool} {ph : Nat → Nat} {dead : Label → Nat → Nat → Bool}
    {lab ra : Label → Int64} {gs : List OGrp} (h : RtNodesOk okPc ph dead lab ra gs) {g : OGrp} (hg : g ∈ gs)
    {b : OBlk} (hb : b ∈ g.bs) :
    blkPh okPc ph (dead g.l b.k) lab (lab g.l + Int64.ofNat (4 * b.k)) (ra g.l) b.blk = true :=
  h g hg b hb

end Spike.Lib.A64.Rt
