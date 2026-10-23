/-
**The runtime rows' phase checks on x86-64** (`RtNodesOk`): every row of a
block table passes the block phase check (`blkPh`,
`Spike/Lib/X64SegInst.lean`) at its address, the premise of the runtime's
node obligations inside `W` (`Spike/Lib/Rt/X64RtW.lean`). The twin of
`Spike/Lib/Rt/A64RtNodes.lean`; a row sits `b.off` bytes after its group's
label (variable-length cells), not `4·b.k`.

- **Temporary premise**: A6 (`phOf`, `okPcOf` of the x86-64 placement
  phases) discharges it per row from `placeOK`, a row's dead targets any set
  holding its phase crossings.
- **Site rows are skipped** (`siteBlk`): x86-64's table keeps each site's
  one-byte `nop` as a row of its own, a pc off `okPc`; its obligation is
  the site's (`takeSiteW`), not a node's. As x86-64's A6 (`phasesOkT`'s
  `siteRow`, its extraction lemmas' `b.blk ≠ siteBlk`), so `RtNodesOk` falls
  out of it.
- `ra` is keyed by group (a function's return point; any pc in the entry's
  phase for a row without a `ret`), `dead` by row (`g.l`, `b.k`).
- **Oracle**: `ret0.x`'s runtime groups at the hand labels, phases and
  off-site pcs (`Spike/Test/X64RtNodes.lean`).
-/
import Spike.Lib.X64SegInst
import Scc.Cert.Rt.OffsX64

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising.X64
open Spike.Lib.X64Consumer (blkPh)
open Scc.Cert.Rt.X64 (OGrp OBlk)

/-- **A site's instruction**: the one-byte `nop` (as
`Scc.Cert.Rt.X64.siteBlk`, `Scc/Cert/Rt/PhasesX64.lean`, by `rfl`; a local copy
of that definition). -/
def siteBlk : List (Directive × Nat) := [(Kraken.Promising.Lower.X64.op64 (.nop 1), 1)]

/-- **A row's phase check at its address** `lab g.l + b.off`, returning to
its group's `ra`, its dead targets `dead g.l b.k`. -/
def rowPh (okPc : Nat → Bool) (ph : Nat → Nat) (dead : Label → Nat → Nat → Bool) (lab : Label → Int64)
    (ra : Label → Int64) (g : OGrp) (b : OBlk) : Bool :=
  blkPh okPc ph (dead g.l b.k) lab (lab g.l + Int64.ofNat b.off) (ra g.l) b.blk

/-- **Every row of `gs` but a site's `nop` passes its phase check**
(temporary; A6). -/
def RtNodesOk (okPc : Nat → Bool) (ph : Nat → Nat) (dead : Label → Nat → Nat → Bool) (lab : Label → Int64)
    (ra : Label → Int64) (gs : List OGrp) : Prop :=
  ∀ g ∈ gs, ∀ b ∈ g.bs, b.blk ≠ siteBlk → rowPh okPc ph dead lab ra g b = true

/-- `RtNodesOk`, decided. -/
def rtNodesOk (okPc : Nat → Bool) (ph : Nat → Nat) (dead : Label → Nat → Nat → Bool) (lab : Label → Int64)
    (ra : Label → Int64) (gs : List OGrp) : Bool :=
  gs.all fun g => g.bs.all fun b => decide (b.blk = siteBlk) || rowPh okPc ph dead lab ra g b

theorem rtNodesOk_sound {okPc : Nat → Bool} {ph : Nat → Nat} {dead : Label → Nat → Nat → Bool}
    {lab ra : Label → Int64} {gs : List OGrp} (h : rtNodesOk okPc ph dead lab ra gs = true) :
    RtNodesOk okPc ph dead lab ra gs := by
  intro g hg b hb hs
  have := List.all_eq_true.mp (List.all_eq_true.mp h g hg) b hb
  simpa [hs] using this

/-- A row of a group of `gs`, not a site's `nop` (`hs`): its phase check. -/
theorem RtNodesOk.row {okPc : Nat → Bool} {ph : Nat → Nat} {dead : Label → Nat → Nat → Bool}
    {lab ra : Label → Int64} {gs : List OGrp} (h : RtNodesOk okPc ph dead lab ra gs) {g : OGrp} (hg : g ∈ gs)
    {b : OBlk} (hb : b ∈ g.bs) (hs : b.blk ≠ siteBlk) :
    blkPh okPc ph (dead g.l b.k) lab (lab g.l + Int64.ofNat b.off) (ra g.l) b.blk = true :=
  h g hg b hb hs

end Spike.Lib.X64.Rt
