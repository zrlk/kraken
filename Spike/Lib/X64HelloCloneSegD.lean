/-
**The clone state's facts for main's segment end, as `h2`'s fence states them, on x86-64** (the twin of
`Spike/Lib/A64HelloCloneSegD.lean`): `CloneSegD`, the body of hello's `CloneSegH`, stated where `h2`'s invariant
can import it (the clone segment's module imports `h2`'s through the root premises).

- `CloneSegD`: `At` of the clone's node with `Hello.Parent.JS` in the widened region `⟨Rm.base, -128, 40⟩`, its
  base (`%rbp`) 128 above `%rsp`, the region not wrapping, the base 16-aligned, the return address `mainX3`'s,
  `%r15` the cell.

## Differences from the AArch64 version

- The region is `⟨Rm.base, -128, 40⟩` (AArch64: `⟨Rm.base, -144, 48⟩`, base 144 above `sp`): `wc_main`'s frame
  of 128 below `%rbp`, and above it the saved `%rbp`, the return address and `scc_rt_main`'s frame up to its
  spill `-48(%rbp)` at offset `32` (`scc_rt_main`'s `%rbp` is `80` above `wc_main`'s); `hi = 40` as wake's
  `X64WakeSpawnR.MainWS.hRhi`.
- The node's caller words are `JS`'s `fp` (the saved `%rbp` at `0`; AArch64: `x29`); the return address is at
  `mainX3` (`.Lscc_rt_main.x1`; AArch64: `mainSp1`); the cell is in `%r15` (`X64HelloWcSp6.JLH`; AArch64: `x13`).
- `cloneAtH` has no label prefix (AArch64's `pfxM`).
-/
import Spike.Lib.X64HelloParent
import Spike.Lib.X64HelloMainPost
import Spike.Lib.X64HelloClonePreHOf
import Spike.Lib.Rt.X64Layout

namespace Spike.Lib.X64HelloCloneSegD

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Region Ctl)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (JS oP)
open Spike.Lib.X64.Flow.Worker.Hello.MainPost (mainX3)
open Spike.Lib.X64HelloPreA (cloneAtH)

/-- **The clone state's facts for `MainSegH`** (module doc; hello's `CloneSegH`).

Its inhabitant is the instance's: `X64HelloCloneSeg.cloneSegH_of_mid` (the twin of A64's) produces it from the
clone's mid state `X64HelloHMid.CloneMidH` (widening `wc_main`'s region by the caller's cells, the return address
`mainX3`'s from the saved frame), and `X64HelloH2Inv.seg2_of` reads it back at `h2`'s clone states. -/
def CloneSegD (L : RuntimeLayout) (endPc : Int64) (s : State) (c : Ctl) : Prop :=
  ∃ (Rm : Region) (F₂ : MachineData → Prop) (cA fp ra tp : BitVec 64),
    At L.exe endPc ⟨Rm.base, -128, 40⟩ F₂ ⟨cloneAtH L.exe, oP, JS c cA fp ra tp⟩ s c ∧
    (Rm.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 128 ∧ (⟨Rm.base, -128, 40⟩ : Region).OK ∧
    Rm.base.toNat % 16 = 0 ∧ Int64.ofBitVec ra = L.lab mainX3 ∧ s.st.1.regs.get64 .r15 = cA

end Spike.Lib.X64HelloCloneSegD
