/-
**The clone state's facts for main's segment end, as `h2`'s fence states them** (AArch64): `CloneSegD`, the body of
`HelloCloneSeg.CloneSegH`, stated where `HelloH2Inv.X2H` can
import it (`A64HelloCloneSeg` imports `A64HelloH2Inv` through `RootHP`). The two are the same predicate (`rfl`,
checked in `A64HelloSegEndX2`), so `cloneSegH_of_mid` produces `X2H`'s clone conjunct and
`HelloSegEnd.hpc_ofR`'s `hseg` reads it back.

- `CloneSegD`: `At` of the clone's node with `JS` in the widened region `⟨Rm.base, -144, 48⟩`, its base 144 above
  `sp`, the region not wrapping, the base 16-aligned, the return address `mainSp1`'s, `x13` the cell.
-/
import Spike.Lib.A64HelloParent
import Spike.Lib.A64HelloMainPost
import Spike.Lib.A64HelloClonePreHOf
import Spike.Lib.Rt.A64Layout

namespace Spike.Lib.HelloCloneSegD

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Region Ctl)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (At)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Hello.MainPost (mainSp1)
open Spike.Lib.HelloPreA (cloneAtH pfxM)

/-- **The clone state's facts for `MainSegH`** (module doc; `HelloCloneSeg.CloneSegH`). -/
def CloneSegD (L : RuntimeLayout) (endPc : Int64) (s : State) (c : Ctl) : Prop :=
  ∃ (Rm : Region) (F₂ : MachineData → Prop) (cA x29 ra tp : BitVec 64),
    At L.exe endPc ⟨Rm.base, -144, 48⟩ F₂ ⟨cloneAtH pfxM L.exe, oP, JS c cA x29 ra tp⟩ s c ∧
    (Rm.base.toNat : Int) = s.st.1.regs.SP.toNat + 144 ∧ (⟨Rm.base, -144, 48⟩ : Region).OK ∧
    Rm.base.toNat % 16 = 0 ∧ Int64.ofBitVec ra = L.lab mainSp1 ∧ s.st.1.regs.X13.toBitVec = cA

end Spike.Lib.HelloCloneSegD
