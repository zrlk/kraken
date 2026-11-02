/-
**main's segment-end facts at `h2`'s clone states** (x86-64; the twin of `Spike/Lib/A64HelloSegEndX2.lean`'s live
part): `HelloSegEnd.hpc_ofR`'s `hseg` at `inv2 := X64HelloH2Inv.inv2H`. `X2H`'s clone clause carries
`X64HelloCloneSegD.CloneSegD`, which `X64HelloCloneSeg.CloneSegH` abbreviates.

- `hseg_X2`: `hpc_ofR`'s `hseg` at `inv2H`, any level, move, side and placement.

## Differences from the AArch64 version

- The fragments are over `isa` (AArch64: `isaLSE2`) and the pc is `Scc.Sem.X64.pcOf`.
- `cloneSegD_eq` (`CloneSegH = CloneSegD` by `rfl`) is not twinned: it is dead in hello, and on x86-64 `CloneSegH`
  is an `abbrev` of `CloneSegD`.
-/
import Spike.Lib.X64HelloCloneSeg
import Spike.Lib.X64HelloH2Inv

namespace Spike.Lib.X64HelloSegEndX2

open Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloPreA (clonePcH)
open Spike.Lib.X64HelloH2Inv (inv2H seg2_of)

/-- **`hpc_ofR`'s `hseg` at `inv2H`**: at a clone state of `h2`'s invariant, `CloneSegH` (`X2H`'s clone clause,
`X64HelloH2Inv.seg2_of`). -/
theorem hseg_X2 {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isa}
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame →
      Spike.Lib.MemSide isa}
    {L : RuntimeLayout} {a : Int64} {L0 : Spike.Lib.X64Consumer.Lbl} {ls0 : Spike.Lib.X64Consumer.Lsize} :
    ∀ l b n l' b' n' s c fs, inv2H W2 K ms2 L a L.endPc L0 ls0 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      Spike.Lib.X64HelloCloneSeg.CloneSegH L L.endPc s c :=
  fun _ _ _ _ _ _ _ _ _ hi hpc => seg2_of hi hpc

end Spike.Lib.X64HelloSegEndX2

/-- info: 'Spike.Lib.X64HelloSegEndX2.hseg_X2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSegEndX2.hseg_X2
