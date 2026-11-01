/-
**main's segment-end facts at `h2`'s clone states** (AArch64):
`HelloSegEnd.hpc_ofR`'s `hseg` at `inv2 := HelloH2Inv.inv2H`. `X2H`'s clone clause carries
`HelloCloneSegD.CloneSegD` (filled at the root by `HelloCloneSeg.cloneSegH_of_mid` in
`H2Root.h2Stmt_root`, through `HelloH2CP.hCP_of`'s `hSeg`), and `CloneSegD` is `CloneSegH` (`rfl`).

- `cloneSegD_eq`: `CloneSegH = CloneSegD`.
- `hseg_X2`: `hpc_ofR`'s `hseg` at `inv2H`, any level, move, side and placement.
-/
import Spike.Lib.A64HelloCloneSeg
import Spike.Lib.A64HelloH2Inv

namespace Spike.Lib.HelloSegEndX2

open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.HelloPreA (clonePcH)
open Spike.Lib.HelloH2Inv (inv2H seg2_of)

/-- **`CloneSegH` is `h2`'s fence conjunct `CloneSegD`** (the same body). -/
theorem cloneSegD_eq : Spike.Lib.HelloCloneSeg.CloneSegH = Spike.Lib.HelloCloneSegD.CloneSegD := rfl

/-- **`hpc_ofR`'s `hseg` at `inv2H`**: at a clone state of `h2`'s invariant, `CloneSegH` (`X2H`'s clone clause,
`HelloH2Inv.seg2_of`). -/
theorem hseg_X2 {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isaLSE2}
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame →
      Spike.Lib.MemSide isaLSE2}
    {L : RuntimeLayout} {a : Int64} {L0 : Spike.Lib.A64Consumer.Lbl} {ls0 : Spike.Lib.A64Consumer.Lsize} :
    ∀ l b n l' b' n' s c fs, inv2H W2 K ms2 L a L.endPc L0 ls0 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      Spike.Lib.HelloCloneSeg.CloneSegH L L.endPc s c :=
  fun _ _ _ _ _ _ _ _ _ hi hpc => seg2_of hi hpc

end Spike.Lib.HelloSegEndX2

/-- info: 'Spike.Lib.HelloSegEndX2.hseg_X2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegEndX2.hseg_X2
