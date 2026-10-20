/-
The `CASP` node shape of fallback (iii), the prepaid release
(`SLR/Escrow.lean`), moved out of `Escrow.lean` so that `Escrow` does not
import the AArch64 ISA (`SLR/LiftCasp.lean` imports `Kraken.Promising.AArch64`
for `caspTree`, and the AArch64 and x64 syntax modules cannot be imported
together). A pure move.

## Contents

- `EvTree.eraseWP_caspHalf_pend`: a `CASP` half with pending promises.
-/
import Kraken.Promising.SLR.Escrow
import Kraken.Promising.SLR.LiftCasp

namespace Kraken.Promising.SLR

open Kraken.Promising.AArch64

variable {I : ISA}

section Shapes

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- A `CASP` half with pending promises: `EvTree.eraseWP_caspHalf` with the
half's `rmw` discharged by `EvTree.eraseWP_rmw_pend`. With
`EvTree.eraseWP_caspTree` this gives the WP of a prepaid `CASPL` in both
orders: the prepaid release half's write takes the pending branch, the other
half (fresh or fulfilling a non-pending promise) the rule branch. -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_caspHalf_pend {ds : Decls} {k : RmwKind}
    {a : BitVec 64} {w : MemWidth} {op : w.type → Option w.type} {cont : w.type → EvTree σ}
    (h : ∀ l, (EvTree.rmw k false l (fun old => (op (old.setWidth w.bits)).map (·.setWidth 128))
      fun old => cont (old.setWidth w.bits)).EraseWP A tid iv rF T c t Post r g cx) :
    (caspHalf ds k a op cont).EraseWP A tid iv rF T c t Post r g cx :=
  EvTree.eraseWP_caspHalf h

end Shapes

end Kraken.Promising.SLR
