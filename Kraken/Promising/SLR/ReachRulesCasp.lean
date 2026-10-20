/-
The `CASP` node shapes of the erasure WP with bounded reach
(`EvTree.EraseWPR`, `SLR/ReachRules.lean`), moved out of `ReachRules.lean`
so that `ReachRules` does not import the AArch64 ISA (`SLR/LiftCasp.lean`
imports `Kraken.Promising.AArch64` for `caspTree`, and the AArch64 and x64
syntax modules cannot be imported together). A pure move.

## Contents

- `EvTree.eraseWPR_caspHalf`: a `CASP` half, its `rmw`'s WP at every
  resolved location.
- `EvTree.eraseWPR_caspTree`: `EvTree.eraseWP_caspTree` for
  `EvTree.EraseWPR`.
-/
import Kraken.Promising.SLR.ReachRules
import Kraken.Promising.SLR.LiftCasp

namespace Kraken.Promising.SLR

open Kraken.Promising.AArch64

variable {I : ISA}

section Shapes

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- A `CASP` half: its `rmw`'s WP at every resolved location. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_caspHalf {ds : Decls} {k : RmwKind} {a : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {cont : w.type → EvTree σ}
    (h : ∀ l, (EvTree.rmw k false l (fun old => (op (old.setWidth w.bits)).map (·.setWidth 128))
      fun old => cont (old.setWidth w.bits)).EraseWPR A tid iv rF T c t Post r g cx) :
    (caspHalf ds k a op cont).EraseWPR A tid iv rF T c t Post r g cx :=
  EvTree.eraseWPR_access h

private theorem eraseWPR_guard {b : Bool} {tr : EvTree σ} {r : Res} {g : Ghost} {cx : Ctx}
    (h : b = true → tr.EraseWPR A tid iv rF T c t Post r g cx) :
    (if b then tr else EvTree.choose 0 nofun).EraseWPR A tid iv rF T c t Post r g cx := by
  cases b
  · intro i; exact i.elim0
  · exact h rfl

/-- **`CASP` with bounded reach**: `EvTree.eraseWP_caspTree` for
`EvTree.EraseWPR`. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_caspTree {ds : Decls} {k : RmwKind} {addr : BitVec 64}
    {w : MemWidth} {cmp1 cmp2 new1 new2 : w.type} {ret : w.type → w.type → EvTree σ}
    (S : Fin 2 → Option w.type → Option w.type → Res → Ghost → Ctx → Prop)
    (hstart : ∀ succ, S succ none none r g cx)
    (hh1 : ∀ succ o2 r g cx (cont : w.type → EvTree σ), S succ none o2 r g cx →
      (∀ o1 r' g' cx', S succ (some o1) o2 r' g' cx' → (cont o1).EraseWPR A tid iv rF T c t Post r' g' cx') →
      (caspHalf ds k addr (caspOp succ cmp1 new1) cont).EraseWPR A tid iv rF T c t Post r g cx)
    (hh2 : ∀ succ o1 r g cx (cont : w.type → EvTree σ), S succ o1 none r g cx →
      (∀ o2 r' g' cx', S succ o1 (some o2) r' g' cx' → (cont o2).EraseWPR A tid iv rF T c t Post r' g' cx') →
      (caspHalf ds k (addr + w.bytesv) (caspOp succ cmp2 new2) cont).EraseWPR A tid iv rF T c t Post r g cx)
    (hfin : ∀ succ o1 o2 r g cx, S succ (some o1) (some o2) r g cx →
      ((o1 == cmp1 && o2 == cmp2) == (succ.val == 1)) = true → (ret o1 o2).EraseWPR A tid iv rF T c t Post r g cx) :
    (caspTree ds k addr cmp1 cmp2 new1 new2 ret).EraseWPR A tid iv rF T c t Post r g cx := by
  intro succ rev
  change (if rev.val == 0 then
      caspHalf ds k addr (caspOp succ cmp1 new1) fun o1 => caspHalf ds k (addr + w.bytesv) (caspOp succ cmp2 new2)
        fun o2 => if ((o1 == cmp1 && o2 == cmp2) == (succ.val == 1)) then ret o1 o2 else EvTree.choose 0 nofun
    else
      caspHalf ds k (addr + w.bytesv) (caspOp succ cmp2 new2) fun o2 => caspHalf ds k addr (caspOp succ cmp1 new1)
        fun o1 => if ((o1 == cmp1 && o2 == cmp2) == (succ.val == 1)) then ret o1 o2 else EvTree.choose 0 nofun
    ).EraseWPR A tid iv rF T c t Post r g cx
  split
  · refine hh1 succ none r g cx _ (hstart succ) fun o1 r₁ g₁ cx₁ h₁ => ?_
    refine hh2 succ (some o1) r₁ g₁ cx₁ _ h₁ fun o2 r₂ g₂ cx₂ h₂ => ?_
    exact eraseWPR_guard (hfin succ o1 o2 r₂ g₂ cx₂ h₂)
  · refine hh2 succ none r g cx _ (hstart succ) fun o2 r₁ g₁ cx₁ h₁ => ?_
    refine hh1 succ (some o2) r₁ g₁ cx₁ _ h₁ fun o1 r₂ g₂ cx₂ h₂ => ?_
    exact eraseWPR_guard (hfin succ o1 o2 r₂ g₂ cx₂ h₂)

end Shapes

end Kraken.Promising.SLR
