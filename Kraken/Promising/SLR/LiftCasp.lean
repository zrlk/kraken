/-
`CASP` under the erasure WP.

`caspTree` (`AArch64.lean`) performs a `CASP` as two `rmw`s, one per half,
in either order (`rev`), with the outcome chosen up front (`succ`): the
success branch writes each half on its match, the failure branch only reads.
`EvTree.eraseWP_caspTree` composes two per-half rules into the WP of the
whole tree, for both orders and both outcomes. The rules are stated against
a joint state `S succ o₁ o₂ r g cx`, where `oᵢ = some old` records that half
`i` has run (and read `old`) and `none` that it has not; so a half's rule may
depend on whether the other half has already run. That is what a release
`CASPL` needs: its pair is published by the *last* of its two release
writes, so the rule of a half provides the release slots (`rel = true` in
`ErAt.rmw`'s preconditions) when the other half is done, and a pure write
(`rel = false`) when it is not. A protocol that needs the release on one
*fixed* half cannot be proved this way (the other order is explored too),
and falls back to option (iii) of §5.4 (treat the `CASPL` as two separately
specified RMWs with the pair invariant held in ghost state).

Each half's rule is discharged with `EvTree.eraseWP_caspHalf`
(`eraseWP_access`) and `EvTree.eraseWP_rmw` (its failure case covers the
reads of the failure branch and of a mismatching half).
-/
import Kraken.Promising.AArch64
import Kraken.Promising.SLR.LiftEvents

namespace Kraken.Promising.SLR

open Kraken.Promising.AArch64

variable {I : ISA} {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop}

/-- One half of `caspTree`: an `rmw` of kind `k` at `a` with operation `op` on
the half's width (`caspTree`'s local `half`). -/
def caspHalf (ds : Decls) (k : RmwKind) (a : BitVec 64) {w : MemWidth} (op : w.type → Option w.type)
    (r : w.type → EvTree σ) : EvTree σ :=
  .access ds a w.bytes fun l =>
    .rmw k false l (fun old => (op (old.setWidth w.bits)).map (·.setWidth 128)) fun old => r (old.setWidth w.bits)

/-- The operation of a `CASP` half on outcome `succ` (`caspTree`'s `op1`/`op2`):
compare-and-swap on success, read only on failure. -/
def caspOp {w : MemWidth} (succ : Fin 2) (cmp new : w.type) : w.type → Option w.type :=
  if succ.val == 1 then fun old => if old == cmp then some new else none else fun _ => none

/-- A half's WP is its `rmw`'s WP at every resolved location
(`EvTree.eraseWP_access`); the `rmw`'s is `EvTree.eraseWP_rmw`'s. -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_caspHalf {ds : Decls} {k : RmwKind} {a : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {cont : w.type → EvTree σ} {r : Res} {g : Ghost} {cx : Ctx}
    (h : ∀ l, (EvTree.rmw k false l (fun old => (op (old.setWidth w.bits)).map (·.setWidth 128))
      fun old => cont (old.setWidth w.bits)).EraseWP A tid iv rF T c t Post r g cx) :
    (caspHalf ds k a op cont).EraseWP A tid iv rF T c t Post r g cx :=
  EvTree.eraseWP_access h

private theorem eraseWP_guard {b : Bool} {tr : EvTree σ} {r : Res} {g : Ghost} {cx : Ctx}
    (h : b = true → tr.EraseWP A tid iv rF T c t Post r g cx) :
    (if b then tr else EvTree.choose 0 nofun).EraseWP A tid iv rF T c t Post r g cx := by
  cases b
  · intro i; exact i.elim0
  · exact h rfl

/-- **`CASP` keeps erasure**, from two per-half rules over a joint state `S`
(`S succ o₁ o₂`: half `i` has run iff `oᵢ = some _`). Each rule runs its
half from a state where it has not run, whatever the other half's flag, so
both orders (`rev`) are covered; `hfin` closes with both halves run and the
outcome's guard (`o₁ = cmp₁ ∧ o₂ = cmp₂` iff `succ = 1`). A rule may depend
on the other half's flag: e.g. a release `CASPL` provides its slots in the
half that runs last (module docstring). -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_caspTree {ds : Decls} {k : RmwKind} {addr : BitVec 64}
    {w : MemWidth} {cmp1 cmp2 new1 new2 : w.type} {ret : w.type → w.type → EvTree σ}
    (S : Fin 2 → Option w.type → Option w.type → Res → Ghost → Ctx → Prop) {r : Res} {g : Ghost} {cx : Ctx}
    (hstart : ∀ succ, S succ none none r g cx)
    (hh1 : ∀ succ o2 r g cx (cont : w.type → EvTree σ), S succ none o2 r g cx →
      (∀ o1 r' g' cx', S succ (some o1) o2 r' g' cx' → (cont o1).EraseWP A tid iv rF T c t Post r' g' cx') →
      (caspHalf ds k addr (caspOp succ cmp1 new1) cont).EraseWP A tid iv rF T c t Post r g cx)
    (hh2 : ∀ succ o1 r g cx (cont : w.type → EvTree σ), S succ o1 none r g cx →
      (∀ o2 r' g' cx', S succ o1 (some o2) r' g' cx' → (cont o2).EraseWP A tid iv rF T c t Post r' g' cx') →
      (caspHalf ds k (addr + w.bytesv) (caspOp succ cmp2 new2) cont).EraseWP A tid iv rF T c t Post r g cx)
    (hfin : ∀ succ o1 o2 r g cx, S succ (some o1) (some o2) r g cx →
      ((o1 == cmp1 && o2 == cmp2) == (succ.val == 1)) = true → (ret o1 o2).EraseWP A tid iv rF T c t Post r g cx) :
    (caspTree ds k addr cmp1 cmp2 new1 new2 ret).EraseWP A tid iv rF T c t Post r g cx := by
  intro succ rev
  change (if rev.val == 0 then
      caspHalf ds k addr (caspOp succ cmp1 new1) fun o1 => caspHalf ds k (addr + w.bytesv) (caspOp succ cmp2 new2)
        fun o2 => if ((o1 == cmp1 && o2 == cmp2) == (succ.val == 1)) then ret o1 o2 else EvTree.choose 0 nofun
    else
      caspHalf ds k (addr + w.bytesv) (caspOp succ cmp2 new2) fun o2 => caspHalf ds k addr (caspOp succ cmp1 new1)
        fun o1 => if ((o1 == cmp1 && o2 == cmp2) == (succ.val == 1)) then ret o1 o2 else EvTree.choose 0 nofun
    ).EraseWP A tid iv rF T c t Post r g cx
  split
  · refine hh1 succ none r g cx _ (hstart succ) fun o1 r₁ g₁ cx₁ h₁ => ?_
    refine hh2 succ (some o1) r₁ g₁ cx₁ _ h₁ fun o2 r₂ g₂ cx₂ h₂ => ?_
    exact eraseWP_guard (hfin succ o1 o2 r₂ g₂ cx₂ h₂)
  · refine hh2 succ none r g cx _ (hstart succ) fun o2 r₁ g₁ cx₁ h₁ => ?_
    refine hh1 succ (some o2) r₁ g₁ cx₁ _ h₁ fun o1 r₂ g₂ cx₂ h₂ => ?_
    exact eraseWP_guard (hfin succ o1 o2 r₂ g₂ cx₂ h₂)

end Kraken.Promising.SLR
