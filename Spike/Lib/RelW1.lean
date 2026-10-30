/-
**Release-only single writers** (code fact for `Spike/Lib/CertReplay.lean`):
an instruction's event tree with at most one write on each path, a release
write.

`EvTree.NoW e`: no path of `e` writes (no `store`, no `rmw` node).
`EvTree.RelW1 A e`: on each path of `e` there is at most one write, and it is a
release write under the profile `A` (a `store` of effective kind `.rel`, e.g.
AArch64 `STLR`, or an `rmw` whose write has effective kind `.rel`: a `rel` or
`acqRel` RMW, e.g. `SWPAL`/`LDADDAL`/`CASAL`); after it the path does not
write again.

Why it matters (`CertReplay`): a release write's pre-view takes `vwOld`, and
every write raises `vwOld` to its timestamp. Once such a thread has written at
a fresh timestamp (above every message, so above every outstanding promise),
none of its outstanding promises can be fulfilled any more. With one write per
instruction, an instruction that appends fulfils nothing, so a certification
run that empties the promise set does so before its first append, with memory
unchanged.
-/
import Kraken.Promising.Basic

namespace Kraken.Promising.EvTree

/-- **No path of the tree writes**: no `store` and no `rmw` node. -/
inductive NoW {σ : Type} : EvTree σ → Prop
  | done (s : σ) : NoW (.done s)
  | fault (m : String) : NoW (.fault m)
  | choose {n : Nat} {k : Fin n → EvTree σ} : (∀ i, NoW (k i)) → NoW (.choose n k)
  | load {k : LoadKind} {xcl : Bool} {l : Loc} {ret : Val → EvTree σ} : (∀ v, NoW (ret v)) →
      NoW (.load k xcl l ret)
  | fence {k : FenceKind} {ret : Unit → EvTree σ} : (∀ u, NoW (ret u)) → NoW (.fence k ret)

/-- **At most one write on each path, a release write** under the profile
`A`: a `store` of effective kind `.rel`, or an `rmw` whose write has effective
kind `.rel` (a `rel` or `acqRel` RMW), with no write after it. -/
inductive RelW1 (A : Arch) {σ : Type} : EvTree σ → Prop
  | noW {e : EvTree σ} : NoW e → RelW1 A e
  | choose {n : Nat} {k : Fin n → EvTree σ} : (∀ i, RelW1 A (k i)) → RelW1 A (.choose n k)
  | load {k : LoadKind} {xcl : Bool} {l : Loc} {ret : Val → EvTree σ} : (∀ v, RelW1 A (ret v)) →
      RelW1 A (.load k xcl l ret)
  | fence {k : FenceKind} {ret : Unit → EvTree σ} : (∀ u, RelW1 A (ret u)) → RelW1 A (.fence k ret)
  | store {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {ret : Bool → EvTree σ} :
      A.storeKind k = .rel → (∀ b, NoW (ret b)) → RelW1 A (.store k xcl l v ret)
  | rmw {k : RmwKind} {noRet : Bool} {l : Loc} {op : Val → Option Val} {ret : Val → EvTree σ} :
      A.storeKind (A.rmwKind k).storeKind = .rel → (∀ v, NoW (ret v)) → RelW1 A (.rmw k noRet l op ret)

/-- `NoW` is kept by `map`. -/
theorem NoW.map {σ τ : Type} (f : σ → τ) {e : EvTree σ} (h : NoW e) : NoW (e.map f) := by
  induction h with
  | done s => exact .done _
  | fault m => exact .fault m
  | choose _ ih => exact .choose ih
  | load _ ih => exact .load ih
  | fence _ ih => exact .fence ih

/-- `RelW1` is kept by `map`. -/
theorem RelW1.map {A : Arch} {σ τ : Type} (f : σ → τ) {e : EvTree σ} (h : RelW1 A e) :
    RelW1 A (e.map f) := by
  induction h with
  | noW h => exact .noW (h.map f)
  | choose _ ih => exact .choose ih
  | load _ ih => exact .load ih
  | fence _ ih => exact .fence ih
  | store hk h => exact .store hk fun b => (h b).map f
  | rmw hk h => exact .rmw hk fun v => (h v).map f

/-- An `acqRel` RMW on armv8 writes with release kind (`SWPAL`, `LDADDAL`). -/
theorem storeKind_rmw_acqRel_armv8 : Arch.armv8.storeKind (Arch.armv8.rmwKind .acqRel).storeKind = .rel := rfl

/-- A release store on armv8 has release kind (`STLR`). -/
theorem storeKind_rel_armv8 : Arch.armv8.storeKind .rel = .rel := rfl

end Kraken.Promising.EvTree
