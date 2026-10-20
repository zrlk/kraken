/-
ISA-neutral erasure-WP rules with bounded reach (`EvTree.EraseWPR`) for the
event shapes of lock-based programs (the SWP spinlocks of both ISAs), at
`NPSafe`'s validity-free erasure (`T = fun _ => True`).

At `T = ⊤` the other threads' promise validity after a write (`HVal`) is
vacuous (`hval_trueT`), so the shapes keep only the resource-level
obligations of SLR's rules:

- `eraseWPR_store_pure`: a store whose location's release predicate is pure
  at the value (a counter's plain store; a lock's locking value): no slots;
  with the pending-promise branch of `eraseWPR_store_pend`.
- `eraseWPR_store_rel`: a release store (a lock's unlock): the thread splits
  off a resource `R` satisfying the location's release predicate at the
  message; the slots (`Erase.slotsFor`) carry it.
- `eraseWPR_rmw_pure`: an RMW writing a value at which the release predicate
  is pure (a lock's swap of `1`): it claims the update slots of the message
  it reads (`claimedSlots`), attaches none.
-/
import Kraken.Promising.SLR.NPSafeInvR
import Kraken.Promising.SLR.ReachRules
import Kraken.Promising.SLR.RmwPendR
import Kraken.Promising.SLR.TreeMap

namespace Kraken.Promising.SLR

variable {I : ISA}

section Shapes

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- At validity-free erasure, other threads' promise validity after a write
is not asked. -/
theorem hval_trueT {cx' : Ctx} {r' : Res} {g' : Ghost} : HVal rF (fun _ => True) c t tid cx' r' g' :=
  fun _ _ _ h => absurd trivial h

/-- **A store at which the release predicate is pure**: no slots, the write
set gains the message. The pending branch (`hp`) fulfils a prepaid promise. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_store_pure (hn : tid < c.threads.size) {k : StoreKind}
    {l : Loc} {v : Val} {ret : Bool → EvTree σ} (hpos : 0 < (r.wr l).q) (hpure : Pred.Pure (g.rel l) v)
    (hp : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∈ g.pend →
      (ret true).EraseWPR A tid iv rF (fun _ => True) c t Post r (unpend g tw) cx')
    (h : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∉ g.pend →
      (ret true).EraseWPR A tid iv rF (fun _ => True) c t Post (r.addW l (v, tw)) (storeGhost g l tw false [])
        cx') :
    (EvTree.store k false l v ret).EraseWPR A tid iv rF (fun _ => True) c t Post r g cx :=
  EvTree.eraseWPR_store_pend hn hp fun cx' tw hc hev hpd _ _ =>
    ⟨false, [], r.addW l (v, tw), hpos, fun h => absurd h (by decide), fun _ => ⟨rfl, hpure⟩,
      by simp [Res.op_unit], fun _ => rfl, hval_trueT, h cx' tw hc hev hpd⟩

/-- **A release store**: in the non-pending branch, the message is not an
outstanding promise of the thread (a fulfilled promised release is prepaid,
hence pending) and not claimed, and the thread splits `r ⊎ {msg}` into `r'`
and a resource `R` satisfying the release predicate at the message, which
the slots carry. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_store_rel (hn : tid < c.threads.size) {k : StoreKind}
    {l : Loc} {v : Val} {ret : Bool → EvTree σ} (hpos : 0 < (r.wr l).q)
    (hp : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∈ g.pend →
      (ret true).EraseWPR A tid iv rF (fun _ => True) c t Post r (unpend g tw) cx')
    (h : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∉ g.pend → ErAt rF (fun _ => True) c t tid r g cx →
      tw ∉ cx.prom ∧ ¬ g.Claimed (l, tw) ∧ ∃ (R r' : Res), (g.rel l).P v cx'.mem tw R ∧
        r'.op R = r.addW l (v, tw) ∧
        ∀ ss, SlotsFor g (total (setRes rF tid r) g c).acq l tw v cx'.mem ss → Res.prod (ss.map (·.res)) = R →
          (ret true).EraseWPR A tid iv rF (fun _ => True) c t Post r' (storeGhost g l tw true ss) cx') :
    (EvTree.store k false l v ret).EraseWPR A tid iv rF (fun _ => True) c t Post r g cx := by
  refine EvTree.eraseWPR_store_pend hn hp fun cx' tw hc hev hpd E _ => ?_
  obtain ⟨hnp, hcl, R, r', hR, hres, hk⟩ := h cx' tw hc hev hpd E
  obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hR
  rw [total_withThread] at hss
  exact ⟨true, ss, r', hpos, fun _ => ⟨hss, hcl⟩, fun h => absurd h (by decide), by rw [hprod, hres],
    fun h => absurd h hnp, hval_trueT, hk ss hss hprod⟩

/-- **An RMW writing a value at which the release predicate is pure**: it
claims the update slots of the message it reads and attaches none. The
obligations are those of `eraseWPR_rmw_pend` at `rel = false`, `ss = []`. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_rmw_pure (hn : tid < c.threads.size) {k : RmwKind}
    {noRet : Bool} {l : Loc} {op : Val → Option Val} {ret : Val → EvTree σ}
    (hfail : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      op x.2.1 = none → (ret x.2.1).EraseWPR A tid iv rF (fun _ => True) c t Post r g (fenceOptCtx A x.2.2))
    (hp : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → tw ∈ g.pend →
      (ret x.2.1).EraseWPR A tid iv rF (fun _ => True) c t Post r (unpend g tw) (rmwAfter A k noRet l cx'))
    (hok : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → tw ∉ g.pend →
      (∀ p ∈ x.2.2.prom, p ∈ g.pend → ∀ w, x.2.2.mem.get? p = some w → w.loc ≠ l) ∧ 0 < (r.wr l).q ∧
        Pred.Pure (g.rel l) new ∧
        (claimedSlots g l x.1 ≠ [] → x.1 ≤ (rmwAfter A k noRet l cx').views.wfloor) ∧
        (ret x.2.1).EraseWPR A tid iv rF (fun _ => True) c t Post
          ((r.op (Res.prod ((claimedSlots g l x.1).map (·.res)))).addW l (new, tw))
          (rmwGhost g l x.1 tw false []) (rmwAfter A k noRet l cx')) :
    (EvTree.rmw k noRet l op ret).EraseWPR A tid iv rF (fun _ => True) c t Post r g cx :=
  EvTree.eraseWPR_rmw_pend hn hfail hp fun x hx new hop cx' tw hc hev hpd _ => by
    obtain ⟨hnp, hpos, hpure, htr, hk⟩ := hok x hx new hop cx' tw hc hev hpd
    exact ⟨false, [], _, hnp, hpos, fun h => absurd h (by decide), fun _ => ⟨rfl, hpure⟩,
      by simp [Res.op_unit], fun _ => rfl, htr, hval_trueT, hk⟩

end Shapes

end Kraken.Promising.SLR
