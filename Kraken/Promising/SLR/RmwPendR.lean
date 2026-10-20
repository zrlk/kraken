/-
The RMW rule with own pending promises to the RMW's location, in the
bounded-reach form `EvTree.EraseWPR`.

`EvTree.eraseWPR_rmw_pend` (`SLR/ReachRules.lean`) allows pending promises of
the thread to *other* locations only; `EvTree.eraseWP_rmw_pend'`
(`SLR/RmwPend.lean`) weakens that, for `EvTree.EraseWP`, to "no pending
promise of the thread claims the message the RMW reads" (a spinlock's `SWPA`
on the lock while the thread's prepaid `STLR` to it is pending). This file
combines the two.

## Contents

- `EvTree.eraseWPR_rmw_pend'`: `EvTree.eraseWPR_rmw_pend` with `hok`'s first
  conjunct weakened as in `EvTree.eraseWP_rmw_pend'`. The `ErAt`-level
  helper is `ErAt.rmw_pendOk` (`SLR/RmwPend.lean`); the bounded-reach
  obligation is discharged by `RStep.rmw`/`RStep.unpend` exactly as in
  `EvTree.eraseWPR_rmw_pend`.
-/
import Kraken.Promising.SLR.RmwPend
import Kraken.Promising.SLR.ReachRules

namespace Kraken.Promising.SLR

variable {I : ISA}

section Shapes

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- **An RMW, with own pending promises to its location, with bounded
reach**: `EvTree.eraseWPR_rmw_pend` with `hok`'s first conjunct weakened to
"no pending promise of the thread claims the message read"
(`EvTree.eraseWP_rmw_pend'`). A successful RMW whose write fulfils a pending
promise needs only the continuation's WP (`RStep.unpend`); a failed RMW only
reads. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_rmw_pend' (hn : tid < c.threads.size) {k : RmwKind}
    {noRet : Bool} {l : Loc} {op : Val → Option Val} {ret : Val → EvTree σ}
    (hfail : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      op x.2.1 = none → (ret x.2.1).EraseWPR A tid iv rF T c t Post r g (fenceOptCtx A x.2.2))
    (hp : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → tw ∈ g.pend →
      (ret x.2.1).EraseWPR A tid iv rF T c t Post r (unpend g tw) (rmwAfter A k noRet l cx'))
    (hok : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → tw ∉ g.pend → ErAt rF T c t tid r g x.2.2 →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res),
        (∀ p ∈ x.2.2.prom, p ∈ g.pend → ((l, x.1), p) ∉ g.claims) ∧ 0 < (r.wr l).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw new cx'.mem ss ∧ ¬ g.Claimed (l, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel l) new) ∧
        r'.op (Res.prod (ss.map (·.res))) =
          (r.op (Res.prod ((claimedSlots g l x.1).map (·.res)))).addW l (new, tw) ∧
        (tw ∈ x.2.2.prom → ss = []) ∧
        (claimedSlots g l x.1 ≠ [] → x.1 ≤ (rmwAfter A k noRet l cx').views.wfloor) ∧
        HVal rF T c t tid cx' r' (rmwGhost g l x.1 tw rel ss) ∧
        (ret x.2.1).EraseWPR A tid iv rF T c t Post r' (rmwGhost g l x.1 tw rel ss) (rmwAfter A k noRet l cx')) :
    (EvTree.rmw k noRet l op ret).EraseWPR A tid iv rF T c t Post r g cx := by
  intro x hx
  refine ⟨hfail x hx, fun new hop cx' hc E hi hm => ?_⟩
  obtain ⟨tw, hev, hrd, hseen⟩ := rmw_event A tid iv hx hi hc
  have hi2 := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
  by_cases hpd : tw ∈ g.pend
  · exact ⟨r, _, ErAt.fulfilPend E hn hi2 hev hpd, RStep.unpend tw _, hp x hx new hop cx' tw hc hev hpd⟩
  · obtain ⟨hm1, -⟩ := fenceOptCtx_memProm A cx
    obtain ⟨hm2, -⟩ := readSuccs_memProm A iv hx
    have hm' : c.mem.last ≤ x.2.2.mem.last := by rw [hm2, hm1]; exact hm
    obtain ⟨rel, ss, r', hnp, hpos, hrel, hrlx, hres, hf, htr, hval, hwp⟩ := hok x hx new hop cx' tw hc hev hpd E
    exact ⟨r', _, ErAt.rmw_pendOk E hn hi2 hev hrd hseen hnp hpd hpos hrel hrlx hres hval,
      RStep.rmw (hev.freshSlots hm' (slots_key hrel hrlx) hf) hres htr, hwp⟩

end Shapes

end Kraken.Promising.SLR
