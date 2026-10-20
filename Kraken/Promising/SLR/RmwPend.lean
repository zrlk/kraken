/-
The RMW rule with own pending promises to the RMW's location.

`EvTree.eraseWP_rmw_pend` (`SLR/Escrow.lean`) allows pending promises of the
thread to *other* locations only (`Erase.not_claimed_loc`'s `hnp`). A
spinlock's `SWPA` on the lock `L`, run while the thread's prepaid `STLR` to
`L` is pending (the virtual thread stopped before the `STLR`, the real one
is still in or before the critical section), fails it. What uniqueness of
claims really needs is that no pending promise of the thread is the
*claimer* of the message the RMW reads: a prepaid plain release store makes
no claim.

## Contents

- `Erase.not_claimed_noclaim`: `Erase.not_claimed_loc` with `hnp` weakened to
  "no pending promise of the thread claims `(x, tr)`".
- `ErAt.rmw_pendOk`: `ErAt.rmw_loc` with the same weakening.
- `EvTree.eraseWP_rmw_pend'`: `EvTree.eraseWP_rmw_pend` with the same
  weakening of `hok`'s first conjunct.
-/
import Kraken.Promising.SLR.Escrow

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `Escrow.lean`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

section Fulfil

variable {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I} {tid : Nat} {r : Res} {g : Ghost}
  {cx cx' : Ctx}

/-- **Uniqueness of claims, with own pending promises.** `Erase.not_claimed`
with `hnp` weakened to "no pending promise of the thread is the claimer of
`(x, tr)`": a claimer of `(x, tr)` that is not one of the thread's
outstanding promises is settled before the RMW and excluded by `OwnSeen`; one
that is an outstanding promise is pending (claims are settled) and excluded
by the hypothesis. -/
theorem Erase.not_claimed_noclaim {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {t t' : Thread I} {mem' : Memory} {x : Loc} {tr tw : Time} {w : Msg}
    (ht : c.threads[tid]? = some t) (hw : WriteAt c tid t t' mem' tw w) (hl : w.loc = x)
    (htr : tr < tw) {old : Val} (hrd : c.mem.read? x tr = some old) (hat : c.mem.atomic x tid tr tw = true)
    (hnp : ∀ p ∈ t.prom, p ∈ g.pend → ((x, tr), p) ∉ g.claims)
    (hseen : OwnSeen c tid t x tr) : ¬ g.Claimed (x, tr) := by
  intro hc
  obtain ⟨⟨k, tw'⟩, hk, hk1⟩ := List.mem_map.mp hc
  simp only at hk1
  subst hk1
  obtain ⟨hlt, w'', hw'', hl'', hs, hb⟩ := E.claimsAt _ tw' hk
  simp only at hlt hl'' hb
  have hj : w''.tid = tid := by
    rcases Nat.lt_trichotomy tw' tw with h | h | h
    · exact atomic_between hat hrd hlt h hw'' hl''
    · subst h
      rcases hw.cases with ⟨-, -, hg⟩ | ⟨-, rfl⟩
      · rw [hg] at hw''
        cases hw''
        exact hw.tid
      · have := c.mem.last_le_of_get?_eq_some hw''; omega_t
    · rcases hw.cases with ⟨-, -, hg⟩ | ⟨-, rfl⟩
      · rw [← hb tw w htr h hg hl]; exact hw.tid
      · have := c.mem.last_le_of_get?_eq_some hw''; omega_t
  by_cases hp : tw' ∈ t.prom
  · rcases hs with hs | hs
    · exact hs ⟨tid, t, ht, hp⟩
    · exact hnp tw' hp hs hk
  · have := hseen tw' w'' hw'' hl'' hj hp
    omega_t

/-- **The RMW obligation of the erasure WP with own pending promises**
(context level): `ErAt.rmw_loc` with `hnp` weakened to "no pending promise of
the thread claims `(l, tr)`". -/
theorem ErAt.rmw_pendOk (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size) (hi : cx.Inv tid)
    {l : Loc} {new old : Val} {tr tw : Time} (hev : WriteEv tid cx cx' l new (some tr) tw)
    (hrd : cx.mem.read? l tr = some old)
    (hseen : ∀ ts w, cx.mem.get? ts = some w → w.loc = l → w.tid = tid → ts ∉ cx.prom → ts ≤ tr)
    (hnp : ∀ p ∈ cx.prom, p ∈ g.pend → ((l, tr), p) ∉ g.claims) (hpend : tw ∉ g.pend)
    (hpos : 0 < (r.wr l).q) {rel : Bool} {ss : List Slot}
    (hrel : rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw new cx'.mem ss ∧ ¬ g.Claimed (l, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel l) new)
    {r' : Res} (hres : r'.op (Res.prod (ss.map (·.res))) =
      (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (new, tw))
    (hval : HVal rF T c t tid cx' r' (rmwGhost g l tr tw rel ss)) :
    ErAt rF T c t tid r' (rmwGhost g l tr tw rel ss) cx' := by
  obtain ⟨htr, hat⟩ := hev.tr tr rfl
  have hW := hev.writeAt (c := c) (t := t) hi
  have hun := Erase.not_claimed_noclaim E (ErAt.get? hn) hW rfl htr hrd hat hnp hseen
  have E' := Erase.rmw E (ErAt.get? hn) hW htr hrd hat hpend hun
    (by rw [setRes_self]; exact hpos) (by rw [total_withThread]; exact hrel) hrlx (r' := r')
    (by rw [setRes_self]; exact hres) (by rw [setRes_setRes, Config.withThread_withThread]; exact hval)
  unfold ErAt
  rw [setRes_setRes, Config.withThread_withThread] at E'
  exact E'

end Fulfil

section Shapes

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- **An RMW, with own pending promises to its location**:
`EvTree.eraseWP_rmw_pend` with `hok`'s first conjunct weakened to "no
pending promise of the thread claims the message read". A successful RMW
whose write fulfils a pending promise needs only the continuation's WP; a
failed RMW only reads. -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_rmw_pend' (hn : tid < c.threads.size) {k : RmwKind}
    {noRet : Bool} {l : Loc} {op : Val → Option Val} {ret : Val → EvTree σ}
    (hfail : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      op x.2.1 = none → (ret x.2.1).EraseWP A tid iv rF T c t Post r g (fenceOptCtx A x.2.2))
    (hp : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → tw ∈ g.pend →
      (ret x.2.1).EraseWP A tid iv rF T c t Post r (unpend g tw) (rmwAfter A k noRet l cx'))
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
        HVal rF T c t tid cx' r' (rmwGhost g l x.1 tw rel ss) ∧
        (ret x.2.1).EraseWP A tid iv rF T c t Post r' (rmwGhost g l x.1 tw rel ss) (rmwAfter A k noRet l cx')) :
    (EvTree.rmw k noRet l op ret).EraseWP A tid iv rF T c t Post r g cx := by
  intro x hx
  refine ⟨hfail x hx, fun new hop cx' hc E hi => ?_⟩
  obtain ⟨tw, hev, hrd, hseen⟩ := rmw_event A tid iv hx hi hc
  have hi2 := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
  by_cases hpd : tw ∈ g.pend
  · exact ⟨r, _, ErAt.fulfilPend E hn hi2 hev hpd, hp x hx new hop cx' tw hc hev hpd⟩
  · obtain ⟨rel, ss, r', hnp, hpos, hrel, hrlx, hres, hval, hwp⟩ := hok x hx new hop cx' tw hc hev hpd E
    exact ⟨r', _, ErAt.rmw_pendOk E hn hi2 hev hrd hseen hnp hpd hpos hrel hrlx hres hval, hwp⟩

end Shapes

end Kraken.Promising.SLR
