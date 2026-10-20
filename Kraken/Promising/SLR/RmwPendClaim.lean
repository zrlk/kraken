/-
An RMW whose write fulfils the thread's own **pending** promise while its
read part **claims** the message read, in the bounded-reach form
`EvTree.EraseWPR` at `NPSafe`'s validity-free erasure (`T = ⊤`).

`EvTree.eraseWPR_rmw_pend'` (`SLR/RmwPendR.lean`) treats a successful RMW
whose write is a pending (prepaid) promise as a plain fulfilment: resource
unchanged, only `pend` shrinks. The read part then claims nothing, so an RMW
that acquires a lock (x64 `xchgl` under TSO: a release write, so it may be
promised and prepaid) gets no slot. Here the pending branch claims as a
non-pending RMW does: the update slots of the message read move to the
thread, the claim is recorded (`rmwGhost … false []`: no release slots,
the prepaid message keeps its mode). The promise is fulfilled first
(`unpend`), then the claim is recorded: claimers are performed writes
(`Erase.claimFulf`).

## Contents

- `Perm.addW_of_mem`, `Res.addW_of_mem`: adding a present write is a no-op.
- `Erase.claimPend`: the ghost step "claim `(x, tr)` by the performed
  (no longer outstanding) message `tw`" preserves erasure (no memory or
  thread change; `T = ⊤`).
- `ErAt.not_outstanding_fulfilled`: after a write event fulfilling `tw`, no
  thread holds `tw`.
- `EvTree.eraseWPR_rmw_pendClaim`: `eraseWPR_rmw_pend'` at `T = ⊤` with the
  claiming pending branch; both branches also receive the value read
  (`read?`) and the message read's unclaimedness (no promise of the thread
  is a claimer, `Erase.claimFulf`).
-/
import Kraken.Promising.SLR.RmwPendR
import Kraken.Promising.SLR.RuleShapes

namespace Kraken.Promising.SLR

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- Adding a write already in the write set changes nothing. -/
theorem Perm.addW_of_mem {a : Perm} {p : Val × Time} (h : a.X p) : a.addW p = a := by
  cases a with
  | mk q X nn z =>
    simp only [Perm.addW, Perm.mk.injEq, true_and]
    funext p'
    apply propext
    constructor
    · rintro (h' | ⟨-, rfl⟩)
      · exact h'
      · exact h
    · exact .inl

/-- Adding a write already in the write set changes nothing. -/
theorem Res.addW_of_mem {r : Res} {x : Loc} {p : Val × Time} (h : (r.wr x).X p) : r.addW x p = r := by
  apply Res.ext
  · funext y
    simp only [Res.addW]
    split
    · next hy => subst hy; exact Perm.addW_of_mem h
    · rfl
  · rfl

section Claim

variable {rF : Nat → Res} {g : Ghost} {c : Config I} {tid : Nat}

/-- **Claiming by a performed message**: erasure survives moving the update
slots of `(x, tr)` to thread `tid` and recording the claim by the message
`tw`, no longer an outstanding promise (a message of `x` above `tr`, with
only messages of its own thread between, and `(x, tr)` unclaimed). The
thread's write set of `x` "gains" `(v, tw)`, which the written message
already contributes. -/
theorem Erase.claimPend (E : Erase rF g (fun _ => True) c) (hn : tid < c.threads.size) {x : Loc}
    {tr tw : Time} {w : Msg} (htr : tr < tw) (hw : c.mem.get? tw = some w) (hl : w.loc = x)
    (hpd : ¬ Outstanding c tw)
    (hb : ∀ ts w', tr < ts → ts < tw → c.mem.get? ts = some w' → w'.loc = x → w'.tid = w.tid)
    (hun : ¬ g.Claimed (x, tr)) (hpos : 0 < ((rF tid).wr x).q) :
    Erase (setRes rF tid (((rF tid).op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x (w.val, tw)))
      (rmwGhost g x tr tw false []) (fun _ => True) c := by
  have ht : c.threads[tid]? = some c.threads[tid] := Array.getElem?_eq_getElem hn
  have hposT : 0 < ((total rF g c).wr x).q := by
    unfold total threadsRes
    exact Res.pos_op.mpr (.inl (Res.pos_prod_of_mem (List.mem_map.mpr ⟨tid, List.mem_range.mpr hn, rfl⟩) hpos))
  have hX : ((total rF g c).wr x).X (w.val, tw) :=
    (E.writes x (.inl hposT) _).mpr (.inr ⟨w, hw, hl, rfl, .inl hpd⟩)
  have htot : total (setRes rF tid (((rF tid).op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x
      (w.val, tw))) (rmwGhost g x tr tw false []) c = total rF g c := by
    rw [← total_withThread _ _ c tid c.threads[tid] c.mem,
      total_rmw (ss := []) (new := w.val) (t' := c.threads[tid]) (mem' := c.mem) ht (by simp [Res.op_unit]) hpos,
      Res.addW_of_mem hX]
  have hupd0 : ∀ ι ∈ g.upd x, (total rF g c).acq x ι = 0 := fun ι h => ((E.updIds x).2 ι h).2
  have hu : ∀ s, s ∈ (rmwGhost g x tr tw false []).u ↔ s ∈ g.u ∧ updSlot g (x, tr) s = false := by
    intro s; rw [mem_rmw_u]; simp
  exact {
    valid := by rw [htot]; exact E.valid
    slotIds := fun s hs => E.slotIds s ((hu s).mp hs).1
    acqIds := by rw [htot]; exact E.acqIds
    relAcq := by rw [htot]; exact E.relAcq
    writes := by rw [htot]; exact E.writes
    pure := E.pure
    relExists := E.relExists
    slotsNodup := by
      simp only [rmwGhost, List.append_nil]
      exact (List.Sublist.map _ List.filter_sublist).nodup E.slotsNodup
    slotsDom := by
      intro k ι
      rw [htot, claimed_rmw]
      constructor
      · rintro ⟨s, hs, rfl, rfl⟩
        obtain ⟨hs, hup⟩ := (hu s).mp hs
        obtain ⟨hk, hd⟩ := (E.slotsDom s.key s.id).mp ⟨s, hs, rfl, rfl⟩
        refine ⟨hk, ?_⟩
        rcases hd with hd | ⟨hu', hc⟩
        · exact .inl hd
        · refine .inr ⟨hu', ?_⟩
          rintro (he | hc')
          · have hu'' : s.id ∈ g.upd x := by simpa [he] using hu'
            simp [updSlot, he, hu''] at hup
          · exact hc hc'
      · rintro ⟨hk, hd⟩
        have hd' : (total rF g c).acq k.1 ι = 1 ∨ (ι ∈ g.upd k.1 ∧ ¬ g.Claimed k) := by
          rcases hd with hd | ⟨hu', hc⟩
          · exact .inl hd
          · exact .inr ⟨hu', fun h => hc (.inr h)⟩
        obtain ⟨s, hs, rfl, rfl⟩ := (E.slotsDom k ι).mpr ⟨hk, hd'⟩
        refine ⟨s, (hu s).mpr ⟨hs, ?_⟩, rfl, rfl⟩
        simp only [updSlot, decide_eq_false_iff_not, not_and]
        intro he hu'
        rcases hd with hd | ⟨-, hc⟩
        · rw [he] at hd; rw [hupd0 _ hu'] at hd; cases hd
        · exact hc (.inl he)
    slotsPred := fun s hs v hv => E.slotsPred s ((hu s).mp hs).1 v hv
    promWf := E.promWf
    promValid := fun _ _ _ hT => absurd trivial hT
    pend := E.pend
    updIds := by rw [htot]; exact E.updIds
    relSettled := E.relSettled
    claimsNodup := by
      simp only [rmwGhost, List.map_cons, List.nodup_cons]
      exact ⟨hun, E.claimsNodup⟩
    claimsAt := by
      intro k tw' hk
      rcases List.mem_cons.mp hk with he | hk
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨htr, w, hw, hl, .inl hpd, hb⟩
      · exact E.claimsAt k tw' hk
    claimFulf := by
      intro k tw' hk
      rcases List.mem_cons.mp hk with he | hk
      · simp only [Prod.mk.injEq] at he
        obtain ⟨-, rfl⟩ := he
        exact hpd
      · exact E.claimFulf k tw' hk }

/-- After a write event that fulfils the promise `tw` of `tid`, no thread
holds `tw`: `tid` dropped it, and every other thread's promises are its own
messages (`promWf`), while `tw` is `tid`'s. -/
theorem ErAt.not_outstanding_fulfilled {T : Nat → Prop} {t : Thread I} {r : Res} {cx cx' : Ctx}
    (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size) (hi : cx.Inv tid)
    {l : Loc} {v : Val} {trOpt : Option Time} {tw : Time} (hev : WriteEv tid cx cx' l v trOpt tw)
    (hget : cx.mem.get? tw = some ⟨l, v, tid⟩) :
    ¬ Outstanding (c.withThread tid { t with prom := cx'.prom } cx'.mem) tw := by
  rw [outstanding_withThread hn, hev.prom]
  rintro (h | ⟨i, t', hne, hi', h⟩)
  · exact ((List.Nodup.mem_erase_iff hi.nodup).mp h).1 rfl
  · have hC : (c.withThread tid { t with prom := cx.prom } cx.mem).threads[i]? = some t' := by
      rw [Config.withThread_get? c _ _ hn, ite_eq_right (Ne.symm hne)]; exact hi'
    obtain ⟨w', hw', htid⟩ := E.promWf i t' hC tw h
    change cx.mem.get? tw = some w' at hw'
    rw [hget] at hw'
    cases hw'
    exact hne htid.symm

end Claim

section Rule

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- **An RMW with a claiming pending branch** (`T = ⊤`): `eraseWPR_rmw_pend'`
where a write fulfilling a pending promise also claims the message read
(`ErAt.fulfilPend`, then `Erase.claimPend`: the claimer is performed). Both successful branches receive
the value read and the unclaimedness of the message read (no promise of the
thread is a claimer, `Erase.claimFulf`). -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_rmw_pendClaim (hn : tid < c.threads.size) {k : RmwKind}
    {noRet : Bool} {l : Loc} {op : Val → Option Val} {ret : Val → EvTree σ}
    (hfail : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      op x.2.1 = none → (ret x.2.1).EraseWPR A tid iv rF (fun _ => True) c t Post r g (fenceOptCtx A x.2.2))
    (hp : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → tw ∈ g.pend → x.2.2.mem.read? l x.1 = some x.2.1 →
      ¬ g.Claimed (l, x.1) →
      0 < (r.wr l).q ∧
        (claimedSlots g l x.1 ≠ [] → x.1 ≤ (rmwAfter A k noRet l cx').views.wfloor) ∧
        (ret x.2.1).EraseWPR A tid iv rF (fun _ => True) c t Post
          ((r.op (Res.prod ((claimedSlots g l x.1).map (·.res)))).addW l (new, tw))
          (unpend (rmwGhost g l x.1 tw false []) tw) (rmwAfter A k noRet l cx'))
    (hok : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → tw ∉ g.pend → x.2.2.mem.read? l x.1 = some x.2.1 →
      ¬ g.Claimed (l, x.1) →
      ErAt rF (fun _ => True) c t tid r g x.2.2 →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res),
        0 < (r.wr l).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw new cx'.mem ss ∧ ¬ g.Claimed (l, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel l) new) ∧
        r'.op (Res.prod (ss.map (·.res))) =
          (r.op (Res.prod ((claimedSlots g l x.1).map (·.res)))).addW l (new, tw) ∧
        (tw ∈ x.2.2.prom → ss = []) ∧
        (claimedSlots g l x.1 ≠ [] → x.1 ≤ (rmwAfter A k noRet l cx').views.wfloor) ∧
        (ret x.2.1).EraseWPR A tid iv rF (fun _ => True) c t Post r' (rmwGhost g l x.1 tw rel ss)
          (rmwAfter A k noRet l cx')) :
    (EvTree.rmw k noRet l op ret).EraseWPR A tid iv rF (fun _ => True) c t Post r g cx := by
  intro x hx
  refine ⟨hfail x hx, fun new hop cx' hc E hi hm => ?_⟩
  obtain ⟨tw, hev, hrd, hseen⟩ := rmw_event A tid iv hx hi hc
  have hi2 := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
  obtain ⟨htr, hat⟩ := hev.tr x.1 rfl
  -- no promise of the thread is a claimer (`Erase.claimFulf`)
  have hnp : ∀ p ∈ x.2.2.prom, p ∈ g.pend → ((l, x.1), p) ∉ g.claims := by
    intro p hp' _ hcl
    exact E.claimFulf _ p hcl ⟨tid, _, ErAt.get? hn, hp'⟩
  have hun' : ¬ g.Claimed (l, x.1) :=
    Erase.not_claimed_noclaim E (ErAt.get? hn) (hev.writeAt hi2) rfl htr hrd hat hnp hseen
  by_cases hpd : tw ∈ g.pend
  · obtain ⟨hpos, htr', hk⟩ := hp x hx new hop cx' tw hc hev hpd hrd hun'
    have hwm : x.2.2.mem.get? tw = some ⟨l, new, tid⟩ := by
      rcases hev.cases with ⟨-, -, hg⟩ | ⟨-, rfl⟩
      · exact hg
      · obtain ⟨⟨w, hw⟩, -⟩ := E.pend _ hpd
        have := Memory.last_le_of_get?_eq_some _ hw
        simp only [Config.withThread] at this
        omega_t
    have hm' : cx'.mem = x.2.2.mem := by
      rcases hev.cases with ⟨h, -⟩ | ⟨-, rfl⟩
      · exact h
      · obtain ⟨⟨w, hw⟩, -⟩ := E.pend _ hpd
        have := Memory.last_le_of_get?_eq_some _ hw
        simp only [Config.withThread] at this
        omega_t
    have E1 : ErAt rF (fun _ => True) c t tid r (unpend g tw) cx' := ErAt.fulfilPend E hn hi2 hev hpd
    have hno := ErAt.not_outstanding_fulfilled E hn hi2 hev hwm
    have E2 := Erase.claimPend (tid := tid) (g := unpend g tw) E1 (by rw [Config.withThread_size]; exact hn) htr
      (show cx'.mem.get? tw = some ⟨l, new, tid⟩ by rw [hm']; exact hwm) rfl hno
      (fun ts w' h1 h2 hw' hl' => atomic_between hat hrd h1 h2 (by rw [← hm']; exact hw') hl') hun'
      (by rw [setRes_self]; exact hpos)
    simp only [setRes_setRes, setRes_self] at E2
    have hg : rmwGhost (unpend g tw) l x.1 tw false [] = unpend (rmwGhost g l x.1 tw false []) tw := rfl
    have hcs : claimedSlots (unpend g tw) l x.1 = claimedSlots g l x.1 := rfl
    rw [hg, hcs] at E2
    exact ⟨(r.op (Res.prod ((claimedSlots g l x.1).map (fun s : Slot => s.res)))).addW l (new, tw),
      unpend (rmwGhost g l x.1 tw false []) tw, E2,
      RStep.trans (RStep.rmw (p := (new, tw)) (FreshSlots.nil _) (by simp [Res.op_unit]) htr') (RStep.unpend tw _) (Nat.le_refl _),
      hk⟩
  · obtain ⟨hm1, -⟩ := fenceOptCtx_memProm A cx
    obtain ⟨hm2, -⟩ := readSuccs_memProm A iv hx
    have hm' : c.mem.last ≤ x.2.2.mem.last := by rw [hm2, hm1]; exact hm
    obtain ⟨rel, ss, r', hpos, hrel, hrlx, hres, hf, htr', hwp⟩ := hok x hx new hop cx' tw hc hev hpd hrd hun' E
    exact ⟨r', _, ErAt.rmw_pendOk E hn hi2 hev hrd hseen hnp hpd hpos hrel hrlx hres hval_trueT,
      RStep.rmw (hev.freshSlots hm' (slots_key hrel hrlx) hf) hres htr', hwp⟩

end Rule

end Kraken.Promising.SLR
