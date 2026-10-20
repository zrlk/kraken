/-
The write events of an instruction, at context level, for the erasure WP
(`EvTree.EraseWP`, `SLR/Lift.lean`).

## Contents

- `WriteEv`: the machine side of one write event between two contexts of
  thread `tid` (fulfil an outstanding promise `tw`, or append at `|M| + 1`;
  the promise set loses `tw`; an exclusive write's `tr < tw` and `atomic`).
  `writeSuccs_writeEv` extracts it from `writeSuccs`; `rmw_event` adds what
  an RMW's read gives (`read?`, and `OwnSeen` from `Ctx.Inv`).
- `Erase.store`: **a store keeps erasure** (event level; plain or release
  store, no claim; the counterpart of S2b's `Erase.rmw` without the read).
  `Erase.hval_store`: its other-thread promise-validity hypothesis when the
  storing thread is exempt.
- `ErAt.store`, `ErAt.rmw`: the event lemmas at context level, i.e. the
  write obligations of `EvTree.EraseWP`, discharged from the rule's
  resource-level preconditions.
-/
import Kraken.Promising.SLR.Lift

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## The machine side of a write event -/

/-- One write event of thread `tid` from context `cx` to `cx'`: the message
`⟨l, v, tid⟩` at `tw` fulfils the outstanding promise `tw` (memory
unchanged) or is appended at `|M| + 1`; the promise set loses `tw`; for an
exclusive write paired with a read at `tr` (`trOpt = some tr`), `tr < tw` and
the `atomic` check holds. -/
structure WriteEv (tid : Nat) (cx cx' : Ctx) (l : Loc) (v : Val) (trOpt : Option Time) (tw : Time) : Prop where
  cases : (cx'.mem = cx.mem ∧ tw ∈ cx.prom ∧ cx.mem.get? tw = some ⟨l, v, tid⟩) ∨
    (cx'.mem = (cx.mem.append ⟨l, v, tid⟩).1 ∧ tw = cx.mem.last + 1)
  prom : cx'.prom = cx.prom.erase tw
  tr : ∀ tr, trOpt = some tr → tr < tw ∧ cx.mem.atomic l tid tr tw = true

private theorem msg_eq {w : Msg} {l : Loc} {v : Val} {tid : Nat} (h1 : w.loc = l) (h2 : w.val = v) (h3 : w.tid = tid) :
    w = ⟨l, v, tid⟩ := by
  cases w; simp_all

/-- Every `writeSuccs` successor is a `WriteEv`. -/
theorem writeSuccs_writeEv {xr : View} (A : Arch) (tid : Nat) (iv : InstrViews) {cx : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc}
    {v : Val} {trOpt : Option Time} {extra : View} {cx' : Ctx} (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v trOpt extra xr)
    (hi : cx.Inv tid) : ∃ tw, WriteEv tid cx cx' l v trOpt tw := by
  unfold writeSuccs at hc
  rw [List.mem_append, List.mem_filterMap] at hc
  rcases hc with ⟨t, htp, hc⟩ | hc
  · split at hc
    · rename_i w hw
      obtain ⟨hcond, hc⟩ := Option.ite_none_right_eq_some.mp hc
      simp only [Option.some.injEq] at hc
      subst hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨⟨hl, hv⟩, htid⟩, hok⟩ := hcond
      refine ⟨t, ⟨.inl ⟨rfl, htp, hw.trans (congrArg some (msg_eq hl hv htid))⟩, rfl, fun tr htr => ?_⟩⟩
      subst htr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      exact hok.2
    · cases hc
  · split at hc
    rename_i _ mem' t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at hc
    obtain ⟨hok', rfl⟩ := hc
    have ht : t = cx.mem.last + 1 := (congrArg Prod.snd hok).symm
    have hm : mem' = (cx.mem.append { loc := l, val := v, tid }).1 := (congrArg Prod.fst hok).symm
    subst ht hm
    have hnot : cx.mem.last + 1 ∉ cx.prom := fun hp => by
      obtain ⟨w, hw, -⟩ := hi.prom _ hp
      have := cx.mem.last_le_of_get?_eq_some hw
      omega_t
    refine ⟨cx.mem.last + 1, ⟨.inr ⟨rfl, rfl⟩, ?_, fun tr htr => ?_⟩⟩
    · show (cx.prom ++ [cx.mem.last + 1]).erase (cx.mem.last + 1) = cx.prom.erase (cx.mem.last + 1)
      rw [List.erase_append_right _ hnot, List.erase_cons_head, List.append_nil, List.erase_of_not_mem hnot]
    · subst htr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
      exact hok'.2

theorem readSuccs_read (A : Arch) (iv : InstrViews) {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : c.mem.read? l x.1 = some x.2.1 := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · rename_i v hv
    by_cases hp : (c.mem.writeIn l t (max (max iv.addrR (max c.views.vrNew
        (if (A.loadKind k == LoadKind.acq) = true then c.views.vRel else 0))) (c.views.getCoh l)) ||
        c.prom.contains t) = true
    · rw [ite_eq_left hp] at ht; cases ht
    · rw [ite_eq_right hp] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      exact hv

/-- **The machine side of a successful RMW event** at context level: the
read at `x.1` returned `x.2.1`, the write is a `WriteEv` with `x.1 < tw` and
`atomic`, and (from `Ctx.Inv`, `ownSeen_of_readSuccs`) the thread has no
performed write to `l` above `x.1`. -/
theorem rmw_event (A : Arch) (tid : Nat) (iv : InstrViews) {cx : Ctx} {kk : LoadKind} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv (fenceOptCtx A cx) kk false l noRet) (hi : cx.Inv tid)
    {sk : StoreKind} {new : Val} {νr : View} {cx' : Ctx} (hw : cx' ∈ writeSuccs A tid iv x.2.2 sk true l new (some x.1) νr) :
    ∃ tw, WriteEv tid x.2.2 cx' l new (some x.1) tw ∧ x.2.2.mem.read? l x.1 = some x.2.1 ∧
      ∀ ts w, x.2.2.mem.get? ts = some w → w.loc = l → w.tid = tid → ts ∉ x.2.2.prom → ts ≤ x.1 := by
  have hi1 := (fenceOpt_inv tid hi A.rmwFence .sy).1
  obtain ⟨hm, hp⟩ := readSuccs_memProm A iv hx
  have hi2 := (readSuccs_inv A tid iv hx hi1).1
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid iv hw hi2
  refine ⟨tw, hev, by rw [hm]; exact readSuccs_read A iv hx, fun ts w hw' hl htid hts => ?_⟩
  rw [hm] at hw'; rw [hp] at hts
  exact ownSeen_of_readSuccs A iv hx hi1.own ts w hw' hl htid hts

/-! ## Store events: erasure -/

/-- The ghost state after a store of `x` at `tw`: for a release store
(`rel`) the message enters release mode with its slots `ss`. -/
def storeGhost (g : Ghost) (x : Loc) (tw : Time) (rel : Bool) (ss : List Slot) : Ghost :=
  { g with
    u := g.u ++ ss
    relMsgs := if rel then (x, tw) :: g.relMsgs else g.relMsgs }

section Store

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {t t' : Thread I}
  {mem' : Memory} {x : Loc} {tw : Time} {new : Val} {rel : Bool} {ss : List Slot}

theorem mem_store_relMsgs {k : Key} :
    k ∈ (storeGhost g x tw rel ss).relMsgs ↔ (rel = true ∧ k = (x, tw)) ∨ k ∈ g.relMsgs := by
  unfold storeGhost; cases rel <;> simp

theorem mem_store_u {s : Slot} : s ∈ (storeGhost g x tw rel ss).u ↔ s ∈ g.u ∨ s ∈ ss := by
  simp [storeGhost]

theorem claimed_store {k : Key} : (storeGhost g x tw rel ss).Claimed k ↔ g.Claimed k := Iff.rfl

/-- The total resource after the store: the new slots out of the thread, and
the write set of `x` gained `(new, tw)`. -/
theorem total_store (ht : c.threads[tid]? = some t) {r' : Res}
    (hres : r'.op (Res.prod (ss.map (·.res))) = (rF tid).addW x (new, tw)) (hpos : 0 < ((rF tid).wr x).q) :
    total (setRes rF tid r') (storeGhost g x tw rel ss) (c.withThread tid t' mem') =
      (total rF g c).addW x (new, tw) := by
  have hn := lt_size_of_get? ht
  obtain ⟨rest, hrest⟩ := threadsRes_split rF hn
  have h1 := hrest rF (fun _ _ => rfl)
  have h2 := hrest (setRes rF tid r') (fun i hi => setRes_ne rF r' hi)
  rw [setRes_self] at h2
  simp only [total, Config.withThread_size, Ghost.slotsRes, storeGhost, List.map_append, Res.prod_append, h1, h2]
  generalize Res.prod (g.u.map (·.res)) = K at *
  generalize Res.prod (ss.map (·.res)) = S at *
  calc (r'.op rest).op (K.op S) = (r'.op S).op (rest.op K) := by
        simp only [Res.op_left_comm, Res.op_comm]
    _ = ((rF tid).addW x (new, tw)).op (rest.op K) := by rw [hres]
    _ = ((rF tid).op (rest.op K)).addW x (new, tw) := Res.addW_op _ _ hpos
    _ = (((rF tid).op rest).op K).addW x (new, tw) := by
        congr 1; simp only [Res.op_left_comm, Res.op_comm]

/-- **A store keeps erasure** (event level).
Thread `tid` writes `new` to `x` at `tw` (`WriteAt`: fulfilling its promise
or appending). Precondition (SLR's relaxed write rule for `rel = false`:
the value is pure; its release write rule, Lemma 49, for `rel = true`: `ss`
are the slots of the new message, `SlotsFor`, from `Erase.slotsFor`): the
thread owns a write permission for `x` (`hpos`); its resource after the
event is `r'` with `r' • ss = r` plus `(new, tw)` in `x`'s write set
(`hres`). `hval`: the outstanding promises of the non-exempt threads are
valid after the event (`Erase.hval_store` when the storing thread is
exempt). Then erasure holds after the event, with the new slots in `u`
(`storeGhost`). No message is claimed. -/
theorem Erase.store (E : Erase rF g T c) (ht : c.threads[tid]? = some t)
    (hw : WriteAt c tid t t' mem' tw ⟨x, new, tid⟩) (hpend : tw ∉ g.pend) (hpos : 0 < ((rF tid).wr x).q)
    (hrel : rel = true → SlotsFor g (total rF g c).acq x tw new mem' ss ∧ ¬ g.Claimed (x, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel x) new)
    {r' : Res} (hres : r'.op (Res.prod (ss.map (·.res))) = (rF tid).addW x (new, tw))
    (hval : ∀ i t₁, (c.withThread tid t' mem').threads[i]? = some t₁ → ¬ T i → ∀ ts ∈ t₁.prom,
      ts ∉ g.pend → ∀ w, mem'.get? ts = some w → mayWrite (setRes rF tid r' i) (storeGhost g x tw rel ss) w.loc) :
    Erase (setRes rF tid r') (storeGhost g x tw rel ss) T (c.withThread tid t' mem') := by
  have hn := lt_size_of_get? ht
  have htot := total_store (rel := rel) (t' := t') (mem' := mem') (g := g) ht hres hpos
  have hset : ∀ p, Settled (c.withThread tid t' mem') (storeGhost g x tw rel ss) p ↔ Settled c g p ∨ p = tw :=
    fun p => WriteAt.settled_iff E ht hw rfl
  have hpre := hw.pre
  have hfresh : (x, tw) ∉ g.relMsgs := by
    intro h
    rcases hw.cases with ⟨-, hp, -⟩ | ⟨-, rfl⟩
    · rcases E.relSettled _ h with h' | h'
      · exact h' ⟨tid, t, ht, hp⟩
      · exact hpend h'
    · have := E.relMsgs_le h; simp only at this; omega_t
  have hnoslot : ∀ s ∈ g.u, s.key ≠ (x, tw) := fun s hs hk =>
    hfresh (hk ▸ ((E.slotsDom s.key s.id).mp ⟨s, hs, rfl, rfl⟩).1)
  have hposT : 0 < ((total rF g c).wr x).q := by
    unfold total threadsRes
    exact Res.pos_op.mpr (.inl (Res.pos_prod_of_mem (List.mem_map.mpr ⟨tid, List.mem_range.mpr hn, rfl⟩) hpos))
  have hupd0 : ∀ ι ∈ g.upd x, (total rF g c).acq x ι = 0 := fun ι h => ((E.updIds x).2 ι h).2
  exact {
    valid := by rw [htot, Res.valid_addW]; exact E.valid
    slotIds := by
      intro s hs
      rcases mem_store_u.mp hs with hs | hs
      · exact E.slotIds s hs
      · obtain ⟨⟨hid, -, -⟩, -⟩ := hrel (by cases rel <;> simp_all)
        have : s.id ∈ g.acqIds (total rF g c).acq x ++ g.upd x := hid ▸ List.mem_map_of_mem hs
        rcases List.mem_append.mp this with h | h
        · simp only [Ghost.acqIds, List.mem_filter, List.mem_range] at h; exact h.1
        · exact ((E.updIds x).2 _ h).1
    acqIds := by rw [htot, Res.addW_acq]; exact E.acqIds
    relAcq := by rw [htot, Res.addW_acq]; exact E.relAcq
    writes := by
      rw [htot]
      intro y hy p
      have hfulf : Fulf (c.withThread tid t' mem') (storeGhost g x tw rel ss) y p ↔
          Fulf c g y p ∨ (y = x ∧ p = (new, tw)) := by
        unfold Fulf
        simp only [Config.withThread, hpre.initVal]
        constructor
        · rintro (h | ⟨w', hw', hl, hv, hs⟩)
          · exact .inl (.inl h)
          · rcases hw.get?_iff.mp hw' with hw' | ⟨h1, rfl⟩
            · rcases (hset p.2).mp hs with hs | hs
              · exact .inl (.inr ⟨w', hw', hl, hv, hs⟩)
              · rw [hs] at hw'
                obtain rfl := hw.old_tw hw'
                exact .inr ⟨hl.symm, Prod.ext hv.symm hs⟩
            · exact .inr ⟨hl.symm, Prod.ext hv.symm h1⟩
        · rintro ((h | ⟨w', hw', hl, hv, hs⟩) | ⟨rfl, rfl⟩)
          · exact .inl h
          · exact .inr ⟨w', hw.get?_iff.mpr (.inl hw'), hl, hv, (hset _).mpr (.inl hs)⟩
          · exact .inr ⟨_, hw.get?_tw, rfl, rfl, (hset _).mpr (.inr rfl)⟩
      rw [hfulf]
      by_cases hyx : y = x
      · subst hyx
        rw [Res.addW_X_self, E.writes y (.inl hposT) p]
        simp only [hposT, true_and]
      · rw [Res.addW_wr_ne _ _ hyx]
        simp only [hyx, false_and, or_false]
        apply E.writes y
        rcases hy with hy | ⟨ts, w', hw', hl, hs⟩
        · rw [Res.addW_q] at hy; exact .inl hy
        · rcases hw.get?_iff.mp hw' with hw' | ⟨rfl, rfl⟩
          · rcases (hset ts).mp hs with hs | rfl
            · exact .inr ⟨ts, w', hw', hl, hs⟩
            · obtain rfl := hw.old_tw hw'; exact absurd hl.symm hyx
          · exact absurd hl.symm hyx
    pure := by
      intro y ts v hv hnot
      change mem'.read? y ts = some v at hv
      by_cases hts : ts = tw
      · subst hts
        obtain ⟨rfl, rfl⟩ := hw.read?_tw hv
        cases rel with
        | true => exact absurd (mem_store_relMsgs.mpr (.inl ⟨rfl, rfl⟩)) hnot
        | false => exact (hrlx rfl).2
      · rw [hw.read?_ne hts] at hv
        exact E.pure y ts v hv fun h => hnot (mem_store_relMsgs.mpr (.inr h))
    relExists := by
      intro k hk
      rcases mem_store_relMsgs.mp hk with ⟨-, rfl⟩ | hk
      · exact ⟨new, hw.read?_tw_self⟩
      · obtain ⟨v, hv⟩ := E.relExists k hk
        exact ⟨v, (hpre.read? (E.relMsgs_le hk)).trans hv⟩
    slotsNodup := by
      simp only [storeGhost, List.map_append]
      rw [List.nodup_append]
      refine ⟨E.slotsNodup, ?_, ?_⟩
      · cases rel with
        | false => rw [(hrlx rfl).1]; exact List.nodup_nil
        | true =>
          obtain ⟨⟨hid, hkey, -⟩, -⟩ := hrel rfl
          have hids : (ss.map (·.id)).Nodup := by
            rw [hid, List.nodup_append]
            refine ⟨List.nodup_range.filter _, (E.updIds x).1, fun a ha b hb hab => ?_⟩
            subst hab
            simp only [Ghost.acqIds, List.mem_filter, beq_iff_eq] at ha
            rw [hupd0 a hb] at ha
            exact absurd ha.2 (by decide)
          have : ss.map (fun s => (s.key, s.id)) = (ss.map (·.id)).map (fun ι => ((x, tw), ι)) := by
            rw [List.map_map]; exact List.map_congr_left fun s hs => by simp [hkey s hs]
          rw [this]
          exact List.Pairwise.map _ (fun a b hab he => hab (by simp at he; exact he)) hids
      · intro a ha b hb hab
        subst hab
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ha
        obtain ⟨s', hs', he⟩ := List.mem_map.mp hb
        cases rel with
        | false => rw [(hrlx rfl).1] at hs'; cases hs'
        | true =>
          have hk := ((hrel rfl).1.key s' hs')
          have : s.key = (x, tw) := by simp at he; rw [← he.1, hk]
          exact hnoslot s hs this
    slotsDom := by
      intro k ι
      rw [htot, Res.addW_acq, claimed_store, mem_store_relMsgs]
      constructor
      · rintro ⟨s, hs, rfl, rfl⟩
        rcases mem_store_u.mp hs with hs | hs
        · obtain ⟨hk, hd⟩ := (E.slotsDom s.key s.id).mp ⟨s, hs, rfl, rfl⟩
          exact ⟨.inr hk, hd⟩
        · obtain ⟨⟨hid, hkey, -⟩, hnc⟩ := hrel (by cases rel <;> simp_all)
          have hr : rel = true := by cases rel <;> simp_all
          have hk := hkey s hs
          refine ⟨.inl ⟨hr, hk⟩, ?_⟩
          have : s.id ∈ g.acqIds (total rF g c).acq x ++ g.upd x := hid ▸ List.mem_map_of_mem hs
          rw [hk]
          rcases List.mem_append.mp this with h | h
          · simp only [Ghost.acqIds, List.mem_filter, beq_iff_eq] at h; exact .inl h.2
          · exact .inr ⟨h, hnc⟩
      · rintro ⟨hk, hd⟩
        rcases hk with ⟨hr, rfl⟩ | hk
        · obtain ⟨⟨hid, hkey, -⟩, -⟩ := hrel hr
          have hmem : ι ∈ ss.map (·.id) := by
            rw [hid, List.mem_append]
            rcases hd with hd | ⟨hu, -⟩
            · left
              simp only [Ghost.acqIds, List.mem_filter, List.mem_range, beq_iff_eq]
              exact ⟨E.acqIds x ι (Nat.le_of_eq hd.symm), hd⟩
            · exact .inr hu
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
          exact ⟨s, mem_store_u.mpr (.inr hs), hkey s hs, rfl⟩
        · obtain ⟨s, hs, rfl, rfl⟩ := (E.slotsDom k ι).mpr ⟨hk, hd⟩
          exact ⟨s, mem_store_u.mpr (.inl hs), rfl, rfl⟩
    slotsPred := by
      intro s hs v hv
      change mem'.read? _ _ = some v at hv
      rcases mem_store_u.mp hs with hs | hs
      · have hk : s.key ∈ g.relMsgs := ((E.slotsDom s.key s.id).mp ⟨s, hs, rfl, rfl⟩).1
        rw [hpre.read? (E.relMsgs_le hk)] at hv
        exact (g.acqPred s.id).mono _ _ _ _ _ hpre (E.slotsPred s hs v hv)
      · obtain ⟨⟨-, hkey, hp⟩, -⟩ := hrel (by cases rel <;> simp_all)
        rw [hkey s hs] at hv ⊢
        obtain ⟨-, rfl⟩ := hw.read?_tw hv
        exact hp s hs
    promWf := by
      intro i t₁ hi ts hts
      rw [Config.withThread_get? c t' mem' hn] at hi
      split at hi
      · next h =>
        subst h
        simp only [Option.some.injEq] at hi
        subst hi
        obtain ⟨w', hw', htid⟩ := E.promWf tid t ht ts (hw.sub ts hts)
        exact ⟨w', hw.get?_iff.mpr (.inl hw'), htid⟩
      · obtain ⟨w', hw', htid⟩ := E.promWf i t₁ hi ts hts
        exact ⟨w', hw.get?_iff.mpr (.inl hw'), htid⟩
    promValid := fun i t₁ hi hT ts hts hp w hw => hval i t₁ hi hT ts hts hp w hw
    pend := by
      intro ts hts
      obtain ⟨⟨w', hw'⟩, ho⟩ := E.pend ts hts
      refine ⟨⟨w', hw.get?_iff.mpr (.inl hw')⟩, (WriteAt.outstanding_iff E ht hw).mpr ⟨ho, ?_⟩⟩
      rintro rfl; exact hpend hts
    updIds := by rw [htot, Res.addW_acq]; exact E.updIds
    relSettled := by
      intro k hk
      rcases mem_store_relMsgs.mp hk with ⟨-, rfl⟩ | hk
      · exact (hset _).mpr (.inr rfl)
      · exact (hset _).mpr (.inl (E.relSettled k hk))
    claimsNodup := E.claimsNodup
    claimsAt := by
      intro k tw' hk
      obtain ⟨hlt, w', hw', hl, hs, hb⟩ := E.claimsAt k tw' hk
      have hle' := c.mem.last_le_of_get?_eq_some hw'
      refine ⟨hlt, w', hw.get?_iff.mpr (.inl hw'), hl, (hset _).mpr (.inl hs), ?_⟩
      intro ts w'' h1 h2 hw'' hl''
      change mem'.get? ts = some w'' at hw''
      rw [hpre.get? (by omega_t)] at hw''
      exact hb ts w'' h1 h2 hw'' hl''
    claimFulf := fun k tw' hk ho => E.claimFulf k tw' hk ((WriteAt.outstanding_iff E ht hw).mp ho).1 }

/-- A store keeps every `mayWrite`: the slots only grow. -/
theorem mayWrite_store {r : Res} {y : Loc} (h : mayWrite r g y) : mayWrite r (storeGhost g x tw rel ss) y := by
  have hu : ∀ s ∈ g.u, s ∈ (storeGhost g x tw rel ss).u := fun s hs => mem_store_u.mpr (.inl hs)
  rcases h with h | ⟨s, hs, hc, hq⟩
  · exact .inl h
  · exact .inr ⟨s, hu s hs, hc.mono hu, hq⟩

/-- The `hval` hypothesis of `Erase.store` when the storing thread is exempt
(`NPSafe`'s weak erasure, `T = (· = tid)`): the other threads' promises are
as before, and their `mayWrite` survives. -/
theorem Erase.hval_store (E : Erase rF g T c) (ht : c.threads[tid]? = some t)
    (hw : WriteAt c tid t t' mem' tw ⟨x, new, tid⟩) (hT : T tid) (r' : Res) :
    ∀ i t₁, (c.withThread tid t' mem').threads[i]? = some t₁ → ¬ T i → ∀ ts ∈ t₁.prom,
      ts ∉ g.pend → ∀ w, mem'.get? ts = some w → mayWrite (setRes rF tid r' i) (storeGhost g x tw rel ss) w.loc := by
  intro i t₁ hi hTi ts hts hp w hw'
  have hn := lt_size_of_get? ht
  rw [Config.withThread_get? c t' mem' hn] at hi
  split at hi
  · next h => subst h; exact absurd hT hTi
  · next h =>
    obtain ⟨w', hw'', -⟩ := E.promWf i t₁ hi ts hts
    rw [hw.pre.get? (c.mem.last_le_of_get?_eq_some hw''), hw''] at hw'
    cases hw'
    rw [setRes_ne rF r' (Ne.symm h)]
    exact mayWrite_store (E.promValid i t₁ hi hTi ts hts hp w hw'')

end Store

/-! ## The write obligations of the erasure WP -/

section Ctx

variable {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I} {tid : Nat} {r : Res} {g : Ghost}
  {cx cx' : Ctx}

theorem setRes_setRes (rF : Nat → Res) (tid : Nat) (r r' : Res) : setRes (setRes rF tid r) tid r' = setRes rF tid r' := by
  funext i; simp only [setRes]; split <;> rfl

theorem total_withThread (rF : Nat → Res) (g : Ghost) (c : Config I) (tid : Nat) (t : Thread I) (m : Memory) :
    total rF g (c.withThread tid t m) = total rF g c := by
  simp only [total, Config.withThread_size]

/-- The write event as a `WriteAt` of the configuration at the context. -/
theorem WriteEv.writeAt {l : Loc} {v : Val} {trOpt : Option Time} {tw : Time} (h : WriteEv tid cx cx' l v trOpt tw)
    (hi : cx.Inv tid) :
    WriteAt (c.withThread tid { t with prom := cx.prom } cx.mem) tid { t with prom := cx.prom }
      { t with prom := cx'.prom } cx'.mem tw ⟨l, v, tid⟩ where
  sub p hp := by rw [h.prom] at hp; exact List.mem_of_mem_erase hp
  gone := by
    show tw ∉ cx'.prom
    rw [h.prom]; exact fun hm => ((List.Nodup.mem_erase_iff hi.nodup).mp hm).1 rfl
  keep p hp hne := by
    show p ∈ cx'.prom
    rw [h.prom]; exact (List.mem_erase_of_ne hne).mpr hp
  tid := rfl
  cases := h.cases

theorem ErAt.get? (hn : tid < c.threads.size) :
    (c.withThread tid { t with prom := cx.prom } cx.mem).threads[tid]? = some { t with prom := cx.prom } := by
  rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl]

/-- **The store obligation of the erasure WP** (context level): from erasure
at `cx`, a `WriteEv` to `cx'` and the store rule's preconditions
(`Erase.store`), erasure at `cx'`. -/
theorem ErAt.store (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size) (hi : cx.Inv tid)
    {x : Loc} {new : Val} {trOpt : Option Time} {tw : Time} (hev : WriteEv tid cx cx' x new trOpt tw)
    (hpend : tw ∉ g.pend) (hpos : 0 < (r.wr x).q) {rel : Bool} {ss : List Slot}
    (hrel : rel = true → SlotsFor g (total (setRes rF tid r) g c).acq x tw new cx'.mem ss ∧ ¬ g.Claimed (x, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel x) new)
    {r' : Res} (hres : r'.op (Res.prod (ss.map (·.res))) = r.addW x (new, tw))
    (hval : ∀ i t₁, (c.withThread tid { t with prom := cx'.prom } cx'.mem).threads[i]? = some t₁ → ¬ T i →
      ∀ ts ∈ t₁.prom, ts ∉ g.pend → ∀ w, cx'.mem.get? ts = some w →
        mayWrite (setRes rF tid r' i) (storeGhost g x tw rel ss) w.loc) :
    ErAt rF T c t tid r' (storeGhost g x tw rel ss) cx' := by
  have E' := Erase.store E (ErAt.get? hn) (hev.writeAt hi) hpend (by rw [setRes_self]; exact hpos)
    (by rw [total_withThread]; exact hrel) hrlx (r' := r') (by rw [setRes_self]; exact hres)
    (by rw [setRes_setRes, Config.withThread_withThread]; exact hval)
  unfold ErAt
  rw [setRes_setRes, Config.withThread_withThread] at E'
  exact E'

/-- **The RMW obligation of the erasure WP** (context level): from erasure at
the context after the RMW's read (`x.2.2`), the machine side of the event
(`rmw_event`), no pending promise of the thread, and the RMW rule's
preconditions (`Erase.rmw`), erasure at `cx'` with the update slots of
`(l, tr)` claimed. -/
theorem ErAt.rmw (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size) (hi : cx.Inv tid)
    {l : Loc} {new old : Val} {tr tw : Time} (hev : WriteEv tid cx cx' l new (some tr) tw)
    (hrd : cx.mem.read? l tr = some old)
    (hseen : ∀ ts w, cx.mem.get? ts = some w → w.loc = l → w.tid = tid → ts ∉ cx.prom → ts ≤ tr)
    (hnp : ∀ p ∈ cx.prom, p ∉ g.pend) (hpos : 0 < (r.wr l).q) {rel : Bool} {ss : List Slot}
    (hrel : rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw new cx'.mem ss ∧ ¬ g.Claimed (l, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel l) new)
    {r' : Res} (hres : r'.op (Res.prod (ss.map (·.res))) = (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (new, tw))
    (hval : ∀ i t₁, (c.withThread tid { t with prom := cx'.prom } cx'.mem).threads[i]? = some t₁ → ¬ T i →
      ∀ ts ∈ t₁.prom, ts ∉ g.pend → ∀ w, cx'.mem.get? ts = some w →
        mayWrite (setRes rF tid r' i) (rmwGhost g l tr tw rel ss) w.loc) :
    ErAt rF T c t tid r' (rmwGhost g l tr tw rel ss) cx' := by
  obtain ⟨htr, hat⟩ := hev.tr tr rfl
  have E' := Erase.rmw_of_seen E (ErAt.get? hn) (hev.writeAt hi) htr hrd hat hnp hseen
    (by rw [setRes_self]; exact hpos) (by rw [total_withThread]; exact hrel) hrlx (r' := r')
    (by rw [setRes_self]; exact hres) (by rw [setRes_setRes, Config.withThread_withThread]; exact hval)
  unfold ErAt
  rw [setRes_setRes, Config.withThread_withThread] at E'
  exact E'

end Ctx

/-! ## Rules for the common event shapes

The erasure WP of each kind of memory event, with the erasure part
discharged: what remains are the event rule's resource-level preconditions
(for a write) or nothing (for a read or a fence). These are ISA-generic: an
instruction's tree is built from such nodes under `EvTree.access` and
`choose` (both ISAs' adapters). -/

section Shapes

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- The other threads' promise validity after a write event, with thread
`tid` holding `r'` and ghost `g'` (the `hval` of `Erase.store`/`Erase.rmw`). -/
def HVal (rF : Nat → Res) (T : Nat → Prop) (c : Config I) (t : Thread I) (tid : Nat) (cx' : Ctx) (r' : Res)
    (g' : Ghost) : Prop :=
  ∀ i t₁, (c.withThread tid { t with prom := cx'.prom } cx'.mem).threads[i]? = some t₁ → ¬ T i →
    ∀ ts ∈ t₁.prom, ts ∉ g'.pend → ∀ w, cx'.mem.get? ts = some w → mayWrite (setRes rF tid r' i) g' w.loc

/-- `HVal` after a store, when the storing thread's promises are exempt
(`NPSafe`'s weak erasure). -/
theorem ErAt.hval_store (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size) (hi : cx.Inv tid) {cx' : Ctx}
    {x : Loc} {new : Val} {trOpt : Option Time} {tw : Time} (hev : WriteEv tid cx cx' x new trOpt tw) (hT : T tid)
    (r' : Res) {rel : Bool} {ss : List Slot} : HVal rF T c t tid cx' r' (storeGhost g x tw rel ss) := by
  have h := Erase.hval_store (rel := rel) (ss := ss) E (ErAt.get? hn) (hev.writeAt hi) hT r'
  rw [setRes_setRes, Config.withThread_withThread] at h
  exact h

/-- `HVal` after an RMW that claims no slot, when the RMW's thread is exempt. -/
theorem ErAt.hval_rmw_noClaim (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size) (hi : cx.Inv tid)
    {cx' : Ctx} {x : Loc} {new : Val} {tr tw : Time} (hev : WriteEv tid cx cx' x new (some tr) tw) (hT : T tid)
    (hcl : claimedSlots g x tr = []) (r' : Res) {rel : Bool} {ss : List Slot} :
    HVal rF T c t tid cx' r' (rmwGhost g x tr tw rel ss) := by
  have h := Erase.hval_of_noClaim (rel := rel) (ss := ss) E (ErAt.get? hn) (hev.writeAt hi) hT hcl r'
  rw [setRes_setRes, Config.withThread_withThread] at h
  exact h

theorem _root_.Kraken.Promising.EvTree.eraseWP_access {ds : Decls} {addr : BitVec 64} {n : Nat} {k : Loc → EvTree σ}
    (h : ∀ l, (k l).EraseWP A tid iv rF T c t Post r g cx) :
    (EvTree.access ds addr n k).EraseWP A tid iv rF T c t Post r g cx := by
  unfold EvTree.access
  split
  · exact h _
  · trivial

/-- **A load (plain or acquire) keeps erasure**: its WP is its
continuation's, with the same resources (SLR's read rules transfer in the
assertion layer, not in erasure). -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_load {k : LoadKind} {xcl : Bool} {l : Loc} {ret : Val → EvTree σ}
    (h : ∀ x ∈ readSuccs A iv cx k xcl l, (ret x.2.1).EraseWP A tid iv rF T c t Post r g x.2.2) :
    (EvTree.load k xcl l ret).EraseWP A tid iv rF T c t Post r g cx := h

/-- **A fence keeps erasure.** -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_fence {k : FenceKind} {ret : Unit → EvTree σ}
    (h : (ret ()).EraseWP A tid iv rF T c t Post r g (fenceStep cx k)) :
    (EvTree.fence k ret).EraseWP A tid iv rF T c t Post r g cx := h

/-- **A (non-exclusive) store, plain or release**: for each write event, the
store rule's preconditions (`ErAt.store`) and the continuation's WP. -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_store (hn : tid < c.threads.size) {k : StoreKind} {l : Loc} {v : Val}
    {ret : Bool → EvTree σ}
    (h : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → ErAt rF T c t tid r g cx → cx.Inv tid →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res), tw ∉ g.pend ∧ 0 < (r.wr l).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw v cx'.mem ss ∧ ¬ g.Claimed (l, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel l) v) ∧
        r'.op (Res.prod (ss.map (·.res))) = r.addW l (v, tw) ∧
        HVal rF T c t tid cx' r' (storeGhost g l tw rel ss) ∧
        (ret true).EraseWP A tid iv rF T c t Post r' (storeGhost g l tw rel ss) cx') :
    (EvTree.store k false l v ret).EraseWP A tid iv rF T c t Post r g cx := by
  refine ⟨fun cx' hc E hi => ?_, fun h => absurd h (by decide)⟩
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi
  obtain ⟨rel, ss, r', hpend, hpos, hrel, hrlx, hres, hval, hwp⟩ := h cx' tw hc hev E hi
  exact ⟨r', _, ErAt.store E hn hi hev hpend hpos hrel hrlx hres hval, hwp⟩

/-- **An RMW** (any kind, `noRet` included): a failed one (its operation
returns `none`: a failed CAS) only reads and needs nothing; for a successful
one, for each read `x` and write event, the RMW rule's preconditions
(`ErAt.rmw`: no pending promise of the thread, a write permission, the new
message's slots or purity, the resource after the claim, `HVal`) and the
continuation's WP. Uniqueness (`OwnSeen`, `atomic`) is discharged here, from
`Ctx.Inv`. -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_rmw (hn : tid < c.threads.size) {k : RmwKind} {noRet : Bool} {l : Loc}
    {op : Val → Option Val} {ret : Val → EvTree σ}
    (hfail : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      op x.2.1 = none → (ret x.2.1).EraseWP A tid iv rF T c t Post r g (fenceOptCtx A x.2.2))
    (hok : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → ErAt rF T c t tid r g x.2.2 →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res), (∀ p ∈ x.2.2.prom, p ∉ g.pend) ∧ 0 < (r.wr l).q ∧
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
  obtain ⟨rel, ss, r', hnp, hpos, hrel, hrlx, hres, hval, hwp⟩ := hok x hx new hop cx' tw hc hev E
  exact ⟨r', _, ErAt.rmw E hn hi2 hev hrd hseen hnp hpos hrel hrlx hres hval, hwp⟩

end Shapes

end Kraken.Promising.SLR
