/-
Fallback (iii) of design (V): the **prepaid release**.

Variant (ii) accounts a promised release by replaying the whole fulfilling
instruction `F` at promise time, which is the real `F` only when `F`'s
release store is its last memory event and nothing is appended before it
(`Erase.pendingOfFulfil`). x64 `movups`/`vmovdqu`, `CASP`/`CASPL` with the
other half after the release half, and instructions whose release store
follows a fresh append are outside that. Fallback (iii) accounts only the
release **event** at promise time:

- the slots `ss` of the release message `(x, ts)` (from the resource the
  thread holds just before `F`, checked at the promise-time memory) go into
  `u` at once (an acquirer may read the outstanding promise before `F`
  runs, so they cannot wait in the thread's ghost);
- the write-set entry `(v, ts)` is added to the thread's `W(x)` (a pending
  message is settled, hence in `Fulf`);
- for an RMW release half, the message it reads is claimed;
- `ts` is marked **pending**.

`SLR.Erase` and `SLR.Ghost` are unchanged: the prepaid message is a pending
release in the sense of S2a's pending clause, with the resource after the
release event (not after `F`). When `F` really runs, its release event
fulfils a pending promise (erasure carries, the resource is unchanged, `ts`
leaves `pend`), and its other events are ordinary event rules on the real
memory.

## Contents

- `Escrow`, `Escrow.Held`: what a promised release fixes at promise time,
  and the ghost facts that record it (documentation for Theorem 1′'s
  invariant; `prepayGhost_held`).
- **Promise-time law**: `Erase.prepay` (release store): erasure before the
  promise gives erasure after it with the release event accounted and `ts`
  pending: the event lemma `Erase.store` on an append, followed by
  `Erase.unfulfil`. Its RMW counterpart `Erase.prepayRmw` (claim at promise
  time) was retired with `Erase.claimFulf` (T1c option (B)): a claimer is a
  performed write, so a prepaid release RMW claims when it runs, with the
  pending promise already fulfilled (`prepayRmwGhost` and its `K1`/`K2`
  frames stay, for an RMW prepayment that does not claim early).
- **`F`-time laws**: `Erase.fulfilPend` / `ErAt.fulfilPend` (a write event
  that fulfils a pending promise keeps erasure, resource unchanged);
  `Erase.not_claimed_loc`, `ErAt.rmw_loc` (S2b's RMW event lemma with `hnp`
  weakened to "no pending promise *to this location*", needed by the other
  half of a prepaid `CASP`); the erasure-WP node shapes
  `EvTree.eraseWP_store_pend`, `EvTree.eraseWP_rmw_pend`,
  `EvTree.eraseWP_caspHalf_pend` (pending branch discharged; in
  `SLR/EscrowCasp.lean`, which keeps this file free of the AArch64 ISA).
- **Shapes**: `ErAt.store2_prepaidFirst` / `ErAt.store2_prepaidLast` (two
  stores in one instruction, x64 `movups`/`vmovdqu`, `STLXP`: the prepaid
  release first, resp. last after a fresh store) and
  `ErAt.rmw2_prepaidFirst` / `ErAt.rmw2_prepaidLast` (the two halves of a
  `CASP`, either order); `EvTree.eraseWP_caspTree` composes the node
  shapes for the whole `caspTree`.

These are standalone theorems: no `ResModel`, `Laws`, `NPSafe` or
`PromisedRelease` shape changes.
-/
import Kraken.Promising.SLR.LiftEvents

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## What a promised release fixes at promise time -/

/-- The **escrow** of a promised release, fixed when it is promised: the
release message (`key = (x, ts)`, value `val`), its slot set (one per
acquire id of `x` held in the total resource and per update id of `x`,
`SlotsFor` at the promise-time memory and view `ts`), and, for an RMW
release half, the message `read` it reads (claimed at promise time). -/
structure Escrow where
  key : Key
  val : Val
  slots : List Slot
  read : Option Time := none

/-- The ghost state holds the escrow `e`: its message is pending and in
release mode, its slots are in `u` (acquirable by readers of the outstanding
promise), and the message an RMW release half reads is claimed by it. -/
structure Escrow.Held (g : Ghost) (e : Escrow) : Prop where
  pend : e.key.2 ∈ g.pend
  rel : e.key ∈ g.relMsgs
  slots : ∀ s ∈ e.slots, s ∈ g.u ∧ s.key = e.key
  claim : ∀ tr, e.read = some tr → ((e.key.1, tr), e.key.2) ∈ g.claims

/-- The ghost state after a prepaid release store of `x` at `ts` with slots
`ss`: the release event's effect (`storeGhost`), and `ts` pending. -/
def prepayGhost (g : Ghost) (x : Loc) (ts : Time) (ss : List Slot) : Ghost :=
  { storeGhost g x ts true ss with pend := ts :: g.pend }

/-- The ghost state after a prepaid release RMW half that reads `(x, tr)`
and writes at `ts`: the release event's effect (`rmwGhost`: the update slots
of `(x, tr)` claimed), and `ts` pending. -/
def prepayRmwGhost (g : Ghost) (x : Loc) (tr ts : Time) (ss : List Slot) : Ghost :=
  { rmwGhost g x tr ts true ss with pend := ts :: g.pend }

/-- The ghost state after the pending promise `ts` is fulfilled. -/
abbrev unpend (g : Ghost) (ts : Time) : Ghost := { g with pend := g.pend.filter (· != ts) }

theorem mem_unpend_pend {g : Ghost} {ts p : Time} : p ∈ (unpend g ts).pend ↔ p ∈ g.pend ∧ p ≠ ts := by
  simp [List.mem_filter]

theorem slotsFor_unpend {g : Ghost} {ts : Time} {A : Loc → PredId → Nat} {x : Loc} {tw : Time} {v : Val}
    {m : Memory} {ss : List Slot} : SlotsFor (unpend g ts) A x tw v m ss ↔ SlotsFor g A x tw v m ss :=
  ⟨fun h => ⟨h.ids, h.key, h.pred⟩, fun h => ⟨h.ids, h.key, h.pred⟩⟩

theorem prepayGhost_held {g : Ghost} {x : Loc} {ts : Time} {v : Val} {ss : List Slot}
    (hk : ∀ s ∈ ss, s.key = (x, ts)) : Escrow.Held (prepayGhost g x ts ss) ⟨(x, ts), v, ss, none⟩ where
  pend := List.mem_cons_self
  rel := by simp [prepayGhost, storeGhost]
  slots s hs := ⟨by simp [prepayGhost, storeGhost, hs], hk s hs⟩
  claim _ h := by cases h

theorem prepayRmwGhost_held {g : Ghost} {x : Loc} {tr ts : Time} {v : Val} {ss : List Slot}
    (hk : ∀ s ∈ ss, s.key = (x, ts)) : Escrow.Held (prepayRmwGhost g x tr ts ss) ⟨(x, ts), v, ss, some tr⟩ where
  pend := List.mem_cons_self
  rel := by simp [prepayRmwGhost, rmwGhost]
  slots s hs := ⟨by simp [prepayRmwGhost, rmwGhost, hs], hk s hs⟩
  claim _ h := by cases h; simp [prepayRmwGhost, rmwGhost]

/-! ## Helpers: outstanding promises after replacing one thread -/

section Helpers

variable {c : Config I} {tid : Nat}

/-- Outstanding promises of `c.withThread tid t₁ m`: those of `t₁` and of the
other threads of `c`. -/
theorem outstanding_withThread (hn : tid < c.threads.size) {t₁ : Thread I} {m : Memory} {p : Time} :
    Outstanding (c.withThread tid t₁ m) p ↔
      p ∈ t₁.prom ∨ ∃ (i : Nat) (t : Thread I), i ≠ tid ∧ c.threads[i]? = some t ∧ p ∈ t.prom := by
  constructor
  · rintro ⟨i, t, hi, hp⟩
    rw [Config.withThread_get? c t₁ m hn] at hi
    split at hi
    · next h => subst h; cases hi; exact .inl hp
    · next h => exact .inr ⟨i, t, Ne.symm h, hi, hp⟩
  · rintro (hp | ⟨i, t, hne, hi, hp⟩)
    · exact ⟨tid, t₁, by rw [Config.withThread_get? c t₁ m hn, ite_eq_left rfl], hp⟩
    · exact ⟨i, t, by rw [Config.withThread_get? c t₁ m hn, ite_eq_right (Ne.symm hne)]; exact hi, hp⟩

theorem read?_le_last' {m : Memory} {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) : t ≤ m.last := by
  unfold Memory.read? at h
  split at h
  · next h0 => subst h0; exact Nat.zero_le _
  · split at h
    · rename_i w hw; exact m.last_le_of_get?_eq_some hw
    · cases h

end Helpers

/-! ## Promise-time laws -/

section Prepay

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {t : Thread I} {w : Msg}

private theorem msg_with_tid (w : Msg) (tid : Nat) : ({ w with tid } : Msg) = ⟨w.loc, w.val, tid⟩ := by
  cases w; rfl

/-- The promised message, appended as a write event of `tid` that leaves its
promise set as it is (the promise step seen as "promise and fulfil at
once"). -/
theorem writeAt_promised (E : Erase rF g T c) (ht : c.threads[tid]? = some t) :
    WriteAt c tid t t (c.mem.append { w with tid }).1 (c.mem.last + 1) ⟨w.loc, w.val, tid⟩ where
  sub _ h := h
  gone h := by
    obtain ⟨w', hw', -⟩ := E.promWf tid t ht _ h
    have := c.mem.last_le_of_get?_eq_some hw'
    omega_t
  keep _ h _ := h
  tid := rfl
  cases := .inr ⟨by rw [msg_with_tid], rfl⟩

/-- The configuration after the promise has the same memory as the one after
the append, and `tid` has one more promise (`ts`). -/
theorem promSub_promised (ht : c.threads[tid]? = some t) :
    PromSub (Promised c tid t w) (c.withThread tid t (c.mem.append { w with tid }).1) where
  mem := rfl
  size := by simp only [Config.withThread_size]
  sub i t' hi := by
    rw [Config.withThread_get? c t _ (lt_size_of_get? ht)] at hi
    rw [promised_get? ht]
    split at hi
    · next h =>
      subst h; cases hi
      exact ⟨_, by rw [ite_eq_left rfl], fun p hp => List.mem_append_left _ hp⟩
    · next h => exact ⟨t', by rw [ite_eq_right h]; exact hi, fun p hp => hp⟩

/-- `promWf` after the promise. -/
theorem promWf_promised (E : Erase rF g T c) (ht : c.threads[tid]? = some t) :
    ∀ (i : Nat) (t' : Thread I), (Promised c tid t w).threads[i]? = some t' →
      ∀ p ∈ t'.prom, ∃ w', (Promised c tid t w).mem.get? p = some w' ∧ w'.tid = i := by
  intro i t' hi ts hts
  rw [promised_get? ht] at hi
  split at hi
  · next h =>
    subst h
    simp only [Option.some.injEq] at hi
    subst hi
    rcases List.mem_append.mp hts with h | h
    · obtain ⟨w', hw', htid⟩ := E.promWf tid t ht ts h
      exact ⟨w', (promised_get?_of_le (c.mem.last_le_of_get?_eq_some hw')).trans hw', htid⟩
    · rw [List.mem_singleton.mp h]
      exact ⟨_, promised_mem ▸ Memory.get?_append_last _ _, rfl⟩
  · obtain ⟨w', hw', htid⟩ := E.promWf i t' hi ts hts
    exact ⟨w', (promised_get?_of_le (c.mem.last_le_of_get?_eq_some hw')).trans hw', htid⟩

/-- `ts = |M| + 1` is pending after the promise, nothing else changes. -/
theorem pend_promised (E : Erase rF g T c) (ht : c.threads[tid]? = some t) (p : Time) :
    p ∈ (c.mem.last + 1) :: g.pend ↔
      p ∈ g.pend ∨ (Outstanding (Promised c tid t w) p ∧
        ¬ Outstanding (c.withThread tid t (c.mem.append { w with tid }).1) p) := by
  have hn := lt_size_of_get? ht
  have hV : ∀ q, Outstanding (c.withThread tid t (c.mem.append { w with tid }).1) q ↔ Outstanding c q := by
    intro q
    rw [outstanding_withThread hn]
    constructor
    · rintro (h | ⟨i, t', -, hi, h⟩)
      · exact ⟨tid, t, ht, h⟩
      · exact ⟨i, t', hi, h⟩
    · rintro ⟨i, t', hi, h⟩
      by_cases he : i = tid
      · subst he; rw [ht] at hi; cases hi; exact .inl h
      · exact .inr ⟨i, t', he, hi, h⟩
  have hnew : ¬ Outstanding c (c.mem.last + 1) := by
    rintro ⟨i, t', hi, h⟩
    obtain ⟨w', hw', -⟩ := E.promWf i t' hi _ h
    have := c.mem.last_le_of_get?_eq_some hw'
    omega_t
  rw [hV, outstanding_promised ht, List.mem_cons]
  constructor
  · rintro (rfl | h)
    · exact .inr ⟨.inr rfl, hnew⟩
    · exact .inl h
  · rintro (h | ⟨h | h, hn'⟩)
    · exact .inr h
    · exact absurd h hn'
    · exact .inl h

/-- No claimer is outstanding after the promise: claimers are performed
writes before it (`Erase.claimFulf`), and the new promise is above every
claimer. -/
theorem claimFulf_promised (E : Erase rF g T c) (ht : c.threads[tid]? = some t) :
    ∀ k tw, (k, tw) ∈ g.claims → ¬ Outstanding (Promised c tid t w) tw := by
  intro k tw hk ho
  obtain ⟨-, w', hw', -⟩ := E.claimsAt k tw hk
  have hle := c.mem.last_le_of_get?_eq_some hw'
  rcases (outstanding_promised ht).mp ho with h | h
  · exact E.claimFulf k tw hk h
  · omega_t

/-- No claim names the new message (claims are of messages below their
claimer, which is in memory). -/
theorem not_claimed_new (E : Erase rF g T c) (x : Loc) : ¬ g.Claimed (x, c.mem.last + 1) := by
  intro hc
  obtain ⟨⟨k, tw⟩, hk, hk1⟩ := List.mem_map.mp hc
  simp only at hk1
  subst hk1
  obtain ⟨hlt, w', hw', -⟩ := E.claimsAt _ tw hk
  have := c.mem.last_le_of_get?_eq_some hw'
  simp only at hlt
  omega_t

/-- **Promise-time law, release store** (fallback (iii)). Thread `tid` (state
`t`, the state just before the fulfilling
instruction `F` in the virtual configuration) promises `w` at
`ts = |M| + 1`. If it owns a write permission for `w.loc` and its resource
splits as `r' • Π ss` plus the write-set entry `(w.val, ts)`, where `ss` are
the slots of the release message (`SlotsFor` at the promise-time memory,
from `Erase.slotsFor` on the release rule's `R(v)`), then erasure holds after
the promise with the release event accounted (`prepayGhost`: the slots in
`u`, the message in release mode) and `ts` pending. `F` itself is not run:
its other events (a fresh high half, the other half of a `CASP`, a fresh
write before the release) happen when `F` really runs. `hown`: the thread's
other promises stay valid with the resource left (vacuous when `tid` is
exempt). The other threads' validity is automatic (slots only grow). -/
theorem Erase.prepay (E : Erase rF g T c) (ht : c.threads[tid]? = some t) {ss : List Slot} {r' : Res}
    (hpos : 0 < ((rF tid).wr w.loc).q)
    (hss : SlotsFor g (total rF g c).acq w.loc (c.mem.last + 1) w.val (c.mem.append { w with tid }).1 ss)
    (hres : r'.op (Res.prod (ss.map (·.res))) = (rF tid).addW w.loc (w.val, c.mem.last + 1))
    (hown : ¬ T tid → ∀ p ∈ t.prom, p ∉ g.pend → ∀ w', c.mem.get? p = some w' →
      mayWrite r' (storeGhost g w.loc (c.mem.last + 1) true ss) w'.loc) :
    Erase (setRes rF tid r') (prepayGhost g w.loc (c.mem.last + 1) ss) T (Promised c tid t w) := by
  have hn := lt_size_of_get? ht
  have hW := writeAt_promised (w := w) E ht
  have hpend : c.mem.last + 1 ∉ g.pend := fun h => by have := E.pend_le h; omega_t
  have E1 := E.store (rel := true) ht hW hpend hpos (fun _ => ⟨hss, not_claimed_new E _⟩) (fun h => by cases h) hres
    (by
      intro i t₁ hi hTi p hp hpd w' hw'
      rw [Config.withThread_get? c t _ hn] at hi
      split at hi
      · next h =>
        subst h; cases hi
        obtain ⟨w'', hw'', -⟩ := E.promWf tid t ht p hp
        rw [hW.pre.get? (c.mem.last_le_of_get?_eq_some hw''), hw''] at hw'
        obtain rfl := Option.some.inj hw'
        rw [setRes_self]
        exact hown hTi p hp hpd w'' hw''
      · next h =>
        obtain ⟨w'', hw'', -⟩ := E.promWf i t₁ hi p hp
        rw [hW.pre.get? (c.mem.last_le_of_get?_eq_some hw''), hw''] at hw'
        obtain rfl := Option.some.inj hw'
        rw [setRes_ne rF r' (Ne.symm h)]
        exact mayWrite_store (E.promValid i t₁ hi hTi p hp hpd w'' hw''))
  exact E1.unfulfil (promSub_promised ht) (promWf_promised E ht) (fun k tw hk => claimFulf_promised E ht k tw hk) (pend_promised E ht)

/-- `Erase.prepay` when the promising thread is exempt (as in `NPSafe`'s
erasure): no validity obligation. -/
theorem Erase.prepay_exempt (E : Erase rF g T c) (ht : c.threads[tid]? = some t) (hT : T tid)
    {ss : List Slot} {r' : Res} (hpos : 0 < ((rF tid).wr w.loc).q)
    (hss : SlotsFor g (total rF g c).acq w.loc (c.mem.last + 1) w.val (c.mem.append { w with tid }).1 ss)
    (hres : r'.op (Res.prod (ss.map (·.res))) = (rF tid).addW w.loc (w.val, c.mem.last + 1)) :
    Erase (setRes rF tid r') (prepayGhost g w.loc (c.mem.last + 1) ss) T (Promised c tid t w) :=
  E.prepay ht hpos hss hres fun h => absurd hT h

end Prepay

/-! ## `F`-time laws: fulfilling a pending promise -/

section Fulfil

variable {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I} {tid : Nat} {r : Res} {g : Ghost}
  {cx cx' : Ctx}

/-- **A write event fulfilling a pending promise keeps erasure** (`F`-time
law of fallback (iii), context level): the resource and every other ghost
component are unchanged, `tw` leaves `pend`. The release event of a prepaid
`F` is such an event; its effect was accounted at promise time
(`Erase.prepay`). -/
theorem ErAt.fulfilPend (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size) (hi : cx.Inv tid)
    {l : Loc} {v : Val} {trOpt : Option Time} {tw : Time} (hev : WriteEv tid cx cx' l v trOpt tw)
    (hpend : tw ∈ g.pend) : ErAt rF T c t tid r (unpend g tw) cx' := by
  have hmemC : (c.withThread tid { t with prom := cx.prom } cx.mem).mem = cx.mem := rfl
  obtain ⟨hm, htp, hget⟩ : cx'.mem = cx.mem ∧ tw ∈ cx.prom ∧ cx.mem.get? tw = some ⟨l, v, tid⟩ := by
    rcases hev.cases with h | ⟨-, rfl⟩
    · exact h
    · have := E.pend_le hpend; rw [hmemC] at this; omega_t
  -- outstanding promises before and after
  have hO : ∀ p, Outstanding (c.withThread tid { t with prom := cx.prom } cx.mem) p ↔
      p ∈ cx.prom ∨ ∃ (i : Nat) (t' : Thread I), i ≠ tid ∧ c.threads[i]? = some t' ∧ p ∈ t'.prom :=
    fun p => outstanding_withThread hn
  have hO' : ∀ p, Outstanding (c.withThread tid { t with prom := cx'.prom } cx'.mem) p ↔
      p ∈ cx.prom.erase tw ∨ ∃ (i : Nat) (t' : Thread I), i ≠ tid ∧ c.threads[i]? = some t' ∧ p ∈ t'.prom := by
    intro p; rw [outstanding_withThread hn, hev.prom]
  -- `tw` is not another thread's promise (its message is `tid`'s)
  have hnot : ¬ Outstanding (c.withThread tid { t with prom := cx'.prom } cx'.mem) tw := by
    rw [hO']
    rintro (h | ⟨i, t', hne, hi', h⟩)
    · exact ((List.Nodup.mem_erase_iff hi.nodup).mp h).1 rfl
    · have hC : (c.withThread tid { t with prom := cx.prom } cx.mem).threads[i]? = some t' := by
        rw [Config.withThread_get? c _ _ hn, ite_eq_right (Ne.symm hne)]; exact hi'
      obtain ⟨w', hw', htid⟩ := E.promWf i t' hC tw h
      rw [hmemC, hget] at hw'
      cases hw'
      exact hne htid.symm
  have hkeep : ∀ p, p ≠ tw → Outstanding (c.withThread tid { t with prom := cx.prom } cx.mem) p →
      Outstanding (c.withThread tid { t with prom := cx'.prom } cx'.mem) p := by
    intro p hne h
    rw [hO] at h; rw [hO']
    rcases h with h | h
    · exact .inl ((List.mem_erase_of_ne hne).mpr h)
    · exact .inr h
  have hsub : PromSub (c.withThread tid { t with prom := cx.prom } cx.mem)
      (c.withThread tid { t with prom := cx'.prom } cx'.mem) := by
    refine ⟨hm, by simp only [Config.withThread_size], fun i t' hi' => ?_⟩
    rw [Config.withThread_get? c _ _ hn] at hi'
    split at hi'
    · next h =>
      subst h; cases hi'
      refine ⟨{ t with prom := cx.prom }, by rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl], ?_⟩
      intro p hp
      rw [hev.prom] at hp
      exact List.mem_of_mem_erase hp
    · next h => exact ⟨t', by rw [Config.withThread_get? c _ _ hn, ite_eq_right h]; exact hi', fun p hp => hp⟩
  have E' := Erase.fulfil (pend' := (unpend g tw).pend) E hsub
    (fun p ho hno => by
      by_cases hp : p = tw
      · exact hp ▸ hpend
      · exact absurd (hkeep p hp ho) hno)
    (fun p => by
      rw [mem_unpend_pend]
      constructor
      · rintro ⟨hp, hne⟩
        exact ⟨hp, hkeep p hne (E.pend p hp).2⟩
      · rintro ⟨hp, ho⟩
        exact ⟨hp, fun he => hnot (he ▸ ho)⟩)
  exact E'

/-- **Uniqueness of claims, location-wise.** S2b's `Erase.not_claimed` with
`hnp` ("no pending promise of the thread") weakened to "no pending promise
of the thread *to `x`*": a pending claimer of `(x, tr)` writes `x`. This is
what the other half of a prepaid `CASP` needs (the pending release half is
to the other location). -/
theorem Erase.not_claimed_loc {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {t t' : Thread I} {mem' : Memory} {x : Loc} {tr tw : Time} {w : Msg}
    (ht : c.threads[tid]? = some t) (hw : WriteAt c tid t t' mem' tw w) (hl : w.loc = x)
    (htr : tr < tw) {old : Val} (hrd : c.mem.read? x tr = some old) (hat : c.mem.atomic x tid tr tw = true)
    (hnp : ∀ p ∈ t.prom, p ∈ g.pend → ∀ w', c.mem.get? p = some w' → w'.loc ≠ x)
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
    · exact hnp tw' hp hs w'' hw'' hl''
  · have := hseen tw' w'' hw'' hl'' hj hp
    omega_t

/-- **The RMW obligation of the erasure WP with a pending promise elsewhere**
(context level): S2b/S2c's `ErAt.rmw` with `hnp` weakened to "no pending
promise of the thread to `l`" and the write itself not pending. Used for the
other half of a `CASP` whose release half is prepaid. -/
theorem ErAt.rmw_loc (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size) (hi : cx.Inv tid)
    {l : Loc} {new old : Val} {tr tw : Time} (hev : WriteEv tid cx cx' l new (some tr) tw)
    (hrd : cx.mem.read? l tr = some old)
    (hseen : ∀ ts w, cx.mem.get? ts = some w → w.loc = l → w.tid = tid → ts ∉ cx.prom → ts ≤ tr)
    (hnp : ∀ p ∈ cx.prom, p ∈ g.pend → ∀ w, cx.mem.get? p = some w → w.loc ≠ l) (hpend : tw ∉ g.pend)
    (hpos : 0 < (r.wr l).q) {rel : Bool} {ss : List Slot}
    (hrel : rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw new cx'.mem ss ∧ ¬ g.Claimed (l, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel l) new)
    {r' : Res} (hres : r'.op (Res.prod (ss.map (·.res))) =
      (r.op (Res.prod ((claimedSlots g l tr).map (·.res)))).addW l (new, tw))
    (hval : HVal rF T c t tid cx' r' (rmwGhost g l tr tw rel ss)) :
    ErAt rF T c t tid r' (rmwGhost g l tr tw rel ss) cx' := by
  obtain ⟨htr, hat⟩ := hev.tr tr rfl
  have hW := hev.writeAt (c := c) (t := t) hi
  have hun := Erase.not_claimed_loc E (ErAt.get? hn) hW rfl htr hrd hat hnp hseen
  have E' := Erase.rmw E (ErAt.get? hn) hW htr hrd hat hpend hun
    (by rw [setRes_self]; exact hpos) (by rw [total_withThread]; exact hrel) hrlx (r' := r')
    (by rw [setRes_self]; exact hres) (by rw [setRes_setRes, Config.withThread_withThread]; exact hval)
  unfold ErAt
  rw [setRes_setRes, Config.withThread_withThread] at E'
  exact E'

end Fulfil

/-! ## Erasure-WP node shapes with the pending branch discharged -/

section Shapes

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- **A store, with pending promises** (fallback (iii)): a write event that
fulfils a pending promise needs only the continuation's WP, with the same
resource and the promise unpended (`ErAt.fulfilPend`); every other write
event needs the store rule's preconditions, as in `EvTree.eraseWP_store`.
(Write events that leave a pending promise of the thread dead are among the
latter: they are vacuous only through `NPSafe`'s `c'.WfProm`, "Limits" (2).) -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_store_pend (hn : tid < c.threads.size) {k : StoreKind} {l : Loc}
    {v : Val} {ret : Bool → EvTree σ}
    (hp : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∈ g.pend →
      (ret true).EraseWP A tid iv rF T c t Post r (unpend g tw) cx')
    (h : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∉ g.pend → ErAt rF T c t tid r g cx → cx.Inv tid →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res), 0 < (r.wr l).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw v cx'.mem ss ∧ ¬ g.Claimed (l, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel l) v) ∧
        r'.op (Res.prod (ss.map (·.res))) = r.addW l (v, tw) ∧
        HVal rF T c t tid cx' r' (storeGhost g l tw rel ss) ∧
        (ret true).EraseWP A tid iv rF T c t Post r' (storeGhost g l tw rel ss) cx') :
    (EvTree.store k false l v ret).EraseWP A tid iv rF T c t Post r g cx := by
  refine ⟨fun cx' hc E hi => ?_, fun h => absurd h (by decide)⟩
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi
  by_cases hpd : tw ∈ g.pend
  · exact ⟨r, _, ErAt.fulfilPend E hn hi hev hpd, hp cx' tw hc hev hpd⟩
  · obtain ⟨rel, ss, r', hpos, hrel, hrlx, hres, hval, hwp⟩ := h cx' tw hc hev hpd E hi
    exact ⟨r', _, ErAt.store E hn hi hev hpd hpos hrel hrlx hres hval, hwp⟩

/-- **An RMW, with pending promises** (fallback (iii)): a successful RMW
whose write fulfils a pending promise (a prepaid release half) needs only
the continuation's WP with the same resource; any other successful write
needs `ErAt.rmw_loc`'s preconditions (no pending promise of the thread *to
`l`*, so the other half of a prepaid `CASP` qualifies); a failed RMW only
reads. -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_rmw_pend (hn : tid < c.threads.size) {k : RmwKind} {noRet : Bool}
    {l : Loc} {op : Val → Option Val} {ret : Val → EvTree σ}
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
        (∀ p ∈ x.2.2.prom, p ∈ g.pend → ∀ w, x.2.2.mem.get? p = some w → w.loc ≠ l) ∧ 0 < (r.wr l).q ∧
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
    exact ⟨r', _, ErAt.rmw_loc E hn hi2 hev hrd hseen hnp hpd hpos hrel hrlx hres hval, hwp⟩


end Shapes

/-! ## The two-event shapes of a prepaid instruction

Event sequences, in the order the instruction performs them; `cx → cx₁ →
cx₂` are the contexts around its two write events. The prepaid release is
`ts` (pending, `Erase.prepay`); the other write is at `tw`, not pending
(fresh, or fulfilling an ordinary promise). -/

section TwoEvents

variable {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I} {tid : Nat} {r : Res} {g : Ghost}
  {cx cx₁ cx₂ : Ctx}

theorem total_unpend (rF : Nat → Res) (g : Ghost) (ts : Time) (c : Config I) :
    total rF (unpend g ts) c = total rF g c := rfl

/-- **Two stores, prepaid release first** (x64 `movups`/`vmovdqu`: low half
the prepaid release, high half after it; `STLXP`). The release event
fulfils the pending `ts` with the resource unchanged; the second store is an
ordinary store rule (`ErAt.store`), on the real memory. -/
theorem ErAt.store2_prepaidFirst (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size)
    (hi : cx.Inv tid) (hi₁ : cx₁.Inv tid)
    {l₁ l₂ : Loc} {v₁ v₂ : Val} {ts tw : Time}
    (hev₁ : WriteEv tid cx cx₁ l₁ v₁ none ts) (hts : ts ∈ g.pend)
    (hev₂ : WriteEv tid cx₁ cx₂ l₂ v₂ none tw) (hpend : tw ∉ g.pend) (hpos : 0 < (r.wr l₂).q)
    {rel : Bool} {ss : List Slot}
    (hrel : rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l₂ tw v₂ cx₂.mem ss ∧ ¬ g.Claimed (l₂, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel l₂) v₂)
    {r' : Res} (hres : r'.op (Res.prod (ss.map (·.res))) = r.addW l₂ (v₂, tw))
    (hval : HVal rF T c t tid cx₂ r' (storeGhost (unpend g ts) l₂ tw rel ss)) :
    ErAt rF T c t tid r' (storeGhost (unpend g ts) l₂ tw rel ss) cx₂ :=
  ErAt.store (ErAt.fulfilPend E hn hi hev₁ hts) hn hi₁ hev₂ (fun h => hpend (mem_unpend_pend.mp h).1) hpos
    (fun h => ⟨slotsFor_unpend.mpr (hrel h).1, (hrel h).2⟩) hrlx hres hval

/-- **Two stores, prepaid release last, after a fresh store** (an
instruction whose release store follows a fresh append). The first store is
an ordinary store rule; the release event then fulfils the pending `ts`. -/
theorem ErAt.store2_prepaidLast (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size)
    (hi : cx.Inv tid) (hi₁ : cx₁.Inv tid)
    {l₁ l₂ : Loc} {v₁ v₂ : Val} {tw ts : Time}
    (hev₁ : WriteEv tid cx cx₁ l₁ v₁ none tw) (hpend : tw ∉ g.pend) (hpos : 0 < (r.wr l₁).q)
    {rel : Bool} {ss : List Slot}
    (hrel : rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l₁ tw v₁ cx₁.mem ss ∧ ¬ g.Claimed (l₁, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel l₁) v₁)
    {r' : Res} (hres : r'.op (Res.prod (ss.map (·.res))) = r.addW l₁ (v₁, tw))
    (hval : HVal rF T c t tid cx₁ r' (storeGhost g l₁ tw rel ss))
    (hev₂ : WriteEv tid cx₁ cx₂ l₂ v₂ none ts) (hts : ts ∈ g.pend) :
    ErAt rF T c t tid r' (unpend (storeGhost g l₁ tw rel ss) ts) cx₂ :=
  ErAt.fulfilPend (ErAt.store E hn hi hev₁ hpend hpos hrel hrlx hres hval) hn hi₁ hev₂ hts

/-- **The two halves of a `CASP`, prepaid release half first.** The release
half's write fulfils the pending `ts` (its read was accounted at promise
time; the claim-at-promise law `Erase.prepayRmw` is retired, see the module
doc); the other half is an RMW rule on the real memory,
which needs only that the thread has no pending promise *to its location*
(`ErAt.rmw_loc`). -/
theorem ErAt.rmw2_prepaidFirst (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size)
    (hi : cx.Inv tid) (hi₁ : cx₁.Inv tid)
    {l₁ l₂ : Loc} {v₁ v₂ old₂ : Val} {tr₁ ts tr₂ tw : Time}
    (hev₁ : WriteEv tid cx cx₁ l₁ v₁ (some tr₁) ts) (hts : ts ∈ g.pend)
    (hev₂ : WriteEv tid cx₁ cx₂ l₂ v₂ (some tr₂) tw) (hrd : cx₁.mem.read? l₂ tr₂ = some old₂)
    (hseen : ∀ ts' w, cx₁.mem.get? ts' = some w → w.loc = l₂ → w.tid = tid → ts' ∉ cx₁.prom → ts' ≤ tr₂)
    (hnp : ∀ p ∈ cx₁.prom, p ∈ g.pend → ∀ w, cx₁.mem.get? p = some w → w.loc ≠ l₂) (hpend : tw ∉ g.pend)
    (hpos : 0 < (r.wr l₂).q) {rel : Bool} {ss : List Slot}
    (hrel : rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l₂ tw v₂ cx₂.mem ss ∧ ¬ g.Claimed (l₂, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel l₂) v₂)
    {r' : Res} (hres : r'.op (Res.prod (ss.map (·.res))) =
      (r.op (Res.prod ((claimedSlots g l₂ tr₂).map (·.res)))).addW l₂ (v₂, tw))
    (hval : HVal rF T c t tid cx₂ r' (rmwGhost (unpend g ts) l₂ tr₂ tw rel ss)) :
    ErAt rF T c t tid r' (rmwGhost (unpend g ts) l₂ tr₂ tw rel ss) cx₂ :=
  ErAt.rmw_loc (ErAt.fulfilPend E hn hi hev₁ hts) hn hi₁ hev₂ hrd hseen
    (fun p hp hpd => hnp p hp (mem_unpend_pend.mp hpd).1) (fun h => hpend (mem_unpend_pend.mp h).1) hpos
    (fun h => ⟨slotsFor_unpend.mpr (hrel h).1, (hrel h).2⟩) hrlx hres hval

/-- **The two halves of a `CASP`, prepaid release half last**, after the
other half (fresh, or fulfilling an ordinary promise): an RMW rule with a
pending promise elsewhere (`ErAt.rmw_loc`), then the release half fulfils
the pending `ts`. -/
theorem ErAt.rmw2_prepaidLast (E : ErAt rF T c t tid r g cx) (hn : tid < c.threads.size)
    (hi : cx.Inv tid) (hi₁ : cx₁.Inv tid)
    {l₁ l₂ : Loc} {v₁ v₂ old₁ : Val} {tr₁ tw tr₂ ts : Time}
    (hev₁ : WriteEv tid cx cx₁ l₁ v₁ (some tr₁) tw) (hrd : cx.mem.read? l₁ tr₁ = some old₁)
    (hseen : ∀ ts' w, cx.mem.get? ts' = some w → w.loc = l₁ → w.tid = tid → ts' ∉ cx.prom → ts' ≤ tr₁)
    (hnp : ∀ p ∈ cx.prom, p ∈ g.pend → ∀ w, cx.mem.get? p = some w → w.loc ≠ l₁) (hpend : tw ∉ g.pend)
    (hpos : 0 < (r.wr l₁).q) {rel : Bool} {ss : List Slot}
    (hrel : rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l₁ tw v₁ cx₁.mem ss ∧ ¬ g.Claimed (l₁, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel l₁) v₁)
    {r' : Res} (hres : r'.op (Res.prod (ss.map (·.res))) =
      (r.op (Res.prod ((claimedSlots g l₁ tr₁).map (·.res)))).addW l₁ (v₁, tw))
    (hval : HVal rF T c t tid cx₁ r' (rmwGhost g l₁ tr₁ tw rel ss))
    (hev₂ : WriteEv tid cx₁ cx₂ l₂ v₂ (some tr₂) ts) (hts : ts ∈ g.pend) :
    ErAt rF T c t tid r' (unpend (rmwGhost g l₁ tr₁ tw rel ss) ts) cx₂ :=
  ErAt.fulfilPend (ErAt.rmw_loc E hn hi hev₁ hrd hseen hnp hpend hpos hrel hrlx hres hval) hn hi₁ hev₂ hts

end TwoEvents

end Kraken.Promising.SLR
