/-
The RMW extension of the SLR-adapted resource model.

SLR has no RMWs, and its one-shot exclusive `Acq(x, φ)` forbids two threads
from acquiring the same message. With RMWs the machine guarantees that at
most one successful RMW reads from each message (`Memory.atomic`), so the
reader of a message by RMW may take the message's *update slots* whole
(FSL++'s duplicable `RMWAcq`). `Ghost.upd`, `Ghost.claims` and the erasure
clauses `updIds`, `relSettled`, `claimsNodup`, `claimsAt` (in
`Erasure.lean`) record this; this file proves the event-level step lemmas.

## Contents

- `Res.addW`: a write permission's write set gains the message just written.
- `WriteAt`: the effect of one write event of thread `tid` on the memory and
  its promise set (fulfil an outstanding promise, or append at `|M| + 1`).
- `Erase.not_claimed`: **uniqueness**. The message an RMW reads is not yet
  claimed: the memory half is `claimsAt` with the RMW's `atomic` check, the
  thread half is `OwnSeen` (the thread has no performed write to the
  location above the message it reads), which follows from `readSuccs` and
  the machine invariant `OwnCoh` (`ownSeen_of_readSuccs`).
- `Erase.rmw`: **the RMW step lemma** at event level. From erasure before a
  successful RMW event (read `tr`, write `tw`) with the rule's precondition
  (a write permission for `x`; for a relaxed write a pure value, for a
  release write the slots of the new message), erasure after it, with the
  update slots of `(x, tr)` moved to the thread and the claim recorded.
  Every RMW rule (acquire / release / acq-rel /
  relaxed update, `noRet`, each half of `CASP`) has this as its erasure
  part: erasure sees neither views nor access kinds.
- `Erase.sameProm`: a step that changes neither memory nor the thread's
  promise set keeps erasure (the read of a **failed CAS**: no claim).
- `Erase.rmw_of_seen`: `Erase.rmw` with uniqueness discharged.
- `mayWrite_rmw_of_noClaim`, `Erase.hval_of_noClaim`: the other threads'
  promise validity after an RMW that claims no slot (the `hval` hypothesis of
  `Erase.rmw` in that case; in general `hval` is Theorem 1′'s path-relative
  condition (3), R3).
-/
import Kraken.Promising.SLR.Virtual

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Adding a write to a write set -/

namespace Perm

/-- `(π, X) ↦ (π, X ∪ {p})` (only for `π > 0`: a zero permission has an empty
write set). -/
def addW (a : Perm) (p : Val × Time) : Perm where
  q := a.q
  X p' := a.X p' ∨ (0 < a.q ∧ p' = p)
  nonneg := a.nonneg
  zero h p' hp := by
    rcases hp with hp | ⟨hq, -⟩
    · exact a.zero h p' hp
    · rw [h] at hq; exact Rat.lt_irrefl hq

theorem addW_op {a : Perm} (b : Perm) (p : Val × Time) (h : 0 < a.q) : (a.addW p).op b = (a.op b).addW p := by
  have hb := b.nonneg
  have h2 : 0 < a.q + b.q := by grind
  apply ext
  · rfl
  · funext p'
    simp only [op, addW, h, h2, true_and]
    apply propext
    grind

end Perm

namespace Res

/-- The write set of `x` gains `p`. -/
def addW (r : Res) (x : Loc) (p : Val × Time) : Res :=
  ⟨fun y => if y = x then (r.wr y).addW p else r.wr y, r.acq⟩

@[simp] theorem addW_acq (r : Res) (x : Loc) (p : Val × Time) : (r.addW x p).acq = r.acq := rfl

@[simp] theorem addW_q (r : Res) (x y : Loc) (p : Val × Time) : ((r.addW x p).wr y).q = (r.wr y).q := by
  simp only [addW]; split <;> rfl

theorem addW_wr_ne (r : Res) {x y : Loc} (p : Val × Time) (h : y ≠ x) : (r.addW x p).wr y = r.wr y := by
  simp only [addW, h, ↓reduceIte]

theorem addW_X_self (r : Res) (x : Loc) (p p' : Val × Time) :
    ((r.addW x p).wr x).X p' ↔ (r.wr x).X p' ∨ (0 < (r.wr x).q ∧ p' = p) := by
  simp only [addW, ↓reduceIte, Perm.addW]

theorem valid_addW (r : Res) (x : Loc) (p : Val × Time) : (r.addW x p).valid ↔ r.valid := by
  simp only [valid, addW_q, addW_acq]

theorem addW_op {a : Res} (b : Res) {x : Loc} (p : Val × Time) (h : 0 < (a.wr x).q) :
    (a.addW x p).op b = (a.op b).addW x p := by
  apply ext
  · funext y
    simp only [op, addW]
    split
    · next hy => subst hy; exact Perm.addW_op _ _ h
    · rfl
  · rfl

end Res

/-! ## Thread resources -/

/-- `rF[tid ↦ r]` (`ResModel.upd` of `model I`, definitionally). -/
def setRes (rF : Nat → Res) (tid : Nat) (r : Res) : Nat → Res := fun i => if i = tid then r else rF i

theorem setRes_eq_upd (rF : Nat → Res) (tid : Nat) (r : Res) : setRes rF tid r = (model I).upd rF tid r := rfl

@[simp] theorem setRes_self (rF : Nat → Res) (tid : Nat) (r : Res) : setRes rF tid r tid = r := by
  simp [setRes]

theorem setRes_ne (rF : Nat → Res) {tid i : Nat} (r : Res) (h : i ≠ tid) : setRes rF tid r i = rF i := by
  simp [setRes, h]

/-- The other threads' share of `Π_i rF(i)`. -/
theorem threadsRes_split (rF : Nat → Res) {tid : Nat} : ∀ {n : Nat}, tid < n →
    ∃ rest, ∀ f : Nat → Res, (∀ i, i ≠ tid → f i = rF i) → threadsRes f n = (f tid).op rest
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rcases Nat.lt_or_ge tid n with hlt | hge
    · obtain ⟨rest, hrest⟩ := threadsRes_split rF hlt
      refine ⟨rest.op (rF n), fun f hf => ?_⟩
      have hn : f n = rF n := hf n (by omega)
      simp only [threadsRes, List.range_succ, List.map_append, Res.prod_append, List.map_cons, List.map_nil,
        Res.prod_cons, Res.prod_nil, Res.op_unit] at hrest ⊢
      rw [hrest f hf, hn, Res.op_assoc]
    · have htid : tid = n := by omega
      subst htid
      refine ⟨Res.prod ((List.range tid).map rF), fun f hf => ?_⟩
      have hmap : (List.range tid).map f = (List.range tid).map rF :=
        List.map_congr_left fun i hi => hf i (by simp at hi; omega)
      simp only [threadsRes, List.range_succ, List.map_append, Res.prod_append, List.map_cons, List.map_nil,
        Res.prod_cons, Res.prod_nil, Res.op_unit, hmap]
      exact Res.op_comm _ _

/-! ## One write event of a thread -/

/-- The effect on memory and on its promise set of a write event of thread
`tid` (state `t` before, `t'` after the instruction) writing the message `w`
at `tw`: either it fulfils the outstanding promise `tw` (memory unchanged)
or it appends `w` at `|M| + 1` ("promise now"); the thread's promise set
loses exactly `tw`. -/
structure WriteAt (c : Config I) (tid : Nat) (t t' : Thread I) (mem' : Memory) (tw : Time) (w : Msg) : Prop where
  sub : ∀ p ∈ t'.prom, p ∈ t.prom
  gone : tw ∉ t'.prom
  keep : ∀ p ∈ t.prom, p ≠ tw → p ∈ t'.prom
  tid : w.tid = tid
  cases : (mem' = c.mem ∧ tw ∈ t.prom ∧ c.mem.get? tw = some w) ∨ (mem' = (c.mem.append w).1 ∧ tw = c.mem.last + 1)

namespace WriteAt

variable {c : Config I} {tid : Nat} {t t' : Thread I} {mem' : Memory} {tw : Time} {w : Msg}

theorem pre (h : WriteAt c tid t t' mem' tw w) : c.mem.Prefix mem' := by
  rcases h.cases with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Memory.Prefix.refl _
  · exact Memory.Prefix.append _ _

theorem get?_iff (h : WriteAt c tid t t' mem' tw w) {ts : Time} {w' : Msg} :
    mem'.get? ts = some w' ↔ c.mem.get? ts = some w' ∨ (ts = tw ∧ w' = w) := by
  rcases h.cases with ⟨rfl, -, hg⟩ | ⟨rfl, rfl⟩
  · constructor
    · exact .inl
    · rintro (h | ⟨rfl, rfl⟩)
      · exact h
      · exact hg
  · constructor
    · intro h'
      rcases Memory.get?_append_eq_some _ _ h' with ⟨-, h'⟩ | ⟨h1, h2⟩
      · exact .inl h'
      · exact .inr ⟨h1, h2⟩
    · rintro (h' | ⟨rfl, rfl⟩)
      · exact (Memory.Prefix.append _ _).get? (c.mem.last_le_of_get?_eq_some h') ▸ h'
      · exact Memory.get?_append_last _ _

theorem get?_tw (h : WriteAt c tid t t' mem' tw w) : mem'.get? tw = some w := h.get?_iff.mpr (.inr ⟨rfl, rfl⟩)

theorem tw_ne_zero (h : WriteAt c tid t t' mem' tw w) : tw ≠ 0 := by
  intro h0
  have := h.get?_tw
  rw [h0] at this
  simp [Memory.get?] at this

theorem old_tw (h : WriteAt c tid t t' mem' tw w) {w' : Msg} (hw' : c.mem.get? tw = some w') : w' = w := by
  rcases h.cases with ⟨-, -, hg⟩ | ⟨-, rfl⟩
  · exact Option.some.inj (hw'.symm.trans hg)
  · rw [Memory.get?_eq_none_of_last_lt _ (Nat.lt_succ_self _)] at hw'; cases hw'

theorem get?_ne (h : WriteAt c tid t t' mem' tw w) {ts : Time} (hne : ts ≠ tw) : mem'.get? ts = c.mem.get? ts := by
  apply Option.ext
  intro w'
  rw [h.get?_iff]
  constructor
  · rintro (h' | ⟨h', -⟩)
    · exact h'
    · exact absurd h' hne
  · exact .inl

theorem read?_ne (h : WriteAt c tid t t' mem' tw w) {ts : Time} (hne : ts ≠ tw) (x : Loc) :
    mem'.read? x ts = c.mem.read? x ts := by
  unfold Memory.read?
  rw [h.pre.initVal, h.get?_ne hne]

theorem read?_tw (h : WriteAt c tid t t' mem' tw w) {x : Loc} {v : Val} (hv : mem'.read? x tw = some v) :
    x = w.loc ∧ v = w.val := by
  unfold Memory.read? at hv
  rw [ite_eq_right h.tw_ne_zero, h.get?_tw] at hv
  by_cases hb : w.loc = x
  · simp [hb] at hv; exact ⟨hb.symm, hv.symm⟩
  · simp [hb] at hv

theorem read?_tw_self (h : WriteAt c tid t t' mem' tw w) : mem'.read? w.loc tw = some w.val := by
  simp [Memory.read?, h.tw_ne_zero, h.get?_tw]

theorem lt_size (ht : c.threads[tid]? = some t) : tid < c.threads.size := lt_size_of_get? ht

/-- After the write, `tw` is no longer outstanding, everything else is as
before. -/
theorem outstanding_iff {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} (E : Erase rF g T c)
    (ht : c.threads[tid]? = some t) (h : WriteAt c tid t t' mem' tw w) {p : Time} :
    Outstanding (c.withThread tid t' mem') p ↔ Outstanding c p ∧ p ≠ tw := by
  have hget := fun i => Config.withThread_get? c (i := i) t' mem' (lt_size_of_get? ht)
  constructor
  · rintro ⟨i, t₁, hi, hp⟩
    rw [hget] at hi
    split at hi
    · next hti =>
      subst hti
      simp only [Option.some.injEq] at hi
      subst hi
      exact ⟨⟨tid, t, ht, h.sub p hp⟩, fun he => h.gone (he ▸ hp)⟩
    · next hti =>
      refine ⟨⟨i, t₁, hi, hp⟩, fun he => ?_⟩
      subst he
      obtain ⟨w', hw', htid⟩ := E.promWf i t₁ hi p hp
      have := h.old_tw hw'
      subst this
      exact hti (h.tid.symm.trans htid)
  · rintro ⟨⟨i, t₁, hi, hp⟩, hne⟩
    by_cases hti : tid = i
    · subst hti
      rw [ht] at hi; cases hi
      exact ⟨tid, t', by rw [hget, ite_eq_left rfl], h.keep p hp hne⟩
    · exact ⟨i, t₁, by rw [hget, ite_eq_right hti]; exact hi, hp⟩

theorem settled_iff {rF : Nat → Res} {g g' : Ghost} {T : Nat → Prop} (E : Erase rF g T c)
    (ht : c.threads[tid]? = some t) (h : WriteAt c tid t t' mem' tw w) (hpend : g'.pend = g.pend) {p : Time} :
    Settled (c.withThread tid t' mem') g' p ↔ Settled c g p ∨ p = tw := by
  unfold Settled
  rw [outstanding_iff E ht h, hpend]
  constructor
  · rintro (h1 | h1)
    · by_cases hp : p = tw
      · exact .inr hp
      · exact .inl (.inl fun ho => h1 ⟨ho, hp⟩)
    · exact .inl (.inr h1)
  · rintro ((h1 | h1) | h1)
    · exact .inl fun ho => h1 ho.1
    · exact .inr h1
    · exact .inl fun ho => ho.2 h1

end WriteAt

/-! ## Uniqueness: the message an RMW reads is unclaimed -/

/-- `Memory.atomic`, unfolded: every message to `l` strictly between the read
`tr` and the write `tw` is by `tid`. -/
theorem atomic_between {m : Memory} {l : Loc} {tid : Nat} {tr tw : Time} (h : m.atomic l tid tr tw = true)
    {v : Val} (hr : m.read? l tr = some v) {ts : Time} {w : Msg} (h1 : tr < ts) (h2 : ts < tw)
    (hw : m.get? ts = some w) (hl : w.loc = l) : w.tid = tid := by
  unfold Memory.atomic at h
  rw [hr] at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h (ts - tr - 1) (by omega_t)
  rw [show tr + (ts - tr - 1) + 1 = ts by omega_t, hw] at h'
  simp only [hl, bne_self_eq_false, Bool.false_or, beq_iff_eq] at h'
  exact h'

/-- The thread half of uniqueness: thread `tid` (state `t`) has no performed
write to `x` above `tr` (its outstanding promises aside). -/
def OwnSeen (c : Config I) (tid : Nat) (t : Thread I) (x : Loc) (tr : Time) : Prop :=
  ∀ ts w, c.mem.get? ts = some w → w.loc = x → w.tid = tid → ts ∉ t.prom → ts ≤ tr

/-- The machine invariant behind `OwnSeen`, for an instruction context: every
message of thread `tid` that is not one of its outstanding promises is at
most its coherence view of the location. Holds of every thread of every
reachable configuration (a thread's writes raise its `coh`; only thread `tid`
writes messages with `tid`); it is a hypothesis of the RMW step lemma rather
than an erasure clause. -/
def _root_.Kraken.Promising.Ctx.OwnCoh (tid : Nat) (cx : Ctx) : Prop :=
  ∀ ts w, cx.mem.get? ts = some w → w.tid = tid → ts ∉ cx.prom → ts ≤ cx.views.getCoh w.loc

private theorem ite_none_some {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : ¬ p ∧ y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rw [ite_eq_right hp] at h; exact ⟨hp, h⟩

/-- A read cannot return a message below a write to its location in
`(tr, coh]`; with `OwnCoh`, the reader has no performed write above what it
reads. -/
theorem ownSeen_of_readSuccs (A : Arch) (iv : InstrViews) {tid : Nat} {cx : Ctx} {k : LoadKind} {xcl : Bool}
    {l : Loc} {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l noRet)
    (hoc : cx.OwnCoh tid) :
    ∀ ts w, cx.mem.get? ts = some w → w.loc = l → w.tid = tid → ts ∉ cx.prom → ts ≤ x.1 := by
  intro ts w hw hl htid hp
  have hcoh := hoc ts w hw htid hp
  rw [hl] at hcoh
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · obtain ⟨hc, ht⟩ := ite_none_some ht
    simp only [Option.some.injEq] at ht
    subst ht
    refine Nat.le_of_not_lt fun hlt => hc ?_
    rw [Bool.or_eq_true]
    exact .inl ((Memory.writeIn_iff _ _ _ _).mpr ⟨ts, w, hlt, Nat.le_trans hcoh (Nat.le_max_right _ _), hw, hl⟩)

/-- **Uniqueness of claims.** The message `(x, tr)` that a successful RMW of
thread `tid` reads (its write `w` at `tw`, checked `atomic`) is not claimed
yet. A claimer of another thread would lie between `tr` and `tw` (or have
`tw` between it and `tr`), which `atomic` resp. `claimsAt` forbids; a
claimer of `tid` itself is a performed write of `tid` above `tr`, which
`OwnSeen` forbids, or a pending one, excluded by `hnp`. -/
theorem Erase.not_claimed {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {tid : Nat} {t t' : Thread I} {mem' : Memory} {x : Loc} {tr tw : Time} {w : Msg}
    (ht : c.threads[tid]? = some t) (hw : WriteAt c tid t t' mem' tw w) (hl : w.loc = x)
    (htr : tr < tw) {old : Val} (hrd : c.mem.read? x tr = some old) (hat : c.mem.atomic x tid tr tw = true)
    (hnp : ∀ p ∈ t.prom, p ∉ g.pend) (hseen : OwnSeen c tid t x tr) : ¬ g.Claimed (x, tr) := by
  intro hc
  obtain ⟨⟨k, tw'⟩, hk, hk1⟩ := List.mem_map.mp hc
  simp only at hk1
  subst hk1
  obtain ⟨hlt, w'', hw'', hl'', hs, hb⟩ := E.claimsAt _ tw' hk
  simp only at hlt hl'' hb
  have hle' := c.mem.last_le_of_get?_eq_some hw''
  have hj : w''.tid = tid := by
    rcases Nat.lt_trichotomy tw' tw with h | h | h
    · exact atomic_between hat hrd hlt h hw'' hl''
    · subst h
      rcases hw.cases with ⟨-, -, hg⟩ | ⟨-, rfl⟩
      · rw [hg] at hw''
        cases hw''
        exact hw.tid
      · omega_t
    · rcases hw.cases with ⟨-, -, hg⟩ | ⟨-, rfl⟩
      · rw [← hb tw w htr h hg hl]; exact hw.tid
      · omega_t
  by_cases hp : tw' ∈ t.prom
  · rcases hs with hs | hs
    · exact hs ⟨tid, t, ht, hp⟩
    · exact hnp tw' hp hs
  · have := hseen tw' w'' hw'' hl'' hj hp
    omega_t

/-! ## The ghost effect of a successful RMW -/

/-- `s` is an update slot of the message `k`. -/
def updSlot (g : Ghost) (k : Key) (s : Slot) : Bool := decide (s.key = k ∧ s.id ∈ g.upd k.1)

/-- The slots an RMW reading `(x, tr)` claims. -/
def claimedSlots (g : Ghost) (x : Loc) (tr : Time) : List Slot := g.u.filter (updSlot g (x, tr))

/-- The ghost state after a successful RMW that read `(x, tr)` and wrote at
`tw`: the update slots of `(x, tr)` leave `u` (they go to the thread), the
claim is recorded, and for a release write (`rel`) the message enters
release mode with its slots `ss`. -/
def rmwGhost (g : Ghost) (x : Loc) (tr tw : Time) (rel : Bool) (ss : List Slot) : Ghost :=
  { g with
    u := g.u.filter (fun s => !updSlot g (x, tr) s) ++ ss
    relMsgs := if rel then (x, tw) :: g.relMsgs else g.relMsgs
    claims := ((x, tr), tw) :: g.claims }

/-- The slots a release write of `v` to `x` at `ts` attaches: one per acquire
id of `x` held in `A` and per update id of `x`, each satisfying its
predicate at the message (SLR's release rule, Lemma 49, plus update ids). -/
structure SlotsFor (g : Ghost) (A : Loc → PredId → Nat) (x : Loc) (ts : Time) (v : Val) (mem : Memory)
    (ss : List Slot) : Prop where
  ids : ss.map (·.id) = g.acqIds A x ++ g.upd x
  key : ∀ s ∈ ss, s.key = (x, ts)
  pred : ∀ s ∈ ss, (g.acqPred s.id).P v mem ts s.res

theorem exists_slots (g : Ghost) (k : Key) (v : Val) (mem : Memory) (V : View) :
    ∀ (ids : List PredId) (r : Res), Pred.SepList (ids.map g.acqPred) v mem V r →
    ∃ ss : List Slot, ss.map (·.id) = ids ∧ (∀ s ∈ ss, s.key = k) ∧
      (∀ s ∈ ss, (g.acqPred s.id).P v mem V s.res) ∧ Res.prod (ss.map (·.res)) = r
  | [], r, h => ⟨[], rfl, by simp, by simp, h.symm⟩
  | ι :: ids, _, ⟨r₁, r₂, hr, h1, h2⟩ => by
    obtain ⟨ss, hid, hk, hp, hprod⟩ := exists_slots g k v mem V ids r₂ h2
    refine ⟨⟨k, ι, r₁⟩ :: ss, by simp [hid], ?_, ?_, by simp [hprod, hr]⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · rfl
      · exact hk s hs
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact h1
      · exact hp s hs

/-- A resource satisfying the release predicate of `x` at `v` splits into the
slots of a release write (`relAcq`). -/
theorem Erase.slotsFor {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {x : Loc} {v : Val} {mem : Memory} {ts : Time} {R : Res} (hR : (g.rel x).P v mem ts R) :
    ∃ ss, SlotsFor g (total rF g c).acq x ts v mem ss ∧ Res.prod (ss.map (·.res)) = R := by
  have h := E.relAcq x v mem ts R hR
  rw [Ghost.acqPreds, Ghost.updPreds, ← List.map_append] at h
  obtain ⟨ss, hid, hk, hp, hprod⟩ := exists_slots g (x, ts) v mem ts _ R h
  exact ⟨ss, ⟨hid, hk, hp⟩, hprod⟩

section Rmw

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {t t' : Thread I}
  {mem' : Memory} {x : Loc} {tr tw : Time} {new : Val} {rel : Bool} {ss : List Slot}

theorem mem_rmw_relMsgs {k : Key} :
    k ∈ (rmwGhost g x tr tw rel ss).relMsgs ↔ (rel = true ∧ k = (x, tw)) ∨ k ∈ g.relMsgs := by
  unfold rmwGhost; cases rel <;> simp

theorem claimed_rmw {k : Key} : (rmwGhost g x tr tw rel ss).Claimed k ↔ k = (x, tr) ∨ g.Claimed k := by
  simp [rmwGhost, Ghost.Claimed]

theorem mem_rmw_u {s : Slot} : s ∈ (rmwGhost g x tr tw rel ss).u ↔ (s ∈ g.u ∧ updSlot g (x, tr) s = false) ∨ s ∈ ss := by
  simp [rmwGhost, List.mem_filter]

/-- The total resource after the RMW: the claimed slots moved to the thread,
the new slots out of it, and the write set of `x` gained `(new, tw)`. -/
theorem total_rmw (ht : c.threads[tid]? = some t) {r' : Res}
    (hres : r'.op (Res.prod (ss.map (·.res))) =
      ((rF tid).op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x (new, tw))
    (hpos : 0 < ((rF tid).wr x).q) :
    total (setRes rF tid r') (rmwGhost g x tr tw rel ss) (c.withThread tid t' mem') =
      (total rF g c).addW x (new, tw) := by
  have hn := lt_size_of_get? ht
  obtain ⟨rest, hrest⟩ := threadsRes_split rF hn
  have h1 := hrest rF (fun _ _ => rfl)
  have h2 := hrest (setRes rF tid r') (fun i hi => setRes_ne rF r' hi)
  rw [setRes_self] at h2
  have hperm : (g.u.filter (fun s => !updSlot g (x, tr) s) ++ claimedSlots g x tr).Perm g.u :=
    List.perm_append_comm.trans (List.filter_append_perm _ _)
  have hu : Res.prod (g.u.map (·.res)) =
      (Res.prod ((g.u.filter fun s => !updSlot g (x, tr) s).map (·.res))).op
        (Res.prod ((claimedSlots g x tr).map (·.res))) := by
    rw [← Res.prod_append, ← List.map_append]; exact (Res.prod_perm (hperm.map _)).symm
  simp only [total, Config.withThread_size, Ghost.slotsRes, rmwGhost, List.map_append, Res.prod_append, h1, h2, hu]
  generalize Res.prod ((g.u.filter fun s => !updSlot g (x, tr) s).map (·.res)) = K at *
  generalize Res.prod (ss.map (·.res)) = S at *
  generalize Res.prod ((claimedSlots g x tr).map (·.res)) = C at *
  have hposC : 0 < (((rF tid).op C).wr x).q := Res.pos_op.mpr (.inl hpos)
  calc (r'.op rest).op (K.op S) = (r'.op S).op (rest.op K) := by
        simp only [Res.op_left_comm, Res.op_comm]
    _ = (((rF tid).op C).addW x (new, tw)).op (rest.op K) := by rw [hres]
    _ = (((rF tid).op C).op (rest.op K)).addW x (new, tw) := Res.addW_op _ _ hposC
    _ = (((rF tid).op rest).op (K.op C)).addW x (new, tw) := by
        congr 1; simp only [Res.op_left_comm, Res.op_comm]

/-- **The RMW step lemma** (event level, RMW extension).
Thread `tid` performs a successful RMW event: it read the message `(x, tr)`
(value `old`) and wrote `new` at `tw` (`WriteAt`: fulfilling its promise or
appending), with the machine's `atomic` check. Precondition (the rule's): the
thread owns a write permission for `x` (`hpos`); the read message is
unclaimed (`hun`, from `Erase.not_claimed`); for a relaxed write (`rel =
false`) the value is pure, for a release write (`rel = true`) `ss` are the
slots of the new message (`SlotsFor`, from `Erase.slotsFor` applied to the
part of the thread's resource satisfying `W.rel x new`); the thread's
resource after the event is `r'` with `r' • ss = (r • claimed slots)` plus
`(new, tw)` in `x`'s write set (`hres`). `hval`: the outstanding promises of
the non-exempt threads are valid after the claim (an update slot is acquirable
by every thread, so a claim may invalidate another
thread's promise; on every lock only in doomed configurations, R3, Theorem
1′'s path-relative condition (3); `mayWrite_of_noClaim` discharges it when
nothing is claimed). Then erasure holds after the event, with the update
slots of `(x, tr)` moved to the thread and the claim recorded
(`rmwGhost`). -/
theorem Erase.rmw (E : Erase rF g T c) (ht : c.threads[tid]? = some t)
    (hw : WriteAt c tid t t' mem' tw ⟨x, new, tid⟩) (htr : tr < tw) {old : Val}
    (hrd : c.mem.read? x tr = some old) (hat : c.mem.atomic x tid tr tw = true)
    (hpend : tw ∉ g.pend) (hun : ¬ g.Claimed (x, tr)) (hpos : 0 < ((rF tid).wr x).q)
    (hrel : rel = true → SlotsFor g (total rF g c).acq x tw new mem' ss ∧ ¬ g.Claimed (x, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel x) new)
    {r' : Res}
    (hres : r'.op (Res.prod (ss.map (·.res))) =
      ((rF tid).op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x (new, tw))
    (hval : ∀ i t₁, (c.withThread tid t' mem').threads[i]? = some t₁ → ¬ T i → ∀ ts ∈ t₁.prom,
      ts ∉ g.pend → ∀ w, mem'.get? ts = some w → mayWrite (setRes rF tid r' i) (rmwGhost g x tr tw rel ss) w.loc) :
    Erase (setRes rF tid r') (rmwGhost g x tr tw rel ss) T (c.withThread tid t' mem') := by
  have hn := lt_size_of_get? ht
  have htot := total_rmw (rel := rel) (t' := t') (mem' := mem') ht hres hpos
  have hset : ∀ p, Settled (c.withThread tid t' mem') (rmwGhost g x tr tw rel ss) p ↔ Settled c g p ∨ p = tw :=
    fun p => WriteAt.settled_iff E ht hw rfl
  have hpre := hw.pre
  -- `tw` is not in release mode, so it has no slots
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
  have htw0 := hw.tw_ne_zero
  have hle : tw ≤ mem'.last := mem'.last_le_of_get?_eq_some hw.get?_tw
  have htrk : (x, tr) ≠ (x, tw) := fun h => by simp at h; omega_t
  -- the update ids of `x` are not held
  have hupd0 : ∀ ι ∈ g.upd x, (total rF g c).acq x ι = 0 := fun ι h => ((E.updIds x).2 ι h).2
  exact {
    valid := by rw [htot, Res.valid_addW]; exact E.valid
    slotIds := by
      intro s hs
      rcases mem_rmw_u.mp hs with ⟨hs, -⟩ | hs
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
      have hfulf : Fulf (c.withThread tid t' mem') (rmwGhost g x tr tw rel ss) y p ↔
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
        | true => exact absurd (mem_rmw_relMsgs.mpr (.inl ⟨rfl, rfl⟩)) hnot
        | false => exact (hrlx rfl).2
      · rw [hw.read?_ne hts] at hv
        exact E.pure y ts v hv fun h => hnot (mem_rmw_relMsgs.mpr (.inr h))
    relExists := by
      intro k hk
      rcases mem_rmw_relMsgs.mp hk with ⟨-, rfl⟩ | hk
      · exact ⟨new, hw.read?_tw_self⟩
      · obtain ⟨v, hv⟩ := E.relExists k hk
        exact ⟨v, (hpre.read? (E.relMsgs_le hk)).trans hv⟩
    slotsNodup := by
      simp only [rmwGhost, List.map_append]
      rw [List.nodup_append]
      refine ⟨(List.Sublist.map _ List.filter_sublist).nodup E.slotsNodup, ?_, ?_⟩
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
        have hs1 := (List.mem_filter.mp hs).1
        cases rel with
        | false => rw [(hrlx rfl).1] at hs'; cases hs'
        | true =>
          have hk := ((hrel rfl).1.key s' hs')
          have : s.key = (x, tw) := by simp at he; rw [← he.1, hk]
          exact hnoslot s hs1 this
    slotsDom := by
      intro k ι
      rw [htot, Res.addW_acq, claimed_rmw, mem_rmw_relMsgs]
      constructor
      · rintro ⟨s, hs, rfl, rfl⟩
        rcases mem_rmw_u.mp hs with ⟨hs, hup⟩ | hs
        · obtain ⟨hk, hd⟩ := (E.slotsDom s.key s.id).mp ⟨s, hs, rfl, rfl⟩
          refine ⟨.inr hk, ?_⟩
          rcases hd with hd | ⟨hu, hc⟩
          · exact .inl hd
          · refine .inr ⟨hu, ?_⟩
            rintro (he | hc')
            · have hu' : s.id ∈ g.upd x := by simpa [he] using hu
              simp [updSlot, he, hu'] at hup
            · exact hc hc'
        · obtain ⟨⟨hid, hkey, -⟩, hnc⟩ := hrel (by cases rel <;> simp_all)
          have hr : rel = true := by cases rel <;> simp_all
          have hk := hkey s hs
          refine ⟨.inl ⟨hr, hk⟩, ?_⟩
          have : s.id ∈ g.acqIds (total rF g c).acq x ++ g.upd x := hid ▸ List.mem_map_of_mem hs
          rw [hk]
          rcases List.mem_append.mp this with h | h
          · simp only [Ghost.acqIds, List.mem_filter, beq_iff_eq] at h; exact .inl h.2
          · exact .inr ⟨h, by rintro (he | hc); exact htrk he.symm; exact hnc hc⟩
      · rintro ⟨hk, hd⟩
        rcases hk with ⟨hr, rfl⟩ | hk
        · -- the new release message: its slots are `ss`
          obtain ⟨⟨hid, hkey, -⟩, -⟩ := hrel hr
          have hmem : ι ∈ ss.map (·.id) := by
            rw [hid, List.mem_append]
            rcases hd with hd | ⟨hu, -⟩
            · left
              simp only [Ghost.acqIds, List.mem_filter, List.mem_range, beq_iff_eq]
              exact ⟨E.acqIds x ι (Nat.le_of_eq hd.symm), hd⟩
            · exact .inr hu
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
          exact ⟨s, mem_rmw_u.mpr (.inr hs), hkey s hs, rfl⟩
        · have hd' : (total rF g c).acq k.1 ι = 1 ∨ (ι ∈ g.upd k.1 ∧ ¬ g.Claimed k) := by
            rcases hd with hd | ⟨hu, hc⟩
            · exact .inl hd
            · exact .inr ⟨hu, fun h => hc (.inr h)⟩
          obtain ⟨s, hs, rfl, rfl⟩ := (E.slotsDom k ι).mpr ⟨hk, hd'⟩
          refine ⟨s, mem_rmw_u.mpr (.inl ⟨hs, ?_⟩), rfl, rfl⟩
          simp only [updSlot, decide_eq_false_iff_not, not_and]
          intro he hu
          rcases hd with hd | ⟨-, hc⟩
          · rw [he] at hd; rw [hupd0 _ hu] at hd; cases hd
          · exact hc (.inl he)
    slotsPred := by
      intro s hs v hv
      change mem'.read? _ _ = some v at hv
      rcases mem_rmw_u.mp hs with ⟨hs, -⟩ | hs
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
      rcases mem_rmw_relMsgs.mp hk with ⟨-, rfl⟩ | hk
      · exact (hset _).mpr (.inr rfl)
      · exact (hset _).mpr (.inl (E.relSettled k hk))
    claimsNodup := by
      simp only [rmwGhost, List.map_cons, List.nodup_cons]
      exact ⟨hun, E.claimsNodup⟩
    claimsAt := by
      intro k tw' hk
      rcases List.mem_cons.mp hk with he | hk
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨htr, _, hw.get?_tw, rfl, (hset _).mpr (.inr rfl), ?_⟩
        intro ts w' h1 h2 hw' hl
        have hw'' : c.mem.get? ts = some w' := by rw [← hw.get?_ne (by omega_t)]; exact hw'
        exact atomic_between hat hrd h1 h2 hw'' hl
      · obtain ⟨hlt, w', hw', hl, hs, hb⟩ := E.claimsAt k tw' hk
        have hle' := c.mem.last_le_of_get?_eq_some hw'
        refine ⟨hlt, w', hw.get?_iff.mpr (.inl hw'), hl, (hset _).mpr (.inl hs), ?_⟩
        intro ts w'' h1 h2 hw'' hl''
        change mem'.get? ts = some w'' at hw''
        rw [hpre.get? (by omega_t)] at hw''
        exact hb ts w'' h1 h2 hw'' hl''
    claimFulf := by
      intro k tw' hk ho
      obtain ⟨ho, hne⟩ := (WriteAt.outstanding_iff E ht hw).mp ho
      rcases List.mem_cons.mp hk with he | hk
      · simp only [Prod.mk.injEq] at he
        exact hne he.2
      · exact E.claimFulf k tw' hk ho }

/-- `Erase.rmw` with uniqueness discharged by `Erase.not_claimed`: the
thread half `OwnSeen` (from `ownSeen_of_readSuccs` and `Ctx.OwnCoh`) and no
pending promise of the thread replace `hun`. -/
theorem Erase.rmw_of_seen (E : Erase rF g T c) (ht : c.threads[tid]? = some t)
    (hw : WriteAt c tid t t' mem' tw ⟨x, new, tid⟩) (htr : tr < tw) {old : Val}
    (hrd : c.mem.read? x tr = some old) (hat : c.mem.atomic x tid tr tw = true)
    (hnp : ∀ p ∈ t.prom, p ∉ g.pend) (hseen : OwnSeen c tid t x tr) (hpos : 0 < ((rF tid).wr x).q)
    (hrel : rel = true → SlotsFor g (total rF g c).acq x tw new mem' ss ∧ ¬ g.Claimed (x, tw))
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel x) new)
    {r' : Res}
    (hres : r'.op (Res.prod (ss.map (·.res))) =
      ((rF tid).op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x (new, tw))
    (hval : ∀ i t₁, (c.withThread tid t' mem').threads[i]? = some t₁ → ¬ T i → ∀ ts ∈ t₁.prom,
      ts ∉ g.pend → ∀ w, mem'.get? ts = some w → mayWrite (setRes rF tid r' i) (rmwGhost g x tr tw rel ss) w.loc) :
    Erase (setRes rF tid r') (rmwGhost g x tr tw rel ss) T (c.withThread tid t' mem') :=
  have hpend : tw ∉ g.pend := by
    intro h
    rcases hw.cases with ⟨-, hp, -⟩ | ⟨-, rfl⟩
    · exact hnp tw hp h
    · have := E.pend_le h; omega_t
  E.rmw ht hw htr hrd hat hpend (E.not_claimed ht hw rfl htr hrd hat hnp hseen) hpos hrel hrlx hres hval

/-! ## Promise validity after a claim -/

theorem CanAcq.mono {u u' : List Slot} {U : Loc → List PredId} {A : Loc → PredId → Nat} {k : Key} {ι : PredId}
    (h : CanAcq u U A k ι) (hu : ∀ s ∈ u, s ∈ u') : CanAcq u' U A k ι := by
  induction h with
  | base hs ha => exact .base (hu _ hs) ha
  | upd hs hi => exact .upd (hu _ hs) hi
  | step _ hs hs' ha ih => exact .step ih (hu _ hs) (hu _ hs') ha

/-- An RMW that claims no slot (the message read has no update slot: it is
relaxed, already claimed by nobody else's slots, or its location has no
update ids) keeps every `mayWrite`: the slots only grow. -/
theorem mayWrite_rmw_of_noClaim (hcl : claimedSlots g x tr = []) {r : Res} {y : Loc} (h : mayWrite r g y) :
    mayWrite r (rmwGhost g x tr tw rel ss) y := by
  have hu : ∀ s ∈ g.u, s ∈ (rmwGhost g x tr tw rel ss).u := by
    intro s hs
    refine mem_rmw_u.mpr (.inl ⟨hs, ?_⟩)
    have := List.filter_eq_nil_iff.mp hcl s hs
    simpa using this
  rcases h with h | ⟨s, hs, hc, hq⟩
  · exact .inl h
  · exact .inr ⟨s, hu s hs, hc.mono hu, hq⟩

/-- The `hval` hypothesis of `Erase.rmw` when the RMW claims nothing and the
RMW's thread is exempt (`NPSafe`'s weak erasure, `T = (· = tid)`): the other
threads' promises are as before, and their `mayWrite` survives. -/
theorem Erase.hval_of_noClaim (E : Erase rF g T c) (ht : c.threads[tid]? = some t)
    (hw : WriteAt c tid t t' mem' tw ⟨x, new, tid⟩) (hT : T tid) (hcl : claimedSlots g x tr = []) (r' : Res) :
    ∀ i t₁, (c.withThread tid t' mem').threads[i]? = some t₁ → ¬ T i → ∀ ts ∈ t₁.prom,
      ts ∉ g.pend → ∀ w, mem'.get? ts = some w → mayWrite (setRes rF tid r' i) (rmwGhost g x tr tw rel ss) w.loc := by
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
    exact mayWrite_rmw_of_noClaim hcl (E.promValid i t₁ hi hTi ts hts hp w hw'')

end Rmw

/-! ## Steps that change neither memory nor the thread's promises -/

/-- **A read keeps erasure** (the read of a failed CAS, a relaxed or acquire
read before SLR's acquire transfer, a fence, a register operation): if the
step changes neither the memory nor thread `tid`'s promise set, erasure is
unchanged. A failed CAS claims nothing. -/
theorem Erase.sameProm {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat}
    {t t' : Thread I} (E : Erase rF g T c) (ht : c.threads[tid]? = some t) (hp : t'.prom = t.prom) :
    Erase rF g T (c.withThread tid t' c.mem) := by
  have hn := lt_size_of_get? ht
  have hget := fun i => Config.withThread_get? c (i := i) t' c.mem hn
  have hsub : PromSub c (c.withThread tid t' c.mem) := by
    refine ⟨rfl, Config.withThread_size _ _ _ _, fun i t₁ hi => ?_⟩
    rw [hget] at hi
    split at hi
    · next h =>
      subst h
      simp only [Option.some.injEq] at hi
      subst hi
      exact ⟨t, ht, fun p h => hp ▸ h⟩
    · exact ⟨t₁, hi, fun _ h => h⟩
  have hout : ∀ ts, Outstanding c ts → Outstanding (c.withThread tid t' c.mem) ts := by
    rintro ts ⟨i, t₁, hi, hts⟩
    by_cases h : tid = i
    · subst h
      rw [ht] at hi; cases hi
      exact ⟨tid, t', by rw [hget, ite_eq_left rfl], hp ▸ hts⟩
    · exact ⟨i, t₁, by rw [hget, ite_eq_right h]; exact hi, hts⟩
  have E' := E.fulfil hsub (fun ts ho hno => absurd (hout ts ho) hno) (pend' := g.pend)
    (fun ts => ⟨fun h => ⟨h, hout ts (E.pend ts h).2⟩, fun h => h.1⟩)
  exact E'

end Kraken.Promising.SLR
