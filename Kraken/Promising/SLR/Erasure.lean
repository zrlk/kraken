/-
Erasure, `canAcq` and the `ResModel` instance of the SLR-adapted resource
model. SLR = Svendsen et al., *A separation logic
for a promising semantics* (ESOP 2018), technical appendix §3.1–3.3.

## Contents

- `Ghost`: SLR's world `W` (release predicates per location, a table of
  acquire predicates indexed by `PredId`) and message resources `u`, plus
  what Kraken's modeless messages need: the set of messages in *release
  mode* (`relMsgs`) and the *pending* releases (`pend`, design (V) variant
  (ii)).
- `CanAcq`, `mayWrite`: SLR's `canAcq(r, u)` as a least fixpoint, and
  `writeAllowed(r • canAcq(r, u), m)` (positivity needs no product).
- `Erase`: SLR's erasure `⌊rF, u, W⌋_T` over Kraken configurations, with the
  pending-release clause.
- `model`, `laws`: the `ResModel` instance and its `ResModel.Laws`
  (`Laws.promise` is SLR's Lemmas 23–24 for messages that transfer nothing).
- `validate`, `promiseExempt_of_pure`: the two fields of
  `ResModel.PromisedRelease`, the second only for messages that transfer
  nothing (it is false in general for SLR's erasure),
  and `pendingOfFulfil`, the pending-release law that replaces it.

## Kraken specifics

Messages carry no mode, so the ghost records which messages are release
messages (`relMsgs`). Every location has an initial message at timestamp
`0`, so message resources and modes are keyed by `(location, timestamp)`.
The write-set clause applies to locations with a permission or a settled
(fulfilled or pending) non-initial message only. Erasure does not look at
thread states or views (SLR's views live in the assertions), only at memory,
promise sets and ghost state; this is what lets erasure of a virtual
configuration (`Config.VirtualOf`) be checked against the real memory.
-/
import Kraken.Promising.SLR.Resources

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Ghost state -/

/-- A message, by location and timestamp (`0`: the initial message of the
location). -/
abbrev Key := Loc × Time

/-- A message resource slot: the resource `res` attached to the release
message `key` for the acquire predicate `id` (SLR's `u(m)(ι)`). -/
structure Slot where
  key : Key
  id : PredId
  res : Res

/-- SLR's ghost state `(u, W)`, with Kraken's message modes. -/
structure Ghost where
  /-- `W.rel`: the release predicate of each location. -/
  rel : Loc → Pred
  /-- `W.acq`: the acquire predicates; ids are indices. -/
  acqTab : List Pred
  /-- `u`: the message resources. -/
  u : List Slot
  /-- The messages in release mode (fulfilled or pending). -/
  relMsgs : List Key
  /-- Pending messages: outstanding promises that the thread's next
  instruction fulfils, one of them with a release store (design (V)
  variant (ii)). Erased as written messages. -/
  pend : List Time
  /-- The **update ids** of each location (RMW extension): acquire predicates that no resource holds and whose slots the
  successful RMW reading the message claims whole. `U(x, φ)` is the world
  fact `∃ ι ∈ upd x, W.acq ι = φ`, duplicable (FSL++'s `RMWAcq`): at most one
  RMW reads each message. -/
  upd : Loc → List PredId := fun _ => []
  /-- Claimed messages: `((x, tr), tw)` says the message `(x, tr)` was read
  by the successful RMW whose write is the message at `tw` (the claimer). -/
  claims : List (Key × Time) := []

namespace Ghost

/-- `W.acq ι`, `⊥` for an unallocated id. -/
def acqPred (g : Ghost) (ι : PredId) : Pred := g.acqTab.getD ι Pred.bot

/-- `Π_{m, ι} u(m)(ι)`. -/
def slotsRes (g : Ghost) : Res := Res.prod (g.u.map (·.res))

/-- The allocated acquire ids of `x` held (once) in `A`. -/
def acqIds (g : Ghost) (A : Loc → PredId → Nat) (x : Loc) : List PredId :=
  (List.range g.acqTab.length).filter fun ι => A x ι == 1

/-- The acquire predicates of `x` held in `A`. -/
def acqPreds (g : Ghost) (A : Loc → PredId → Nat) (x : Loc) : List Pred :=
  (g.acqIds A x).map g.acqPred

/-- The update predicates of `x`. -/
def updPreds (g : Ghost) (x : Loc) : List Pred := (g.upd x).map g.acqPred

/-- The message `k` has been claimed by a successful RMW. -/
def Claimed (g : Ghost) (k : Key) : Prop := k ∈ g.claims.map (·.1)

end Ghost

/-- `Π_{i < n} rF(i)`. -/
def threadsRes (rF : Nat → Res) (n : Nat) : Res := Res.prod ((List.range n).map rF)

/-- SLR's `t = Π_i r(i) • Π_{m, ι} u(m)(ι)`: every thread's resource and
every message resource. -/
def total (rF : Nat → Res) (g : Ghost) (c : Config I) : Res := (threadsRes rF c.threads.size).op g.slotsRes

/-! ## Messages: outstanding, settled, write sets -/

/-- `ts` is an outstanding promise of some thread. -/
def Outstanding (c : Config I) (ts : Time) : Prop := ∃ (i : Nat) (t : Thread I), c.threads[i]? = some t ∧ ts ∈ t.prom

/-- The message at `ts` counts as written: it is not an outstanding promise,
or it is a pending release. -/
def Settled (c : Config I) (g : Ghost) (ts : Time) : Prop := ¬ Outstanding c ts ∨ ts ∈ g.pend

/-- SLR's `{(m.val, m.time) | m ∈ M(x) \ P}`, with pending releases counted
as written and the initial message included. -/
def Fulf (c : Config I) (g : Ghost) (x : Loc) (p : Val × Time) : Prop :=
  (p.2 = 0 ∧ p.1 = c.mem.initVal x) ∨
    ∃ w, c.mem.get? p.2 = some w ∧ w.loc = x ∧ w.val = p.1 ∧ Settled c g p.2

/-- The write-set clause applies to `x`: some resource has a permission for
it, or it has a settled non-initial message. -/
def Tracked (c : Config I) (g : Ghost) (t : Res) (x : Loc) : Prop :=
  0 < (t.wr x).q ∨ ∃ ts w, c.mem.get? ts = some w ∧ w.loc = x ∧ Settled c g ts

/-! ## Acquirable resources -/

/-- SLR's `canAcq(A, u)`: the message resource slots a thread holding the
acquire permissions `A` may acquire, directly (`ι ∈ A(m.loc)`) or through
the acquire permissions of slots it may acquire. SLR computes it by a
recursion that deletes used slots; its value is this least fixpoint. -/
inductive CanAcq (u : List Slot) (U : Loc → List PredId) (A : Loc → PredId → Nat) : Key → PredId → Prop
  | base {s : Slot} : s ∈ u → 1 ≤ A s.key.1 s.id → CanAcq u U A s.key s.id
  /-- RMW extension: an update slot (`s.id ∈ U s.key.1`) is acquirable by
  every thread (`U(x, φ)` is duplicable), so a thread may promise a store
  whose permission it will claim by an RMW. -/
  | upd {s : Slot} : s ∈ u → s.id ∈ U s.key.1 → CanAcq u U A s.key s.id
  | step {s s' : Slot} : CanAcq u U A s.key s.id → s ∈ u → s' ∈ u → 1 ≤ s.res.acq s'.key.1 s'.id →
      CanAcq u U A s'.key s'.id

/-- SLR's `writeAllowed(r • canAcq(r, u), m)` for a message to `x`: the
thread owns a write permission for `x` or may acquire one. -/
def mayWrite (r : Res) (g : Ghost) (x : Loc) : Prop :=
  0 < (r.wr x).q ∨ ∃ s ∈ g.u, CanAcq g.u g.upd r.acq s.key s.id ∧ 0 < (s.res.wr x).q

/-- `CanAcq` using only slots of messages at timestamps `≤ b` (for
condition (3), the bounded-reach proposal): every slot of the acquisition chain is
attached to a message that was in memory when the memory had `b` messages. -/
inductive CanAcqB (u : List Slot) (U : Loc → List PredId) (A : Loc → PredId → Nat) (b : Time) :
    Key → PredId → Prop
  | base {s : Slot} : s ∈ u → s.key.2 ≤ b → 1 ≤ A s.key.1 s.id → CanAcqB u U A b s.key s.id
  | upd {s : Slot} : s ∈ u → s.key.2 ≤ b → s.id ∈ U s.key.1 → CanAcqB u U A b s.key s.id
  | step {s s' : Slot} : CanAcqB u U A b s.key s.id → s ∈ u → s' ∈ u → s'.key.2 ≤ b →
      1 ≤ s.res.acq s'.key.1 s'.id → CanAcqB u U A b s'.key s'.id

theorem CanAcqB.canAcq {u : List Slot} {U : Loc → List PredId} {A : Loc → PredId → Nat} {b : Time}
    {k : Key} {ι : PredId} (h : CanAcqB u U A b k ι) : CanAcq u U A k ι := by
  induction h with
  | base hs _ ha => exact .base hs ha
  | upd hs _ hu => exact .upd hs hu
  | step _ hs hs' _ ha ih => exact .step ih hs hs' ha

/-- `mayWrite` bounded by `b` (`ResModel.reach` of the instance): the thread
owns a write permission for `x`, or may acquire one through slots of
messages `≤ b` only. -/
def reachB (r : Res) (g : Ghost) (x : Loc) (b : Time) : Prop :=
  0 < (r.wr x).q ∨ ∃ s ∈ g.u, s.key.2 ≤ b ∧ CanAcqB g.u g.upd r.acq b s.key s.id ∧ 0 < (s.res.wr x).q

theorem reachB_mayWrite {r : Res} {g : Ghost} {x : Loc} {b : Time} (h : reachB r g x b) : mayWrite r g x := by
  rcases h with h | ⟨s, hs, -, hc, hp⟩
  · exact .inl h
  · exact .inr ⟨s, hs, hc.canAcq, hp⟩

/-! ## Erasure -/

/-- **SLR's erasure `⌊rF, u, W⌋_T`** over Kraken (table "Erasure"). Outstanding
promises of threads in `T` need not be valid. -/
structure Erase (rF : Nat → Res) (g : Ghost) (T : Nat → Prop) (c : Config I) : Prop where
  /-- `t` is defined. -/
  valid : (total rF g c).valid
  /-- `wf`: slot ids are allocated. -/
  slotIds : ∀ s ∈ g.u, s.id < g.acqTab.length
  /-- `wf`: held acquire ids are allocated. -/
  acqIds : ∀ x ι, 1 ≤ (total rF g c).acq x ι → ι < g.acqTab.length
  /-- `wf`: `W.rel x v ⊢ ⊛_{ι ∈ t.acq x} W.acq ι v ⊛ ⊛_{ι ∈ upd x} W.acq ι v`
  (held ids, then update ids). -/
  relAcq : ∀ x v m V r, (g.rel x).P v m V r →
    Pred.SepList (g.acqPreds (total rF g c).acq x ++ g.updPreds x) v m V r
  /-- Write sets: the write set of `x` is its settled messages. -/
  writes : ∀ x, Tracked c g (total rF g c) x → ∀ p, ((total rF g c).wr x).X p ↔ Fulf c g x p
  /-- Every message not in release mode (relaxed; promises and initial
  messages included) satisfies its location's release predicate purely. -/
  pure : ∀ x ts v, c.mem.read? x ts = some v → (x, ts) ∉ g.relMsgs → Pred.Pure (g.rel x) v
  /-- Release-mode messages exist. -/
  relExists : ∀ k ∈ g.relMsgs, ∃ v, c.mem.read? k.1 k.2 = some v
  /-- At most one slot per message and id. -/
  slotsNodup : (g.u.map fun s => (s.key, s.id)).Nodup
  /-- `dom u(m) = t.acq(m.loc)` for release messages, plus the update ids of
  `m.loc` while `m` is unclaimed, and only release messages have slots. -/
  slotsDom : ∀ k ι, (∃ s ∈ g.u, s.key = k ∧ s.id = ι) ↔
    (k ∈ g.relMsgs ∧ ((total rF g c).acq k.1 ι = 1 ∨ (ι ∈ g.upd k.1 ∧ ¬ g.Claimed k)))
  /-- Each slot satisfies its acquire predicate at the message's value and
  timestamp. -/
  slotsPred : ∀ s ∈ g.u, ∀ v, c.mem.read? s.key.1 s.key.2 = some v → (g.acqPred s.id).P v c.mem s.key.2 s.res
  /-- Every outstanding promise is a message of its thread (`P ⊆ M`). -/
  promWf : ∀ i t, c.threads[i]? = some t → ∀ ts ∈ t.prom, ∃ w, c.mem.get? ts = some w ∧ w.tid = i
  /-- `validPromises_T`: an outstanding promise of a thread outside `T` that
  is not pending is one its thread may write. -/
  promValid : ∀ i t, c.threads[i]? = some t → ¬ T i → ∀ ts ∈ t.prom, ts ∉ g.pend →
    ∀ w, c.mem.get? ts = some w → mayWrite (rF i) g w.loc
  /-- **Pending-release clause**: a pending message is an outstanding
  promise. It is erased as written (`Settled`: write sets, no validity
  obligation); in release mode (`relMsgs`) it carries its slots, otherwise it
  must be pure, as any relaxed message. -/
  pend : ∀ ts ∈ g.pend, (∃ w, c.mem.get? ts = some w) ∧ Outstanding c ts
  /-- Update ids are allocated, distinct, and held by no resource. -/
  updIds : ∀ x, (g.upd x).Nodup ∧ ∀ ι ∈ g.upd x, ι < g.acqTab.length ∧ (total rF g c).acq x ι = 0
  /-- Release-mode messages are settled (written, or pending). -/
  relSettled : ∀ k ∈ g.relMsgs, Settled c g k.2
  /-- At most one claim per message (atomicity of RMWs). -/
  claimsNodup : (g.claims.map (·.1)).Nodup
  /-- A claim `((x, tr), tw)`: the claimer `tw` is a settled message to `x`
  above `tr`, and every message to `x` strictly between them is by the
  claimer's thread (the RMW's `Memory.atomic` check, remembered). -/
  claimsAt : ∀ k tw, (k, tw) ∈ g.claims → k.2 < tw ∧ ∃ w, c.mem.get? tw = some w ∧ w.loc = k.1 ∧
    Settled c g tw ∧ ∀ ts w', k.2 < ts → ts < tw → c.mem.get? ts = some w' → w'.loc = k.1 → w'.tid = w.tid
  /-- **Claimers are performed writes** (T1c option (B)): the write `tw` of a
  claim is not an outstanding promise. An RMW claims when its write is
  performed (a fresh message or a fulfilled promise), never at promise time,
  so a thread's own pending promise is never a claimer; RMW rules use this
  instead of an own-pending hypothesis. -/
  claimFulf : ∀ k tw, (k, tw) ∈ g.claims → ¬ Outstanding c tw

/-! ## The resource model -/

/-- SLR's world order `W ≤ W'` (`ResModel.ghostLe`): release
predicates unchanged, acquire predicates only allocated (the table grows at
the end, so an id keeps its predicate), update ids only added. Message
resources, release modes, pending marks and claims are free: erasure alone
constrains them. -/
structure Ghost.Le (g g' : Ghost) : Prop where
  rel : g'.rel = g.rel
  acqTab : g.acqTab <+: g'.acqTab
  upd : ∀ x, g.upd x <+: g'.upd x

theorem Ghost.Le.refl (g : Ghost) : g.Le g := ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩

theorem Ghost.Le.trans {g₁ g₂ g₃ : Ghost} (h₁ : g₁.Le g₂) (h₂ : g₂.Le g₃) : g₁.Le g₃ :=
  ⟨h₂.rel.trans h₁.rel, h₁.acqTab.trans h₂.acqTab, fun x => (h₁.upd x).trans (h₂.upd x)⟩

/-- The SLR-adapted resource model. `owns`: a positive
write permission; `acqLe`: SLR's ownership order `≤o` on `r • canAcq(r, u)`,
qualitatively (no location becomes ownable-or-acquirable), which is all that
SLR's proofs of Theorem 1 and adequacy use of it. `ghostLe`: `Ghost.Le`;
`pendingAt`: the pending list `pend`; `reach`: `reachB`, the
bounded `mayWrite`. -/
def model (I : ISA) : ResModel I where
  R := Res
  Ghost := Ghost
  erase := Erase
  owns r x := 0 < (r.wr x).q
  acqLe r' g' r g := ∀ x, mayWrite r' g' x → mayWrite r g x
  ghostLe := Ghost.Le
  pendingAt g ts := ts ∈ g.pend
  reach := reachB

/-! ## Helper facts -/

private theorem read?_le_last {m : Memory} {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) :
    t ≤ m.last := by
  unfold Memory.read? at h
  split at h
  · next h0 => subst h0; exact Nat.zero_le _
  · split at h
    · rename_i w hw; exact m.last_le_of_get?_eq_some hw
    · cases h

theorem Erase.relMsgs_le {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {k : Key} (hk : k ∈ g.relMsgs) : k.2 ≤ c.mem.last := by
  obtain ⟨v, hv⟩ := E.relExists k hk
  exact read?_le_last hv

theorem Erase.pend_le {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {ts : Time} (hts : ts ∈ g.pend) : ts ≤ c.mem.last := by
  obtain ⟨⟨w, hw⟩, -⟩ := E.pend ts hts
  exact c.mem.last_le_of_get?_eq_some hw

/-! ## Laws: weakening and `mayWrite` (SLR Lemmas 16, 21) -/

/-- Exempting more threads weakens erasure. -/
theorem Erase.weaken {rF : Nat → Res} {g : Ghost} {T T' : Nat → Prop} {c : Config I}
    (hT : ∀ i, T i → T' i) (E : Erase rF g T c) : Erase rF g T' c :=
  { E with promValid := fun i t ht hi => E.promValid i t ht (fun h => hi (hT i h)) }

/-! ## Laws: promises of messages that transfer nothing (SLR Lemmas 23–24) -/

section Promise

variable {c : Config I} {tid : Nat} {t : Thread I} {w : Msg}

/-- The configuration after thread `tid` (state `t`) promises `w`, as
`StepBy`, `ResModel.Laws.promise` and `ResModel.PromisedRelease` write it. -/
abbrev Promised (c : Config I) (tid : Nat) (t : Thread I) (w : Msg) : Config I :=
  c.withThread tid { t with prom := t.prom ++ [(c.mem.append { w with tid }).2] } (c.mem.append { w with tid }).1

theorem promised_mem : (Promised c tid t w).mem = (c.mem.append { w with tid }).1 := rfl

theorem promised_size : (Promised c tid t w).threads.size = c.threads.size :=
  Config.withThread_size _ _ _ _

theorem promised_get? (ht : c.threads[tid]? = some t) (i : Nat) :
    (Promised c tid t w).threads[i]? =
      if tid = i then some { t with prom := t.prom ++ [c.mem.last + 1] } else c.threads[i]? :=
  Config.withThread_get? _ _ _ (lt_size_of_get? ht)

theorem promised_total (rF : Nat → Res) (g : Ghost) : total rF g (Promised c tid t w) = total rF g c := by
  simp only [total, promised_size]

theorem promised_prefix : c.mem.Prefix (Promised c tid t w).mem := Memory.Prefix.append _ _

theorem promised_get?_of_le {ts : Time} (h : ts ≤ c.mem.last) :
    (Promised c tid t w).mem.get? ts = c.mem.get? ts :=
  promised_prefix.get? h

theorem promised_get?_cases {ts : Time} {w' : Msg} (h : (Promised c tid t w).mem.get? ts = some w') :
    (ts ≤ c.mem.last ∧ c.mem.get? ts = some w') ∨ (ts = c.mem.last + 1 ∧ w' = { w with tid }) :=
  Memory.get?_append_eq_some _ _ h

theorem promised_read?_of_le {x : Loc} {ts : Time} (h : ts ≤ c.mem.last) :
    (Promised c tid t w).mem.read? x ts = c.mem.read? x ts :=
  promised_prefix.read? h

theorem promised_read?_new {x : Loc} {ts : Time} {v : Val} (hv : (Promised c tid t w).mem.read? x ts = some v)
    (hlt : c.mem.last < ts) : ts = c.mem.last + 1 ∧ x = w.loc ∧ v = w.val := by
  rw [promised_mem] at hv
  have hle := read?_le_last hv
  rw [Memory.last_append] at hle
  obtain rfl : ts = c.mem.last + 1 := by omega_t
  refine ⟨rfl, ?_⟩
  unfold Memory.read? at hv
  rw [Memory.get?_append_last] at hv
  simp only [Nat.add_one_ne_zero, ↓reduceIte] at hv
  split at hv
  · next hb => simp only [beq_iff_eq] at hb; simp only [Option.some.injEq] at hv; exact ⟨hb.symm, hv.symm⟩
  · cases hv

theorem outstanding_promised (ht : c.threads[tid]? = some t) {ts : Time} :
    Outstanding (Promised c tid t w) ts ↔ Outstanding c ts ∨ ts = c.mem.last + 1 := by
  constructor
  · rintro ⟨i, t', hi, hts⟩
    rw [promised_get? ht] at hi
    split at hi
    · next h =>
      subst h
      simp only [Option.some.injEq] at hi
      subst hi
      rcases List.mem_append.mp hts with h | h
      · exact .inl ⟨tid, t, ht, h⟩
      · exact .inr (List.mem_singleton.mp h)
    · exact .inl ⟨i, t', hi, hts⟩
  · rintro (⟨i, t', hi, hts⟩ | rfl)
    · by_cases h : tid = i
      · subst h
        rw [ht] at hi; cases hi
        exact ⟨tid, _, by rw [promised_get? ht, ite_eq_left rfl], List.mem_append_left _ hts⟩
      · exact ⟨i, t', by rw [promised_get? ht, ite_eq_right h]; exact hi, hts⟩
    · exact ⟨tid, _, by rw [promised_get? ht, ite_eq_left rfl], List.mem_append_right _ (List.mem_singleton_self _)⟩

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop}

theorem settled_promised (ht : c.threads[tid]? = some t) {ts : Time}
    (hts : ts ≤ c.mem.last) : Settled (Promised c tid t w) g ts ↔ Settled c g ts := by
  have hne : ts ≠ c.mem.last + 1 := by omega_t
  unfold Settled
  rw [outstanding_promised ht]
  simp only [hne, or_false]

theorem not_settled_promised_new (E : Erase rF g T c) (ht : c.threads[tid]? = some t) :
    ¬ Settled (Promised c tid t w) g (c.mem.last + 1) := by
  rintro (h | h)
  · exact h ((outstanding_promised ht).mpr (.inr rfl))
  · have := E.pend_le h; omega_t

theorem fulf_promised (E : Erase rF g T c) (ht : c.threads[tid]? = some t) (x : Loc) (p : Val × Time) :
    Fulf (Promised c tid t w) g x p ↔ Fulf c g x p := by
  unfold Fulf
  rw [promised_prefix.initVal]
  constructor
  · rintro (h | ⟨w', hw', hl, hv, hs⟩)
    · exact .inl h
    · rcases promised_get?_cases hw' with ⟨hle, hw''⟩ | ⟨he, -⟩
      · exact .inr ⟨w', hw'', hl, hv, (settled_promised ht hle).mp hs⟩
      · rw [he] at hs; exact absurd hs (not_settled_promised_new E ht)
  · rintro (h | ⟨w', hw', hl, hv, hs⟩)
    · exact .inl h
    · have hle := c.mem.last_le_of_get?_eq_some hw'
      exact .inr ⟨w', (promised_get?_of_le hle).trans hw', hl, hv, (settled_promised ht hle).mpr hs⟩

theorem tracked_promised (E : Erase rF g T c) (ht : c.threads[tid]? = some t) (r : Res) (x : Loc) :
    Tracked (Promised c tid t w) g r x ↔ Tracked c g r x := by
  unfold Tracked
  constructor
  · rintro (h | ⟨ts, w', hw', hl, hs⟩)
    · exact .inl h
    · rcases promised_get?_cases hw' with ⟨hle, hw''⟩ | ⟨he, -⟩
      · exact .inr ⟨ts, w', hw'', hl, (settled_promised ht hle).mp hs⟩
      · rw [he] at hs; exact absurd hs (not_settled_promised_new E ht)
  · rintro (h | ⟨ts, w', hw', hl, hs⟩)
    · exact .inl h
    · have hle := c.mem.last_le_of_get?_eq_some hw'
      exact .inr ⟨ts, w', (promised_get?_of_le hle).trans hw', hl, (settled_promised ht hle).mpr hs⟩

/-- **A promise keeps erasure** (SLR Lemmas 23–24): if the promising thread
may write the location (unless its promises are exempt) and the message is
pure for its location's release predicate (it transfers nothing), erasure
holds after the promise. The new message is outstanding, so write sets are
unchanged; it is in relaxed mode and pure; predicates of release messages
stay true because the memory only grew. -/
theorem Erase.promise (E : Erase rF g T c) (ht : c.threads[tid]? = some t)
    (hw : ¬ T tid → mayWrite (rF tid) g w.loc) (hp : Pred.Pure (g.rel w.loc) w.val) :
    Erase rF g T (Promised c tid t w) where
  valid := by rw [promised_total]; exact E.valid
  slotIds := E.slotIds
  acqIds := by rw [promised_total]; exact E.acqIds
  relAcq := by rw [promised_total]; exact E.relAcq
  writes := by
    rw [promised_total]
    intro x hx p
    rw [fulf_promised E ht]
    exact E.writes x ((tracked_promised E ht _ x).mp hx) p
  pure := by
    intro x ts v hv hnot
    rcases Nat.lt_or_ge c.mem.last ts with hlt | hle
    · obtain ⟨-, rfl, rfl⟩ := promised_read?_new hv hlt
      exact hp
    · rw [promised_read?_of_le hle] at hv
      exact E.pure x ts v hv hnot
  relExists := by
    intro k hk
    rw [promised_read?_of_le (E.relMsgs_le hk)]
    exact E.relExists k hk
  slotsNodup := E.slotsNodup
  slotsDom := by rw [promised_total]; exact E.slotsDom
  slotsPred := by
    intro s hs v hv
    have hk : s.key ∈ g.relMsgs := ((E.slotsDom s.key s.id).mp ⟨s, hs, rfl, rfl⟩).1
    rw [promised_read?_of_le (E.relMsgs_le hk)] at hv
    exact (g.acqPred s.id).mono _ _ _ _ _ promised_prefix (E.slotsPred s hs v hv)
  promWf := by
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
  promValid := by
    intro i t' hi hT ts hts hpend w' hw'
    rw [promised_get? ht] at hi
    split at hi
    · next h =>
      subst h
      simp only [Option.some.injEq] at hi
      subst hi
      rcases promised_get?_cases hw' with ⟨hle, hw''⟩ | ⟨he, rfl⟩
      · have hts' : ts ∈ t.prom := by
          rcases List.mem_append.mp hts with h | h
          · exact h
          · rw [List.mem_singleton.mp h] at hle; omega_t
        exact E.promValid tid t ht hT ts hts' hpend w' hw''
      · exact hw hT
    · obtain ⟨w'', hw'', -⟩ := E.promWf i t' hi ts hts
      have hle := c.mem.last_le_of_get?_eq_some hw''
      rw [promised_get?_of_le hle] at hw'
      exact E.promValid i t' hi hT ts hts hpend w' hw'
  pend := by
    intro ts hts
    obtain ⟨⟨w', hw'⟩, ho⟩ := E.pend ts hts
    exact ⟨⟨w', (promised_get?_of_le (c.mem.last_le_of_get?_eq_some hw')).trans hw'⟩,
      (outstanding_promised ht).mpr (.inl ho)⟩
  updIds := by rw [promised_total]; exact E.updIds
  relSettled := fun k hk => (settled_promised ht (E.relMsgs_le hk)).mpr (E.relSettled k hk)
  claimsNodup := E.claimsNodup
  claimsAt := by
    intro k tw hk
    obtain ⟨hlt, w', hw', hl, hs, hb⟩ := E.claimsAt k tw hk
    have hle := c.mem.last_le_of_get?_eq_some hw'
    refine ⟨hlt, w', (promised_get?_of_le hle).trans hw', hl, (settled_promised ht hle).mpr hs, ?_⟩
    intro ts w'' h1 h2 hw'' hl''
    rw [promised_get?_of_le (by omega_t)] at hw''
    exact hb ts w'' h1 h2 hw'' hl''
  claimFulf := by
    intro k tw hk ho
    obtain ⟨-, w', hw', -⟩ := E.claimsAt k tw hk
    have hle := c.mem.last_le_of_get?_eq_some hw'
    rcases (outstanding_promised ht).mp ho with h | h
    · exact E.claimFulf k tw hk h
    · omega_t

end Promise

/-! ## The laws -/

/-- **`ResModel.Laws` for the SLR-adapted model.** `mayWrite` is SLR's
`writeAllowed(r • canAcq(r, u), ·)`; a message transfers nothing when its
location's release predicate is pure at its value (SLR's condition for
relaxed messages); `promise` is `Erase.promise` (SLR Lemmas 23–24);
`owns_mayWrite` and `acqLe_mayWrite` (SLR Lemmas 16, 21's use of `≤o`) hold
by definition of the qualitative `≤o`. -/
def laws (I : ISA) : (model I).Laws where
  weaken := fun _ _ _ _ _ hT E => Erase.weaken hT E
  mayWrite := mayWrite
  transfersNothing g w := Pred.Pure (Ghost.rel g w.loc) w.val
  promise := fun _ _ _ _ _ _ _ E ht hw hp => Erase.promise E ht hw hp
  owns_mayWrite := fun _ _ _ h => .inl h
  owns_reach := fun _ _ _ _ h => .inl h
  reach_mayWrite := fun _ _ _ _ h => reachB_mayWrite h
  acqLe_mayWrite := fun _ _ _ _ l h hm => h l hm
  ghostLe_refl := Ghost.Le.refl
  ghostLe_trans := fun _ _ _ h₁ h₂ => h₁.trans h₂

/-! ## Design (V): the laws of `ResModel.PromisedRelease` -/

/-- `ResModel.PromisedRelease.validate` (SLR's erasure condition (3) for one
thread): exempt erasure plus `mayWrite` for each outstanding promise of the
thread that is not pending is erasure without the exemption (the
hypothesis no longer covers pending promises, which `promValid` exempts). -/
theorem validate {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat}
    (E : Erase rF g T c)
    (hv : ∀ t, c.threads[tid]? = some t → ∀ ts ∈ t.prom, ts ∉ g.pend → ∀ w, c.mem.get? ts = some w →
      mayWrite (rF tid) g w.loc) :
    Erase rF g (fun i => T i ∧ i ≠ tid) c :=
  { E with
    promValid := fun i t ht hT ts hts hp w hw => by
      by_cases hi : i = tid
      · subst hi; exact hv t ht ts hts hp w hw
      · exact E.promValid i t ht (fun h => hT ⟨h, hi⟩) ts hts hp w hw }

/-- `validate` in the shape of `ResModel.PromisedRelease.validate`. -/
theorem model_validate (rF : Nat → (model I).R) (g : (model I).Ghost) (T : Nat → Prop) (c : Config I) (tid : Nat)
    (E : (model I).erase rF g T c)
    (hv : ∀ t, c.threads[tid]? = some t → ∀ ts ∈ t.prom, ¬ (model I).pendingAt g ts → ∀ w, c.mem.get? ts = some w →
      (laws I).mayWrite (rF tid) g w.loc) :
    (model I).erase rF g (fun i => T i ∧ i ≠ tid) c :=
  validate E hv

/-- `promiseExempt` (a field of `ResModel.PromisedRelease`,
replaced there by `pending`) for messages that transfer
nothing. In general (any message) it is **false** for SLR's erasure: weak
erasure exempts only the *validity* of the exempt thread's promises, not the
purity of a relaxed message (SLR Lemma 24 needs purity of every promised
relaxed message, and the relaxed read rule relies on it), and exempting
purity as well would make `validate` unprovable. Design (V) does not need
the general form: see `Erase.pendingOfFulfil`. -/
theorem promiseExempt_of_pure {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat}
    {t : Thread I} {w : Msg} (hT : T tid) (E : Erase rF g T c) (ht : c.threads[tid]? = some t)
    (hp : (laws I).transfersNothing g w) : Erase rF g T (Promised c tid t w) :=
  E.promise ht (fun h => absurd hT h) hp

/-! ## The pending-release law (design (V) variant (ii)) -/

section Pending

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {t t' : Thread I}

/-- The configuration in which thread `tid` has run its next instruction `F`
without changing memory: state `t'`, whose promises are among `t`'s. -/
abbrev Fulfilled (c : Config I) (tid : Nat) (t' : Thread I) : Config I := c.withThread tid t' c.mem

/-- The promises of `t` that `t'` has fulfilled. -/
def fulfilledBy (t t' : Thread I) : List Time := t.prom.filter fun p => !t'.prom.contains p

theorem mem_fulfilledBy {p : Time} : p ∈ fulfilledBy t t' ↔ p ∈ t.prom ∧ p ∉ t'.prom := by
  simp [fulfilledBy, List.mem_filter]

theorem fulfilled_get? (ht : c.threads[tid]? = some t) (i : Nat) :
    (Fulfilled c tid t').threads[i]? = if tid = i then some t' else c.threads[i]? :=
  Config.withThread_get? _ _ _ (lt_size_of_get? ht)

theorem fulfilled_size : (Fulfilled c tid t').threads.size = c.threads.size :=
  Config.withThread_size _ _ _ _

/-- Before `F`, a message is outstanding iff it is outstanding after `F` or
`F` fulfils it. -/
theorem outstanding_fulfilled (ht : c.threads[tid]? = some t) (hsub : ∀ p ∈ t'.prom, p ∈ t.prom) {ts : Time} :
    Outstanding c ts ↔ Outstanding (Fulfilled c tid t') ts ∨ ts ∈ fulfilledBy t t' := by
  constructor
  · rintro ⟨i, t₁, hi, hts⟩
    by_cases h : tid = i
    · subst h
      rw [ht] at hi; cases hi
      by_cases h' : ts ∈ t'.prom
      · exact .inl ⟨tid, t', by rw [fulfilled_get? ht, ite_eq_left rfl], h'⟩
      · exact .inr (mem_fulfilledBy.mpr ⟨hts, h'⟩)
    · exact .inl ⟨i, t₁, by rw [fulfilled_get? ht, ite_eq_right h]; exact hi, hts⟩
  · rintro (⟨i, t₁, hi, hts⟩ | h)
    · rw [fulfilled_get? ht] at hi
      split at hi
      · next h =>
        subst h
        simp only [Option.some.injEq] at hi
        subst hi
        exact ⟨tid, t, ht, hsub ts hts⟩
      · exact ⟨i, t₁, hi, hts⟩
    · exact ⟨tid, t, ht, (mem_fulfilledBy.mp h).1⟩

/-- **Pending-release law** (design (V) variant (ii)).
If erasure holds after thread `tid`'s next instruction `F` has run without
changing memory (`F`'s release store is its last memory event, so every
write of `F` fulfils a promise), with ghost `g` (in which `F`'s release
messages are in release mode with their slots), then erasure holds *before*
`F`, with the promises `F` fulfils marked pending. The thread's resource is
its resource after `F`; erasure does not look at the thread's state. This
replaces `PromisedRelease.promiseExempt` at a release promise: Theorem 1′
runs the advance and `F` from the pre-promise configuration (memory-silent
by (S2)) and marks the promise pending. `hcl`: no claim of `g` is by a write
of `F` (claimers are performed writes, `Erase.claimFulf`; an RMW `F` claims
when it runs, not at promise time). -/
theorem Erase.pendingOfFulfil (ht : c.threads[tid]? = some t) (hsub : ∀ p ∈ t'.prom, p ∈ t.prom)
    (hwf : ∀ p ∈ t.prom, ∃ w, c.mem.get? p = some w ∧ w.tid = tid)
    (hcl : ∀ k tw, (k, tw) ∈ g.claims → tw ∉ fulfilledBy t t')
    (E : Erase rF g T (Fulfilled c tid t')) :
    Erase rF { g with pend := fulfilledBy t t' ++ g.pend } T c := by
  have htot : total rF { g with pend := fulfilledBy t t' ++ g.pend } c = total rF g (Fulfilled c tid t') := by
    simp only [total, fulfilled_size, Ghost.slotsRes]
  -- a fulfilled promise is outstanding only at `tid`, which no longer has it
  have hnot : ∀ p ∈ fulfilledBy t t', ¬ Outstanding (Fulfilled c tid t') p := by
    rintro p hp ⟨i, t₁, hi, hpi⟩
    obtain ⟨hpt, hpt'⟩ := mem_fulfilledBy.mp hp
    rw [fulfilled_get? ht] at hi
    split at hi
    · next h =>
      subst h
      simp only [Option.some.injEq] at hi
      subst hi
      exact hpt' hpi
    · next h =>
      obtain ⟨w, hw, htid⟩ := hwf p hpt
      obtain ⟨w', hw', htid'⟩ := E.promWf i t₁ (by rw [fulfilled_get? ht, ite_eq_right h]; exact hi) p hpi
      have : w = w' := Option.some.inj (hw.symm.trans hw')
      subst this
      exact h (htid.symm.trans htid')
  have hset : ∀ p, Settled c { g with pend := fulfilledBy t t' ++ g.pend } p ↔ Settled (Fulfilled c tid t') g p := by
    intro p
    unfold Settled
    simp only [List.mem_append]
    rw [outstanding_fulfilled ht hsub]
    constructor
    · rintro (h | h | h)
      · exact .inl fun h' => h (.inl h')
      · exact .inl (hnot p h)
      · exact .inr h
    · rintro (h | h)
      · by_cases hp : p ∈ fulfilledBy t t'
        · exact .inr (.inl hp)
        · exact .inl fun h' => h'.elim h hp
      · exact .inr (.inr h)
  have hfulf : ∀ x p, Fulf c { g with pend := fulfilledBy t t' ++ g.pend } x p ↔ Fulf (Fulfilled c tid t') g x p := by
    intro x p
    unfold Fulf
    simp only [hset]
    exact Iff.rfl
  have htr : ∀ r x, Tracked c { g with pend := fulfilledBy t t' ++ g.pend } r x ↔ Tracked (Fulfilled c tid t') g r x := by
    intro r x
    unfold Tracked
    simp only [hset]
    exact Iff.rfl
  exact {
    valid := htot ▸ E.valid
    slotIds := E.slotIds
    acqIds := htot ▸ E.acqIds
    relAcq := htot ▸ E.relAcq
    writes := by
      rw [htot]
      intro x hx p
      rw [hfulf]
      exact E.writes x ((htr _ x).mp hx) p
    pure := E.pure
    relExists := E.relExists
    slotsNodup := E.slotsNodup
    slotsDom := htot ▸ E.slotsDom
    slotsPred := E.slotsPred
    promWf := by
      intro i t₁ hi ts hts
      by_cases h : tid = i
      · subst h
        rw [ht] at hi; cases hi
        exact hwf ts hts
      · exact E.promWf i t₁ (by rw [fulfilled_get? ht, ite_eq_right h]; exact hi) ts hts
    promValid := by
      intro i t₁ hi hT ts hts hp w hw
      simp only [List.mem_append, not_or] at hp
      by_cases h : tid = i
      · subst h
        rw [ht] at hi; cases hi
        have hts' : ts ∈ t'.prom :=
          Classical.byContradiction fun hn => hp.1 (mem_fulfilledBy.mpr ⟨hts, hn⟩)
        exact E.promValid tid t' (by rw [fulfilled_get? ht, ite_eq_left rfl]) hT ts hts' hp.2 w hw
      · exact E.promValid i t₁ (by rw [fulfilled_get? ht, ite_eq_right h]; exact hi) hT ts hts hp.2 w hw
    pend := by
      intro ts hts
      rcases List.mem_append.mp hts with h | h
      · obtain ⟨hpt, -⟩ := mem_fulfilledBy.mp h
        obtain ⟨w, hw, -⟩ := hwf ts hpt
        exact ⟨⟨w, hw⟩, ⟨tid, t, ht, hpt⟩⟩
      · obtain ⟨hw, ho⟩ := E.pend ts h
        exact ⟨hw, (outstanding_fulfilled ht hsub).mpr (.inl ho)⟩
    updIds := htot ▸ E.updIds
    relSettled := fun k hk => (hset k.2).mpr (E.relSettled k hk)
    claimsNodup := E.claimsNodup
    claimsAt := by
      intro k tw hk
      obtain ⟨hlt, w', hw', hl, hs, hb⟩ := E.claimsAt k tw hk
      exact ⟨hlt, w', hw', hl, (hset tw).mpr hs, hb⟩
    claimFulf := by
      intro k tw hk ho
      rcases (outstanding_fulfilled ht hsub).mp ho with h | h
      · exact E.claimFulf k tw hk h
      · exact hcl k tw hk h }

end Pending

end Kraken.Promising.SLR
