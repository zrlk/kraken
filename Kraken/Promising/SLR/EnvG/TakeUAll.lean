/-
**Part 1: the cumulative take.** ISA-neutral.
Additive (new file; `EnvG/TakeAll.lean`, `EnvG/TakeAllWr.lean` unchanged).

The original take (`takeAll l tr`, `EnvG/TakeAll.lean`) takes only the
thread's slots of the message `(l, tr)` its acquire load reads. A reader
that **skips** a release (reads `tail = 2` without ever reading `tail = 1`)
strands the slot of the skipped message: it is renamed to the fresh id, and
no later load can take it, since coherence forbids reading the skipped
message again.

The cumulative take `takeUpTo l tr` takes, in increasing order of `ts`, the
thread's slots of `(l, ts)` for **every** `ts ≤ tr`: one `takeAll l ts` round
per timestamp, at the resource and ghost the previous round left (so a slot
renamed by an earlier round is taken under its new id). The renamings are
composed (`composeRen`), so the existing `renameSeen` applies to the result.

**Soundness** (nothing new is assumed): a round is `takeAll`, i.e. a sequence
of `Erase.take` (`SLR/TakeRuleErase.lean`), which has *no* condition on the
taken message's timestamp, and of `Erase.rStepS_take` (`SLR/TakeRule.lean`),
which needs only `ts ≤ wfloor` of the context after the load; a non-forwarded
acquire load of `(l, tr)` gives `tr ≤ wfloor` (`take_floor_acqLoad`), hence
`ts ≤ wfloor` for every round. `RStepS` composes (`RStepS.trans`; its
`AllocIds` frame is stable under the growing acquire table).

What is proved:

- `takeRounds_spec` / `takeUpTo_spec`: the `takeAll_spec` analogue (erasure
  with the taking thread exempt, `RStepS`, `mayWrite` back, ghost growth,
  pending marks).
- `takeUpTo_eq_takeAll`: **the original take is the special case** in which the
  thread has no exposed slot of `l` below `tr` (e.g. a reader that never
  skips): then `takeUpTo l tr = takeAll l tr`, renaming included.
- `takeUpTo_erase`, `takeUpTo_wr`, `takeUpTo_q_ge`: validity-free erasure,
  and the take only adds write permissions.
- `takeUpTo_wr_of_slot`, **`takeUpTo_wr_full`**: a slot of `(l, ts)`,
  `ts ≤ tr`, for an id the thread holds once at the start is taken (through
  the renamings of the earlier rounds); if it holds all of `x`, the thread
  ends with all of `x` and exactly the slot's write set.
- `Pred.takeAtL`, `takeUpTo_held`: a held id survives, its predicate relaxed
  at some timestamps `≤ tr` (`Pred.takeAtL_P`: at a later message the
  relaxation is invisible).

Phase-1 limits as `EnvG/TakeAll.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeAllWr

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

private theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

private theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

/-! ## Definitions -/

/-- Compose renamings: the old pairs are redirected along the new ones, the
new pairs are appended (so `List.lookup` follows the whole chain from an id
renamed first by `old`). -/
def composeRen (old new : List (PredId × PredId)) : List (PredId × PredId) :=
  old.map (fun p => (p.1, (new.lookup p.2).getD p.2)) ++ new

@[simp] theorem composeRen_nil_left (new : List (PredId × PredId)) : composeRen [] new = new := rfl

/-- **One round of the cumulative take**: the existing iterated take of the
message `(l, ts)` at the current resource and ghost, renamings composed. -/
def takeRound (l : Loc) (a : TakeAcc) (ts : Time) : TakeAcc :=
  ⟨(takeAll l ts a.r a.g).r, (takeAll l ts a.r a.g).g, composeRen a.ren (takeAll l ts a.r a.g).ren⟩

/-- **The cumulative take** of an acquire load of `(l, tr)`: the rounds at
`ts = 0, 1, …, tr`. -/
def takeUpTo (l : Loc) (tr : Time) (r : Res) (g : Ghost) : TakeAcc :=
  (List.range (tr + 1)).foldl (takeRound l) ⟨r, g, []⟩

theorem takeRound_r (l : Loc) (a : TakeAcc) (ts : Time) : (takeRound l a ts).r = (takeAll l ts a.r a.g).r := rfl
theorem takeRound_g (l : Loc) (a : TakeAcc) (ts : Time) : (takeRound l a ts).g = (takeAll l ts a.r a.g).g := rfl

/-! ## The original take is the special case -/

/-- **`takeAll` is the cumulative take with nothing exposed below `tr`.** -/
theorem takeUpTo_eq_takeAll {l : Loc} {tr : Time} {r : Res} {g : Ghost}
    (h : ∀ ts < tr, ∀ ι ∈ g.acqIds r.acq l, slotAt g (l, ts) ι = none) : takeUpTo l tr r g = takeAll l tr r g := by
  unfold takeUpTo
  rw [List.range_succ, List.foldl_append]
  have e : ∀ L : List Time, (∀ ts ∈ L, ts < tr) → L.foldl (takeRound l) ⟨r, g, []⟩ = ⟨r, g, []⟩ := by
    intro L hL
    induction L with
    | nil => rfl
    | cons ts L ih =>
      rw [List.foldl_cons]
      have e1 : takeRound l ⟨r, g, []⟩ ts = ⟨r, g, []⟩ := by
        unfold takeRound
        simp only
        rw [takeAll_noSlot (h ts (hL ts (List.mem_cons_self ..)))]
        rfl
      rw [e1]
      exact ih fun t ht => hL t (List.mem_cons_of_mem _ ht)
  rw [e _ fun t ht => List.mem_range.mp ht]
  rfl

/-! ## Erasure, reach and `acqLe` -/

/-- **The rounds of a cumulative take**: erasure (taking thread exempt),
`RStepS` at a context whose floor is at least every round's timestamp,
`mayWrite` back, ghost growth, pending marks. -/
theorem takeRounds_spec {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {tid : Nat} {l : Loc}
    {cx : Ctx} {B : Time} (hn : tid < c.threads.size) (hT : T tid) :
    ∀ (L : List Time) (a : TakeAcc), (∀ ts ∈ L, ts ≤ cx.views.wfloor) → Erase (setRes rF tid a.r) a.g T c →
      Erase (setRes rF tid (L.foldl (takeRound l) a).r) (L.foldl (takeRound l) a).g T c ∧
        RStepS B a.r a.g (L.foldl (takeRound l) a).r (L.foldl (takeRound l) a).g cx ∧
        (∀ x, mayWrite (L.foldl (takeRound l) a).r (L.foldl (takeRound l) a).g x → mayWrite a.r a.g x) ∧
        a.g.Le (L.foldl (takeRound l) a).g ∧ (L.foldl (takeRound l) a).g.pend = a.g.pend
  | [], a, _, E => ⟨E, RStepS.refl _ _ _ _, fun _ h => h, Ghost.Le.refl _, rfl⟩
  | ts :: L, a, hL, E => by
    rw [List.foldl_cons]
    obtain ⟨E1, hR1, hmw1, hle1, hp1⟩ := takeAll_spec (l := l) (B := B) hn hT (hL ts (List.mem_cons_self ..)) E
    obtain ⟨E2, hR2, hmw2, hle2, hp2⟩ :=
      takeRounds_spec hn hT L (takeRound l a ts) (fun t ht => hL t (List.mem_cons_of_mem _ ht)) E1
    exact ⟨E2, hR1.trans hR2 (Nat.le_refl _), fun x hx => hmw1 x (hmw2 x hx), hle1.trans hle2, hp2.trans hp1⟩

/-- **The cumulative take of an acquire load** (`takeAll_spec`'s analogue):
the floor bound is the one of the message read. -/
theorem takeUpTo_spec {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {tid : Nat} {l : Loc} {tr : Time}
    {cx : Ctx} {B : Time} {r : Res} {g : Ghost} (hn : tid < c.threads.size) (hT : T tid)
    (hfl : tr ≤ cx.views.wfloor) (E : Erase (setRes rF tid r) g T c) :
    Erase (setRes rF tid (takeUpTo l tr r g).r) (takeUpTo l tr r g).g T c ∧
      RStepS B r g (takeUpTo l tr r g).r (takeUpTo l tr r g).g cx ∧
      (∀ x, mayWrite (takeUpTo l tr r g).r (takeUpTo l tr r g).g x → mayWrite r g x) ∧
      g.Le (takeUpTo l tr r g).g ∧ (takeUpTo l tr r g).g.pend = g.pend :=
  takeRounds_spec (B := B) hn hT _ ⟨r, g, []⟩
    (fun _ hts => Nat.le_trans (Nat.lt_succ_iff.mp (List.mem_range.mp hts)) hfl) E

/-- **The cumulative take keeps validity-free erasure.** -/
theorem takeUpTo_erase {rF : Nat → Res} {c : Config I} {tid : Nat} {l : Loc} {tr : Time} {r : Res} {g : Ghost}
    (hn : tid < c.threads.size) (E : Erase (setRes rF tid r) g (fun _ => True) c) :
    Erase (setRes rF tid (takeUpTo l tr r g).r) (takeUpTo l tr r g).g (fun _ => True) c :=
  (takeUpTo_spec (cx := { views := { vwNew := tr }, prom := [], mem := c.mem }) (B := 0) hn trivial
    (Nat.le_max_left _ _) E).1

theorem takeUpTo_le (l : Loc) (tr : Time) (r : Res) (g : Ghost) : g.Le (takeUpTo l tr r g).g := by
  have : ∀ (L : List Time) (a : TakeAcc), a.g.Le (L.foldl (takeRound l) a).g := by
    intro L
    induction L with
    | nil => exact fun a => Ghost.Le.refl a.g
    | cons ts L ih =>
      intro a
      rw [List.foldl_cons]
      exact (takeFold_le l ts (a.g.acqIds a.r.acq l) ⟨a.r, a.g, []⟩).trans (ih (takeRound l a ts))
  exact this _ ⟨r, g, []⟩

/-! ## Write permissions -/

/-- **The rounds add a permission.** -/
theorem takeRounds_wr (l : Loc) (x : Loc) :
    ∀ (L : List Time) (a : TakeAcc), ∃ d : Perm,
      ((L.foldl (takeRound l) a).r.wr x).q = (a.r.wr x).q + d.q ∧
        ∀ p, ((L.foldl (takeRound l) a).r.wr x).X p ↔ (a.r.wr x).X p ∨ d.X p
  | [], _ => ⟨Perm.unit, (Rat.add_zero _).symm, fun _ => ⟨.inl, fun h => h.elim id False.elim⟩⟩
  | ts :: L, a => by
    rw [List.foldl_cons]
    obtain ⟨e, he, hX⟩ := takeFold_wr l ts x (a.g.acqIds a.r.acq l) ⟨a.r, a.g, []⟩
    obtain ⟨d, hd, hXd⟩ := takeRounds_wr l x L (takeRound l a ts)
    rw [takeRound_r] at hd hXd
    change ((takeAll l ts a.r a.g).r.wr x).q = (a.r.wr x).q + e.q at he
    change ∀ p, ((takeAll l ts a.r a.g).r.wr x).X p ↔ (a.r.wr x).X p ∨ e.X p at hX
    refine ⟨e.op d, ?_, fun p => ?_⟩
    · rw [hd, he]; show _ = _ + (e.q + d.q); rw [Rat.add_assoc]
    · rw [hXd, hX]; show _ ↔ _ ∨ (e.X p ∨ d.X p); exact or_assoc

/-- **The cumulative take adds a permission.** -/
theorem takeUpTo_wr (l : Loc) (tr : Time) (r : Res) (g : Ghost) (x : Loc) :
    ∃ d : Perm, ((takeUpTo l tr r g).r.wr x).q = (r.wr x).q + d.q ∧
      ∀ p, ((takeUpTo l tr r g).r.wr x).X p ↔ (r.wr x).X p ∨ d.X p :=
  takeRounds_wr l x _ ⟨r, g, []⟩

/-- The cumulative take does not decrease any fraction. -/
theorem takeUpTo_q_ge (l : Loc) (tr : Time) (r : Res) (g : Ghost) (x : Loc) :
    (r.wr x).q ≤ ((takeUpTo l tr r g).r.wr x).q := by
  obtain ⟨d, hd, -⟩ := takeUpTo_wr l tr r g x
  rw [hd]; have := d.nonneg; grind

theorem takeUpTo_wr_pos (l : Loc) (tr : Time) {r : Res} (g : Ghost) {x : Loc} (h : 0 < (r.wr x).q) :
    0 < ((takeUpTo l tr r g).r.wr x).q := by
  have := takeUpTo_q_ge l tr r g x; grind

/-! ## A slot below the message read survives the earlier rounds -/

/-- One take step at another message keeps a slot of `(l, ts)` (possibly
renamed to the fresh id) with its resource, for an id still held. -/
theorem takeStep_slot_keep {l : Loc} {ts' ts : Time} (hne : ts ≠ ts') (a : TakeAcc) (ι : PredId)
    (hιlt : ι < a.g.acqTab.length) {s0 : Slot} (hs0 : s0 ∈ a.g.u) (hk : s0.key = (l, ts))
    (hacq : 1 ≤ a.r.acq l s0.id) (hlt : s0.id < a.g.acqTab.length) :
    ∃ s1 ∈ (takeStep l ts' a ι).g.u, s1.key = (l, ts) ∧ s1.res = s0.res ∧
      1 ≤ (takeStep l ts' a ι).r.acq l s1.id ∧ s1.id < (takeStep l ts' a ι).g.acqTab.length := by
  unfold takeStep
  split
  · next s _ =>
    refine ⟨takeSlot l ι a.g.acqTab.length ts' s0, List.mem_map_of_mem hs0, ?_, ?_, ?_, ?_⟩
    · unfold takeSlot; split <;> simp [hk]
    · unfold takeSlot; split
      · simp only [hk]; rw [ite_f hne]
      · rfl
    · unfold takeSlot
      by_cases h : s0.key.1 = l ∧ s0.id = ι
      · rw [ite_t h]
        simp only [takeRes, Res.op, swapAcq]
        have hne' : a.g.acqTab.length ≠ ι := Nat.ne_of_gt hιlt
        simp only [true_and, hne', ↓reduceIte]
        omega
      · rw [ite_f h]
        have hne1 : s0.id ≠ ι := fun e => h ⟨by rw [hk], e⟩
        exact Nat.le_trans hacq (takeRes_acq_ge hne1 (Nat.ne_of_lt hlt))
    · rw [takeGhost_length]
      unfold takeSlot; split
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt hlt
  · exact ⟨s0, hs0, hk, rfl, hacq, hlt⟩

/-- An iterated take at another message keeps such a slot. -/
theorem takeFold_slot_keep {l : Loc} {ts' ts : Time} (hne : ts ≠ ts') :
    ∀ (ids : List PredId) (a : TakeAcc), (∀ j ∈ ids, j < a.g.acqTab.length) →
      ∀ {s0 : Slot}, s0 ∈ a.g.u → s0.key = (l, ts) → 1 ≤ a.r.acq l s0.id → s0.id < a.g.acqTab.length →
      ∃ s1 ∈ (ids.foldl (takeStep l ts') a).g.u, s1.key = (l, ts) ∧ s1.res = s0.res ∧
        1 ≤ (ids.foldl (takeStep l ts') a).r.acq l s1.id ∧ s1.id < (ids.foldl (takeStep l ts') a).g.acqTab.length
  | [], _, _, s0, hs0, hk, hacq, hlt => ⟨s0, hs0, hk, rfl, hacq, hlt⟩
  | j :: ids, a, hids, s0, hs0, hk, hacq, hlt => by
    rw [List.foldl_cons]
    obtain ⟨s1, hs1, hk1, hr1, ha1, hl1⟩ :=
      takeStep_slot_keep hne a j (hids j (List.mem_cons_self ..)) hs0 hk hacq hlt
    have hids' : ∀ j' ∈ ids, j' < (takeStep l ts' a j).g.acqTab.length := fun j' hj' =>
      Nat.lt_of_lt_of_le (hids j' (List.mem_cons_of_mem _ hj')) (by
        unfold takeStep; split
        · rw [takeGhost_length]; exact Nat.le_succ _
        · exact Nat.le_refl _)
    obtain ⟨s2, hs2, hk2, hr2, ha2, hl2⟩ := takeFold_slot_keep hne ids _ hids' hs1 hk1 ha1 hl1
    exact ⟨s2, hs2, hk2, hr2.trans hr1, ha2, hl2⟩

/-- **A round at another message keeps a slot of `(l, ts)`** for an id held
once (validity, from the erasure after the round, gives "once" again). -/
theorem takeRound_slot_keep {rF : Nat → Res} {c : Config I} {tid : Nat} (hn : tid < c.threads.size) {l : Loc}
    {ts' ts : Time} (hne : ts ≠ ts') (a : TakeAcc) (E : Erase (setRes rF tid a.r) a.g (fun _ => True) c)
    {s0 : Slot} (hs0 : s0 ∈ a.g.u) (hk : s0.key = (l, ts)) (hacq : a.r.acq l s0.id = 1) :
    ∃ s1 ∈ (takeRound l a ts').g.u, s1.key = (l, ts) ∧ s1.res = s0.res ∧ (takeRound l a ts').r.acq l s1.id = 1 := by
  obtain ⟨s1, hs1, hk1, hr1, ha1, -⟩ := takeFold_slot_keep hne (a.g.acqIds a.r.acq l) ⟨a.r, a.g, []⟩
    (fun _ hj => (mem_acqIds hj).2) hs0 hk (Nat.le_of_eq hacq.symm) (E.slotIds s0 hs0)
  have E1 := takeAll_erase (l := l) (tr := ts') hn E
  have hle := E1.thread_acq_le hn l s1.id
  exact ⟨s1, hs1, hk1, hr1, by rw [takeRound_r]; exact Nat.le_antisymm hle ha1⟩

/-- `takeAll` adds the slot of a held id, and a remainder (`takeAll_wr_full`'s
first steps, kept as a decomposition). -/
theorem takeAll_wr_of_slot {rF : Nat → Res} {c : Config I} {tid : Nat} {l : Loc} {tr : Time} {r : Res} {g : Ghost}
    (E : Erase (setRes rF tid r) g (fun _ => True) c) {s : Slot} (hs : s ∈ g.u)
    (hk : s.key = (l, tr)) (hι : r.acq l s.id = 1) (x : Loc) :
    ∃ d : Perm, ((takeAll l tr r g).r.wr x).q = (r.wr x).q + (s.res.wr x).q + d.q ∧
      ∀ p, ((takeAll l tr r g).r.wr x).X p ↔ (r.wr x).X p ∨ (s.res.wr x).X p ∨ d.X p := by
  have hsl := slotAt_of_mem E.slotsNodup hs
  rw [hk] at hsl
  have hmem : s.id ∈ g.acqIds r.acq l := by
    unfold Ghost.acqIds
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (E.slotIds s hs), by simp [hι]⟩
  exact takeFold_wr_of_slot l tr x _ ⟨r, g, []⟩ hmem (acqIds_nodup _ _ _) (fun _ hj => (mem_acqIds hj).2) hsl

/-- **The rounds take a slot of a message among them** (renamed or not by the
earlier rounds), and a remainder. -/
theorem takeRounds_wr_of_slot {rF : Nat → Res} {c : Config I} {tid : Nat} (hn : tid < c.threads.size) (l : Loc)
    (x : Loc) {ts : Time} :
    ∀ (L : List Time) (a : TakeAcc), ts ∈ L → L.Nodup → Erase (setRes rF tid a.r) a.g (fun _ => True) c →
      ∀ {s : Slot}, s ∈ a.g.u → s.key = (l, ts) → a.r.acq l s.id = 1 → ∃ d : Perm,
        ((L.foldl (takeRound l) a).r.wr x).q = (a.r.wr x).q + (s.res.wr x).q + d.q ∧
        ∀ p, ((L.foldl (takeRound l) a).r.wr x).X p ↔ (a.r.wr x).X p ∨ (s.res.wr x).X p ∨ d.X p
  | [], _, h, _, _, _, _, _, _ => absurd h List.not_mem_nil
  | t :: L, a, hm, hnd, E, s, hs, hk, hacq => by
    rw [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    have E1 : Erase (setRes rF tid (takeRound l a t).r) (takeRound l a t).g (fun _ => True) c :=
      takeAll_erase hn E
    by_cases ht : t = ts
    · subst ht
      obtain ⟨e, he, hX⟩ := takeAll_wr_of_slot E hs hk hacq x
      obtain ⟨d, hd, hXd⟩ := takeRounds_wr l x L (takeRound l a t)
      rw [takeRound_r] at hd hXd
      refine ⟨e.op d, ?_, fun p => ?_⟩
      · rw [hd, he]; show _ = _ + (e.q + d.q); grind
      · rw [hXd, hX]; show _ ↔ _ ∨ _ ∨ (e.X p ∨ d.X p); grind
    · have hm' : ts ∈ L := (List.mem_cons.mp hm).resolve_left (fun h => ht h.symm)
      obtain ⟨s1, hs1, hk1, hr1, ha1⟩ := takeRound_slot_keep hn (Ne.symm ht) a E hs hk hacq
      obtain ⟨d, hd, hXd⟩ := takeRounds_wr_of_slot hn l x L (takeRound l a t) hm' hnd.2 E1 hs1 hk1 ha1
      obtain ⟨e, he, hX⟩ := takeFold_wr l t x (a.g.acqIds a.r.acq l) ⟨a.r, a.g, []⟩
      change ((takeRound l a t).r.wr x).q = (a.r.wr x).q + e.q at he
      change ∀ p, ((takeRound l a t).r.wr x).X p ↔ (a.r.wr x).X p ∨ e.X p at hX
      rw [hr1] at hd hXd
      refine ⟨e.op d, ?_, fun p => ?_⟩
      · rw [hd, he]; show _ = _ + (e.q + d.q); grind
      · rw [hXd, hX]; show _ ↔ _ ∨ _ ∨ (e.X p ∨ d.X p); grind

/-- **A slot of `(l, ts)`, `ts ≤ tr`, of an id held once is taken** by the
cumulative take of `(l, tr)`: its permission is added (with a remainder). -/
theorem takeUpTo_wr_of_slot {rF : Nat → Res} {c : Config I} {tid : Nat} {l : Loc} {tr ts : Time} {r : Res}
    {g : Ghost} (hn : tid < c.threads.size) (E : Erase (setRes rF tid r) g (fun _ => True) c) {s : Slot}
    (hs : s ∈ g.u) (hk : s.key = (l, ts)) (hts : ts ≤ tr) (hι : r.acq l s.id = 1) (x : Loc) :
    ∃ d : Perm, ((takeUpTo l tr r g).r.wr x).q = (r.wr x).q + (s.res.wr x).q + d.q ∧
      ∀ p, ((takeUpTo l tr r g).r.wr x).X p ↔ (r.wr x).X p ∨ (s.res.wr x).X p ∨ d.X p :=
  takeRounds_wr_of_slot hn l x _ ⟨r, g, []⟩ (List.mem_range.mpr (Nat.lt_succ_of_le hts)) List.nodup_range E hs hk hι

/-- **A skipped (or read) slot holding all of `x` is all of the thread's `x`**
after the cumulative take: fraction `1`, write set the slot's
(`takeAll_wr_full` for every `ts ≤ tr`). -/
theorem takeUpTo_wr_full {rF : Nat → Res} {c : Config I} {tid : Nat} {l : Loc} {tr ts : Time} {r : Res}
    {g : Ghost} (hn : tid < c.threads.size) (E : Erase (setRes rF tid r) g (fun _ => True) c) {s : Slot}
    (hs : s ∈ g.u) (hk : s.key = (l, ts)) (hts : ts ≤ tr) (hι : r.acq l s.id = 1) {x : Loc}
    (hq : (s.res.wr x).q = 1) :
    ((takeUpTo l tr r g).r.wr x).q = 1 ∧ ∀ p, ((takeUpTo l tr r g).r.wr x).X p ↔ (s.res.wr x).X p := by
  obtain ⟨d, hd, hXd⟩ := takeUpTo_wr_of_slot hn E hs hk hts hι x
  have hle := (takeUpTo_erase (l := l) (tr := tr) hn E).thread_q_le hn x
  have h0 := (r.wr x).nonneg
  have h1 := d.nonneg
  have hr0 : (r.wr x).q = 0 := by grind
  have hd0 : d.q = 0 := by grind
  refine ⟨by grind, fun p => ?_⟩
  rw [hXd]
  exact ⟨fun h => h.elim (fun h' => absurd h' ((r.wr x).zero hr0 p))
    (fun h' => h'.elim id fun h'' => absurd h'' (d.zero hd0 p)), fun h => .inr (.inl h)⟩

/-! ## A held acquire id survives -/

/-- `φ` relaxed at each timestamp of `L` in turn (`Pred.takeAt`). -/
def _root_.Kraken.Promising.SLR.Pred.takeAtL (φ : Pred) (L : List Time) : Pred := L.foldl Pred.takeAt φ

@[simp] theorem _root_.Kraken.Promising.SLR.Pred.takeAtL_nil (φ : Pred) : φ.takeAtL [] = φ := rfl

theorem _root_.Kraken.Promising.SLR.Pred.takeAtL_snoc (φ : Pred) (L : List Time) (t : Time) :
    φ.takeAtL (L ++ [t]) = (φ.takeAtL L).takeAt t := by
  simp [Pred.takeAtL, List.foldl_append]

/-- **What a relaxed predicate says**: the unit resource at one of the
relaxed timestamps, or the original predicate. At a message above all of
them it is the original predicate. -/
theorem _root_.Kraken.Promising.SLR.Pred.takeAtL_P :
    ∀ {L : List Time} {φ : Pred} {v : Val} {m : Memory} {V : View} {r : Res}, (φ.takeAtL L).P v m V r →
      (∃ t ∈ L, V = t ∧ r = Res.unit) ∨ φ.P v m V r := by
  intro L
  induction L with
  | nil => exact fun h => .inr h
  | cons t L ih =>
    intro φ v m V r h
    rcases ih (φ := φ.takeAt t) h with ⟨t', ht', h'⟩ | h
    · exact .inl ⟨t', List.mem_cons_of_mem _ ht', h'⟩
    · rcases h with ⟨h1, h2⟩ | h
      · exact .inl ⟨t, List.mem_cons_self .., h1, h2⟩
      · exact .inr h

theorem _root_.Kraken.Promising.SLR.Pred.takeAtL_P_of_lt {φ : Pred} {L : List Time} {v : Val} {m : Memory}
    {V : View} {r : Res} (hL : ∀ t ∈ L, t < V) (h : (φ.takeAtL L).P v m V r) : φ.P v m V r :=
  (Pred.takeAtL_P h).resolve_left fun ⟨t, ht, e, _⟩ => Nat.lt_irrefl _ (e ▸ hL t ht)

theorem _root_.Kraken.Promising.SLR.Pred.le_takeAtL :
    ∀ (L : List Time) {φ : Pred} {v : Val} {m : Memory} {V : View} {r : Res}, φ.P v m V r →
      (φ.takeAtL L).P v m V r := by
  intro L
  induction L with
  | nil => exact fun h => h
  | cons t L ih =>
    intro φ v m V r h
    exact ih (φ := φ.takeAt t) (.inr h)

/-- **A held id survives the rounds**, its predicate relaxed at some of the
rounds' timestamps. -/
theorem takeRounds_held (l : Loc) (P0 : Pred) :
    ∀ (L : List Time) (a : TakeAcc) (K : List Time), (∀ t ∈ K, t ∈ L ∨ t ∈ K) →
      (∃ ι, 1 ≤ a.r.acq l ι ∧ ι < a.g.acqTab.length ∧ a.g.acqPred ι = P0.takeAtL K) →
      ∃ ι' K', (∀ t ∈ K', t ∈ K ∨ t ∈ L) ∧ 1 ≤ (L.foldl (takeRound l) a).r.acq l ι' ∧
        ι' < (L.foldl (takeRound l) a).g.acqTab.length ∧ (L.foldl (takeRound l) a).g.acqPred ι' = P0.takeAtL K'
  | [], a, K, _, ⟨ι, h1, h2, h3⟩ => ⟨ι, K, fun t ht => .inl ht, h1, h2, h3⟩
  | ts :: L, a, K, _, ⟨ι, h1, h2, h3⟩ => by
    rw [List.foldl_cons]
    obtain ⟨ι', h1', h2', h3'⟩ := takeAll_held (l := l) (tr := ts) (r := a.r) (g := a.g) h1 h2
    have hstep : ∃ K₁, (∀ t ∈ K₁, t ∈ K ∨ t = ts) ∧ (takeRound l a ts).g.acqPred ι' = P0.takeAtL K₁ := by
      rw [takeRound_g]
      rcases h3' with h | h
      · exact ⟨K, fun t ht => .inl ht, by rw [h, h3]⟩
      · refine ⟨K ++ [ts], fun t ht => ?_, by rw [h, h3, Pred.takeAtL_snoc]⟩
        rcases List.mem_append.mp ht with ht | ht
        · exact .inl ht
        · exact .inr (List.mem_singleton.mp ht)
    obtain ⟨K₁, hK₁, hP₁⟩ := hstep
    obtain ⟨ι'', K', hK', r1, r2, r3⟩ := takeRounds_held l P0 L (takeRound l a ts) K₁ (fun t ht => .inr ht)
      ⟨ι', h1', h2', hP₁⟩
    refine ⟨ι'', K', fun t ht => ?_, r1, r2, r3⟩
    rcases hK' t ht with h | h
    · rcases hK₁ t h with h | h
      · exact .inl h
      · exact .inr (h ▸ List.mem_cons_self ..)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- **A held id survives the cumulative take**, its predicate relaxed at
some timestamps `≤ tr` (`takeAll_held` for every round). -/
theorem takeUpTo_held {l : Loc} {tr : Time} {r : Res} {g : Ghost} {ι : PredId} (h1 : 1 ≤ r.acq l ι)
    (h2 : ι < g.acqTab.length) :
    ∃ ι' K, (∀ t ∈ K, t ≤ tr) ∧ 1 ≤ (takeUpTo l tr r g).r.acq l ι' ∧ ι' < (takeUpTo l tr r g).g.acqTab.length ∧
      (takeUpTo l tr r g).g.acqPred ι' = (g.acqPred ι).takeAtL K := by
  obtain ⟨ι', K, hK, r1, r2, r3⟩ := takeRounds_held l (g.acqPred ι) _ ⟨r, g, []⟩ [] (fun _ h => .inr h)
    ⟨ι, h1, h2, rfl⟩
  refine ⟨ι', K, fun t ht => ?_, r1, r2, r3⟩
  rcases hK t ht with h | h
  · exact absurd h List.not_mem_nil
  · exact Nat.lt_succ_iff.mp (List.mem_range.mp h)

#print axioms takeUpTo_spec
#print axioms takeUpTo_eq_takeAll
#print axioms takeUpTo_wr_full
#print axioms takeUpTo_held

end Kraken.Promising.SLR.EnvG
