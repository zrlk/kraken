/-
Conservativity of the promising machine.

For a single thread with no outstanding promises, the promising rules of
`Kraken.Promising.Thread` degenerate to a sequential memory: every read
returns the last write to its location and every store appends. This file
states and proves that against the ISA-independent event tree (`EvTree`), so
that it covers both ISA adapters at once.

- `seqRun` is the sequential interpreter of event trees.
- `Memory.lastWrite` is the timestamp of the last write to a location.
- `Ctx.Seq tid c` is the invariant on a thread's context under which the
  promising rules are deterministic: no promises, every view at most `|M|`,
  and the coherence view of each location at or past its last write.
- `runTree_sound`: every successful promising run of a tree from a `Seq`
  context is a sequential run (and ends in a `Seq` context);
  `runTree_complete`: for trees without exclusives, conversely.
- `stepOne_sound`: the same lifted to one instruction of a `Thread`;
  `succs_sound`: to a promise-free step of a one-thread `Config`;
  `reachablePF_sound`: to promise-free runs (`ReachablePF`, the fragment of
  `Reachable` whose steps leave no promise outstanding).

Not covered: runs that promise and later fulfil (they are also sequentially
explainable for one thread, but that needs reasoning about the fulfil rule,
which is not done here). The connection of `seqRun` to each ISA's
single-threaded judgment (`Effects.All` on a `dmem` merged with the shared
locations' last writes) is `Kraken.Promising.SeqLink`, `SeqLinkAArch64` and
`SeqLinkX64`.

Note: the invariant is `lastWrite l ≤ coh l`, not the equality
`coh l = lastWrite l`. The read rule raises `coh(l)` to the read's post-view,
which includes the address view and may exceed the last write to `l`; what
determinism needs is only that `coh(l)` is at or past the last write and at
most `|M|`.
-/
import Kraken.Promising.Rel

namespace Kraken.Promising

/-! ## The sequential interpreter -/

/-- The sequential meaning of an event tree against a memory: reads return
the last write (`finalVal`), stores append. A store exclusive may also fail;
an RMW whose operation declines (`op old = none`) does
not write. `tid` tags the appended messages. -/
def seqRun {σ : Type} (tid : Nat) (mem : Memory) : EvTree σ → List (σ × Memory)
  | .done s => [(s, mem)]
  | .fault _ => []
  | .choose n k => (List.finRange n).flatMap fun i => seqRun tid mem (k i)
  | .load _ _ l ret => seqRun tid mem (ret (mem.finalVal l))
  | .store _ xcl l v ret =>
    seqRun tid (mem.append { loc := l, val := v, tid }).1 (ret true) ++
      (if xcl then seqRun tid mem (ret false) else [])
  | .rmw _ _ l op ret =>
    let old := mem.finalVal l
    match op old with
    | some v => seqRun tid (mem.append { loc := l, val := v, tid }).1 (ret old)
    | none => seqRun tid mem (ret old)
  | .fence _ ret => seqRun tid mem (ret ())

/-- A tree with no store exclusive and no RMW: the fragment on which the
promising and sequential runs coincide exactly. -/
def EvTree.NoExcl {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, NoExcl (k i)
  | .load _ _ _ ret => ∀ v, NoExcl (ret v)
  | .store _ xcl _ _ ret => xcl = false ∧ ∀ b, NoExcl (ret b)
  | .rmw .. => False
  | .fence _ ret => NoExcl (ret ())

/-! ## Memory: the last write to a location -/

/-- `omega` after unfolding the `Nat` abbreviations `Time` and `View`, which
this toolchain's `omega` does not see through. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

namespace Memory

/-- The greatest `t ≤ n` at which `m` holds a write to `l`, else `0`. -/
def lastWriteBelow (m : Memory) (l : Loc) : Nat → Time
  | 0 => 0
  | n + 1 =>
    match m.get? (n + 1) with
    | some w => if w.loc = l then n + 1 else m.lastWriteBelow l n
    | none => m.lastWriteBelow l n

/-- The timestamp of the last write to `l`: the greatest `t ≤ |M|` holding a
write to `l`, else `0` (the initial write). -/
def lastWrite (m : Memory) (l : Loc) : Time := m.lastWriteBelow l m.last

theorem get?_eq_none_of_last_lt (m : Memory) {t : Time} (h : m.last < t) : m.get? t = none := by
  unfold last at h
  unfold get?
  rw [ite_eq_right (by omega_t)]
  exact Array.getElem?_eq_none (by omega_t)

theorem get?_zero (m : Memory) : m.get? 0 = none := by simp [get?]

theorem last_le_of_get?_eq_some (m : Memory) {t : Time} {w : Msg} (h : m.get? t = some w) : t ≤ m.last := by
  rcases Nat.lt_or_ge m.last t with hlt | hge
  · rw [get?_eq_none_of_last_lt m hlt] at h; cases h
  · exact hge

theorem lastWriteBelow_le (m : Memory) (l : Loc) : ∀ n, m.lastWriteBelow l n ≤ n
  | 0 => Nat.le_refl _
  | n + 1 => by
    have ih := lastWriteBelow_le m l n
    cases hw : m.get? (n + 1) with
    | none => simp only [lastWriteBelow, hw]; omega_t
    | some w => simp only [lastWriteBelow, hw]; split <;> omega_t

theorem lastWrite_le (m : Memory) (l : Loc) : m.lastWrite l ≤ m.last := lastWriteBelow_le m l _

/-- A nonzero `lastWriteBelow` is a write to `l`. -/
theorem get?_lastWriteBelow (m : Memory) (l : Loc) :
    ∀ n, m.lastWriteBelow l n ≠ 0 → ∃ w, m.get? (m.lastWriteBelow l n) = some w ∧ w.loc = l
  | 0, h => absurd rfl h
  | n + 1, h => by
    cases hw : m.get? (n + 1) with
    | none =>
      simp only [lastWriteBelow, hw] at h ⊢
      exact get?_lastWriteBelow m l n h
    | some w =>
      by_cases hl : w.loc = l
      · simp only [lastWriteBelow, hw, hl, ite_true]
        exact ⟨w, rfl, hl⟩
      · simp only [lastWriteBelow, hw, hl, ite_false] at h ⊢
        exact get?_lastWriteBelow m l n h

/-- Nothing in `(lastWriteBelow n, n]` is a write to `l`. -/
theorem not_write_of_lastWriteBelow_lt (m : Memory) (l : Loc) :
    ∀ n (t : Nat) w, m.lastWriteBelow l n < t → t ≤ n → m.get? t = some w → w.loc ≠ l
  | 0, t, _, h1, h2, _ => by omega_t
  | n + 1, t, w, h1, h2, h3 => by
    have ih := not_write_of_lastWriteBelow_lt m l n t w
    rcases Nat.lt_or_ge t (n + 1) with ht | ht
    · refine ih ?_ (by omega_t) h3
      cases hw : m.get? (n + 1) with
      | none => simp only [lastWriteBelow, hw] at h1; exact h1
      | some w' =>
        simp only [lastWriteBelow, hw] at h1
        split at h1
        · omega_t
        · exact h1
    · have : t = n + 1 := by omega_t
      subst this
      intro hl
      simp only [lastWriteBelow, h3, hl, ite_true] at h1
      omega_t

theorem not_write_of_lastWrite_lt (m : Memory) (l : Loc) {t : Time} {w : Msg}
    (h1 : m.lastWrite l < t) (h3 : m.get? t = some w) : w.loc ≠ l :=
  not_write_of_lastWriteBelow_lt m l m.last t w h1 (m.last_le_of_get?_eq_some h3) h3

theorem read?_eq_some (m : Memory) {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) :
    (t = 0 ∧ v = m.initVal l) ∨ ∃ w, m.get? t = some w ∧ w.loc = l ∧ v = w.val := by
  unfold read? at h
  split at h
  · left; cases h; exact ⟨‹_›, rfl⟩
  · right
    split at h
    · next w hw =>
      split at h
      · next hl => cases h; exact ⟨w, hw, by simpa using hl, rfl⟩
      · cases h
    · cases h

theorem lastWriteBelow_append (m : Memory) (w : Msg) (l : Loc) :
    ∀ n, n ≤ m.last → (m.append w).1.lastWriteBelow l n = m.lastWriteBelow l n
  | 0, _ => rfl
  | n + 1, h => by
    unfold lastWriteBelow
    rw [get?_append_of_le m w (n + 1) h, lastWriteBelow_append m w l n (by omega_t)]

theorem lastWrite_append (m : Memory) (w : Msg) (l : Loc) :
    (m.append w).1.lastWrite l = if w.loc = l then m.last + 1 else m.lastWrite l := by
  show (m.append w).1.lastWriteBelow l (m.append w).1.last = _
  rw [last_append]
  simp only [lastWriteBelow, get?_append_last, lastWriteBelow_append m w l m.last (Nat.le_refl _)]
  rfl

/-- A message of the appended memory is the new one or an old one. -/
theorem get?_append_eq_some (m : Memory) (w : Msg) {t : Nat} {w' : Msg} (h : (m.append w).1.get? t = some w') :
    (t ≤ m.last ∧ m.get? t = some w') ∨ (t = m.last + 1 ∧ w' = w) := by
  rcases Nat.lt_or_ge m.last t with hlt | hge
  · right
    have ht : t ≤ m.last + 1 := by
      have := (m.append w).1.last_le_of_get?_eq_some h
      rw [last_append] at this; exact this
    have : t = m.last + 1 := by omega_t
    subst this
    rw [get?_append_last] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · left
    rw [get?_append_of_le m w t hge] at h
    exact ⟨hge, h⟩

/-- Every memory is a sequence of appends to an empty one. -/
private theorem push_induction (P : Memory → Prop) (h0 : ∀ init, P { init, msgs := #[] })
    (hp : ∀ m w, P m → P (m.append w).1) : ∀ m, P m := by
  intro ⟨init, ⟨xs⟩⟩
  have : ∀ ys : List Msg, P { init, msgs := ys.reverse.toArray } := by
    intro ys
    induction ys with
    | nil => exact h0 init
    | cons y ys ih =>
      have := hp _ y ih
      simpa [append] using this
  simpa using this xs.reverse

/-- Reading at the last write to `l` gives the final value of `l`. -/
theorem read?_lastWrite (m : Memory) (l : Loc) : m.read? l (m.lastWrite l) = some (m.finalVal l) := by
  induction m using push_induction with
  | h0 init => simp [lastWrite, lastWriteBelow, last, read?, finalVal]
  | hp m w ih =>
    rw [lastWrite_append]
    have hfv : (m.append w).1.finalVal l = if w.loc = l then w.val else m.finalVal l := by
      unfold finalVal; simp only [append]
      by_cases hl : w.loc = l
      · rw [Array.findRev?_push_of_pos (by simpa using hl), ite_eq_left hl]
      · rw [Array.findRev?_push_of_neg (by simpa using hl), ite_eq_right hl]
        rfl
    rw [hfv]
    by_cases hl : w.loc = l
    · rw [ite_eq_left hl, ite_eq_left hl]; subst hl; exact read?_append_last m w
    · rw [ite_eq_right hl, ite_eq_right hl, ← ih]
      unfold read?
      rw [get?_append_of_le m w _ (m.lastWrite_le l)]
      rfl

theorem writeIn_iff (m : Memory) (l : Loc) (lo hi : Time) :
    m.writeIn l lo hi = true ↔ ∃ (t : Nat) (w : Msg), lo < t ∧ t ≤ hi ∧ m.get? t = some w ∧ w.loc = l := by
  simp only [writeIn, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    split at h
    · next w hw => exact ⟨lo + i + 1, w, by omega_t, by omega_t, hw, by simpa using h⟩
    · cases h
  · rintro ⟨t, w, h1, h2, h3, h4⟩
    refine ⟨t - lo - 1, by omega_t, ?_⟩
    have : lo + (t - lo - 1) + 1 = t := by omega_t
    rw [this, h3]; simp [h4]

/-- No write to `l` is after its last write. -/
theorem writeIn_lastWrite (m : Memory) (l : Loc) (hi : Time) : m.writeIn l (m.lastWrite l) hi = false := by
  rw [Bool.eq_false_iff, Ne, writeIn_iff]
  rintro ⟨t, w, h1, _, h3, h4⟩
  exact m.not_write_of_lastWrite_lt l h1 h3 h4

/-- Any interval ending at or after the last write and starting before it
contains a write to `l`. -/
theorem writeIn_of_lt_lastWrite (m : Memory) (l : Loc) {t hi : Time} (h1 : t < m.lastWrite l)
    (h2 : m.lastWrite l ≤ hi) : m.writeIn l t hi = true := by
  rw [writeIn_iff]
  obtain ⟨w, hw, hl⟩ := m.get?_lastWriteBelow l m.last (by unfold lastWrite at h1; omega_t)
  exact ⟨m.lastWrite l, w, h1, h2, hw, hl⟩

/-- The only `t ≤ |M|` that reads `l` with no later write to `l` in
`(t, bound]`, for `lastWrite l ≤ bound`, is `lastWrite l` itself. -/
theorem read?_eq_none_or_writeIn (m : Memory) (l : Loc) {t bound : Time} (ht : t ≤ m.last)
    (hne : t ≠ m.lastWrite l) (hb : m.lastWrite l ≤ bound) :
    m.read? l t = none ∨ m.writeIn l t bound = true := by
  rcases Nat.lt_or_ge t (m.lastWrite l) with hlt | hge
  · exact .inr (m.writeIn_of_lt_lastWrite l hlt hb)
  · left
    have hlt : m.lastWrite l < t := Nat.lt_of_le_of_ne hge (Ne.symm hne)
    match h : m.read? l t with
    | none => rfl
    | some v =>
      rcases m.read?_eq_some h with ⟨rfl, _⟩ | ⟨w, hw, hl, _⟩
      · exact absurd hlt (Nat.not_lt_zero _)
      · exact absurd hl (m.not_write_of_lastWrite_lt l hlt hw)

theorem atomic_of_forall (m : Memory) (l : Loc) (tid : Nat) (tr tw : Time)
    (h : ∀ (t : Nat) w, tr < t → t < tw → m.get? t = some w → w.loc = l → w.tid = tid) :
    m.atomic l tid tr tw = true := by
  unfold atomic
  split
  · rfl
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    split
    · next w hw =>
      by_cases hl : w.loc = l
      · simp [h _ _ (by omega_t) (by omega_t) hw hl]
      · simp [hl]
    · rfl

end Memory

/-! ## Views -/

theorem Loc.compare_eq_eq_iff {a b : Loc} : compare a b = .eq ↔ a = b := by
  show (compare a.addr.toNat b.addr.toNat).then (compare a.bytes b.bytes) = .eq ↔ _
  rw [Ordering.then_eq_eq, Nat.compare_eq_eq, Nat.compare_eq_eq]
  constructor
  · rintro ⟨h1, h2⟩
    cases a; cases b
    simp only at h1 h2
    rw [BitVec.eq_of_toNat_eq h1, h2]
  · rintro rfl; exact ⟨rfl, rfl⟩

namespace Views

theorem find?_setSorted {β} (xs : List (Loc × β)) (l l' : Loc) (b : β) :
    (setSorted xs l b).find? (·.1 == l') = if l' = l then some (l, b) else xs.find? (·.1 == l') := by
  induction xs with
  | nil =>
    by_cases h : l' = l
    · subst h; simp [setSorted]
    · simp [setSorted, h, Ne.symm h]
  | cons p rest ih =>
    obtain ⟨l₀, b₀⟩ := p
    simp only [setSorted]
    split
    · by_cases h : l' = l
      · subst h; simp
      · simp [h, Ne.symm h]
    · next hc =>
      have : l = l₀ := Loc.compare_eq_eq_iff.mp hc
      subst this
      by_cases h : l' = l
      · subst h; simp
      · simp [h, Ne.symm h]
    · next hc =>
      have hne : l ≠ l₀ := fun h => by
        subst h; rw [Loc.compare_eq_eq_iff.mpr rfl] at hc; cases hc
      by_cases h0 : l₀ = l'
      · subst h0; simp [Ne.symm hne]
      · simp [h0, ih]

theorem getCoh_setCoh (v : Views) (l l' : Loc) (t : View) :
    (v.setCoh l t).getCoh l' = if l' = l then max (v.getCoh l) t else v.getCoh l' := by
  simp only [getCoh, setCoh, find?_setSorted]
  split <;> simp

theorem getFwd_setFwd (v : Views) (l l' : Loc) (f : FwdItem) :
    (v.setFwd l f).getFwd l' = if l' = l then some f else v.getFwd l' := by
  simp only [getFwd, setFwd, find?_setSorted]
  split <;> simp

end Views

/-! ## The sequential invariant -/

/-- Every view component of `vs` is at most `n`. -/
structure Views.Le (vs : Views) (n : Nat) : Prop where
  coh : ∀ l, vs.getCoh l ≤ n
  vrNew : vs.vrNew ≤ n
  vrOld : vs.vrOld ≤ n
  vrOldNR : vs.vrOldNR ≤ n
  vwNew : vs.vwNew ≤ n
  vwOld : vs.vwOld ≤ n
  vCAP : vs.vCAP ≤ n
  vRel : vs.vRel ≤ n
  fwd : ∀ l f, vs.getFwd l = some f → f.view ≤ n
  vwOldNT : vs.vwOldNT ≤ n

/-- Every view of an instruction's dependencies is at most `n`. -/
structure InstrViews.Le (iv : InstrViews) (n : Nat) : Prop where
  addrR : iv.addrR ≤ n
  addrW : iv.addrW ≤ n
  dataR : iv.dataR ≤ n
  dataW : iv.dataW ≤ n
  condW : iv.condW ≤ n
  dataPer : ∀ p ∈ iv.dataPer, p.1 ≤ n ∧ p.2 ≤ n

theorem InstrViews.Le.mono {iv : InstrViews} {n n' : Nat} (h : iv.Le n) (hn : n ≤ n') : iv.Le n' :=
  ⟨Nat.le_trans h.addrR hn, Nat.le_trans h.addrW hn, Nat.le_trans h.dataR hn, Nat.le_trans h.dataW hn,
   Nat.le_trans h.condW hn,
   fun p hp => ⟨Nat.le_trans (h.dataPer p hp).1 hn, Nat.le_trans (h.dataPer p hp).2 hn⟩⟩

/-- A store's own views are bounded when the instruction's are. -/
theorem InstrViews.Le.forStore {iv : InstrViews} {n : Nat} (h : iv.Le n) (i : Nat) : (iv.forStore i).Le n := by
  unfold InstrViews.forStore
  split
  · next r w hi =>
    have hp := h.dataPer (r, w) (List.mem_of_getElem? hi)
    exact ⟨h.addrR, h.addrW, hp.1, hp.2, h.condW, h.dataPer⟩
  · exact h

/-- The pending load exclusive, if any, read from a timestamp in memory and
every later write to its location is by `tid` (so that a paired store
exclusive satisfies `atomic`). -/
def Views.XclbOk (vs : Views) (tid : Nat) (m : Memory) : Prop :=
  ∀ t ν l, vs.xclb = some (t, ν, l) →
    t ≤ m.last ∧ ∀ (t' : Nat) (w : Msg), t < t' → m.get? t' = some w → w.loc = l → w.tid = tid

/-- The views of a thread that has run alone, promise-free: every view is at
most `|M|`, the coherence view of each location is at or past its last
write, and the pending load exclusive is `XclbOk`. -/
structure Views.Seq (tid : Nat) (vs : Views) (m : Memory) : Prop where
  coh : ∀ l, m.lastWrite l ≤ vs.getCoh l
  le : vs.Le m.last
  xclb : vs.XclbOk tid m

/-- The invariant on a thread's context under which the promising rules are
sequential: no promises, `Views.Seq`, and the per-instruction views at most
`|M|`. -/
structure Ctx.Seq (tid : Nat) (c : Ctx) : Prop where
  prom : c.prom = []
  views : c.views.Seq tid c.mem
  loadViews : ∀ ν ∈ c.loadViews, ν ≤ c.mem.last
  succView : c.succView ≤ c.mem.last

/-! ## The rules under the invariant -/

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readView_le {k : LoadKind} {f : Option FwdItem} {t : Time} {n : Nat}
    (hf : ∀ f', f = some f' → f'.view ≤ n) (ht : t ≤ n) : readView A k f t ≤ n := by
  unfold readView
  split
  · split
    · split
      · exact Nat.max_le.mpr ⟨hf _ rfl, Nat.le_trans (Nat.min_le_right _ _) ht⟩
      · exact hf _ rfl
    · exact ht
  · exact ht

/-- `filterMap` over a range whose only hit is `a`. -/
private theorem filterMap_range_eq_singleton {β} {f : Nat → Option β} {n a : Nat} {b : β}
    (ha : a < n) (hfa : f a = some b) (hother : ∀ x, x < n → x ≠ a → f x = none) :
    (List.range n).filterMap f = [b] := by
  have key : ∀ xs : List Nat, xs.Nodup → a ∈ xs → (∀ x ∈ xs, x < n) → xs.filterMap f = [b] := by
    intro xs
    induction xs with
    | nil => intro _ h; cases h
    | cons x xs ih =>
      intro hnd hmem hlt
      rw [List.nodup_cons] at hnd
      by_cases hx : x = a
      · subst hx
        rw [List.filterMap_cons_some hfa, List.filterMap_eq_nil_iff.mpr]
        intro y hy
        exact hother y (hlt y (List.mem_cons_of_mem _ hy)) (fun h => hnd.1 (h ▸ hy))
      · rw [List.filterMap_cons_none (hother x (hlt x List.mem_cons_self) hx)]
        exact ih hnd.2 (by rcases List.mem_cons.mp hmem with h | h; exact absurd h.symm hx; exact h)
          (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
  exact key _ (List.nodup_range) (List.mem_range.mpr ha) (fun _ h => List.mem_range.mp h)

/-- The views after a read of `l` from its last write, with post-view
`νpost ≤ |M|`, are `Seq` again. The literal is the one `readSuccs` builds. -/
theorem Views.Seq.read {vs : Views} {m : Memory} (hs : vs.Seq tid m) {l : Loc} {νpost a : View}
    {acq xcl noRet : Bool} {t : Time} (hν : νpost ≤ m.last) (ha : a ≤ m.last) (ht : t = m.lastWrite l) :
    Views.Seq tid
      { (vs.setCoh l νpost) with
        vrOld := if noRet then vs.vrOld else max vs.vrOld νpost
        vrOldNR := if noRet then max vs.vrOldNR νpost else vs.vrOldNR
        vrNew := if acq then max vs.vrNew νpost else vs.vrNew
        vwNew := if acq then max vs.vwNew νpost else vs.vwNew
        vCAP := max vs.vCAP a
        xclb := if xcl then some (t, νpost, l) else vs.xclb } m := by
  have hle := hs.le
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro l'
    show m.lastWrite l' ≤ (vs.setCoh l νpost).getCoh l'
    rw [Views.getCoh_setCoh]
    split
    · next h => rw [h]; have := hs.coh l; omega_t
    · exact hs.coh l'
  · intro l'
    show (vs.setCoh l νpost).getCoh l' ≤ m.last
    rw [Views.getCoh_setCoh]
    split
    · have := hle.coh l; omega_t
    · exact hle.coh l'
  · show (if acq = true then max vs.vrNew νpost else vs.vrNew) ≤ m.last
    have := hle.vrNew; split <;> omega_t
  · show (if noRet = true then vs.vrOld else max vs.vrOld νpost) ≤ m.last
    have := hle.vrOld; split <;> omega_t
  · show (if noRet = true then max vs.vrOldNR νpost else vs.vrOldNR) ≤ m.last
    have := hle.vrOldNR; split <;> omega_t
  · show (if acq = true then max vs.vwNew νpost else vs.vwNew) ≤ m.last
    have := hle.vwNew; split <;> omega_t
  · exact hle.vwOld
  · show max vs.vCAP a ≤ m.last
    have := hle.vCAP; omega_t
  · exact hle.vRel
  · intro l' f hf; exact hle.fwd l' f hf
  · exact hle.vwOldNT
  · intro t' ν' l' h
    have h' : (if xcl = true then some (t, νpost, l) else vs.xclb) = some (t', ν', l') := h
    split at h'
    · simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl⟩ := h'
      subst ht
      refine ⟨m.lastWrite_le l, fun t' w hlt hw hl => ?_⟩
      exact absurd hl (m.not_write_of_lastWrite_lt l hlt hw)
    · exact hs.xclb t' ν' l' h'

/-- The `read` rule from a `Seq` context reads the last write and returns the
final value; the context after it is `Seq` with the same memory. -/
theorem readSuccs_eq {c : Ctx} (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool)
    (hc : c.Seq tid) (hiv : iv.Le c.mem.last) :
    ∃ c', readSuccs A iv c k xcl l noRet = [(c.mem.lastWrite l, c.mem.finalVal l, c')] ∧
      c'.mem = c.mem ∧ c'.Seq tid := by
  have hcoh := hc.views.coh l
  have hcohle := hc.views.le.coh l
  have hlw := c.mem.lastWrite_le l
  have hnc : c.prom.contains (c.mem.lastWrite l) = false := by rw [hc.prom]; rfl
  simp only [readSuccs]
  refine ⟨_, filterMap_range_eq_singleton (a := c.mem.lastWrite l) (by omega_t)
    (by simp only [Memory.read?_lastWrite, Memory.writeIn_lastWrite, hnc,
          Bool.or_self, Bool.false_eq_true, ite_false]; rfl)
    ?_, ?_, ?_⟩
  · intro t ht hne
    rcases c.mem.read?_eq_none_or_writeIn l (bound := max (max iv.addrR (max c.views.vrNew (if A.loadKind k == .acq then c.views.vRel else 0))) (c.views.getCoh l)) (by omega_t) hne (by omega_t) with h | h
    · simp only [h]
    · simp only [h, Bool.true_or, ite_true]
      split <;> rfl
  · rfl
  · have hif : (if (A.loadKind k == LoadKind.acq) = true then c.views.vRel else 0) ≤ c.mem.last := by
      split
      · exact hc.views.le.vRel
      · exact Nat.zero_le _
    have hrv := readView_le A (k := A.loadKind k) (f := c.views.getFwd l) (hc.views.le.fwd l) hlw
    have haddrR := hiv.addrR
    have hvrNew := hc.views.le.vrNew
    refine ⟨hc.prom, Views.Seq.read tid hc.views (by omega_t) hiv.addrW rfl, ?_, hc.succView⟩
    intro ν hν
    rcases List.mem_append.mp hν with h | h
    · exact hc.loadViews ν h
    · rw [List.mem_singleton] at h; subst h; omega_t

/-- The context after "promise now" of `l := v` from a `Seq` context is `Seq`.
The context argument is the one `writeSuccs` builds: the memory appended,
the fresh timestamp promised. -/
theorem Ctx.Seq.write {c : Ctx} {m : Memory} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {νfwd : View} {fulfilled : Bool} {xr : View}
    (hprom : c.prom = [m.last + 1]) (hmem : c.mem = (m.append { loc := l, val := v, tid }).1)
    (hv : c.views.Seq tid m) (hload : ∀ ν ∈ c.loadViews, ν ≤ m.last) (hνfwd : νfwd ≤ m.last)
    (hiv : iv.Le m.last) :
    (afterWrite A iv c k xcl l v (m.last + 1) νfwd fulfilled xr).Seq tid := by
  have hle := hv.le
  have hlast : (m.append { loc := l, val := v, tid }).1.last = m.last + 1 := Memory.last_append _ _
  unfold afterWrite
  refine ⟨?_, ?_, ?_, ?_⟩
  · show c.prom.erase (m.last + 1) = []
    rw [hprom]; simp
  · show Views.Seq tid _ c.mem
    rw [hmem]
    refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro l'
      show (m.append _).1.lastWrite l' ≤ (c.views.setCoh l (m.last + 1)).getCoh l'
      rw [Memory.lastWrite_append, Views.getCoh_setCoh]
      simp only
      by_cases h : l' = l
      · rw [h]; simp only [ite_true]; omega_t
      · rw [ite_eq_right (Ne.symm h), ite_eq_right h]; exact hv.coh l'
    · intro l'
      show (c.views.setCoh l (m.last + 1)).getCoh l' ≤ _
      rw [hlast, Views.getCoh_setCoh]
      have := hle.coh l; have := hle.coh l'
      split <;> omega_t
    · show c.views.vrNew ≤ _
      rw [hlast]; have := hle.vrNew; omega_t
    · show c.views.vrOld ≤ _
      rw [hlast]; have := hle.vrOld; omega_t
    · show c.views.vrOldNR ≤ _
      rw [hlast]; have := hle.vrOldNR; omega_t
    · show c.views.vwNew ≤ _
      rw [hlast]; have := hle.vwNew; omega_t
    · show (if (k == StoreKind.nt) = true then c.views.vwOld else max c.views.vwOld (m.last + 1)) ≤ _
      rw [hlast]; have := hle.vwOld; split <;> omega_t
    · show max c.views.vCAP iv.addrW ≤ _
      rw [hlast]; have := hle.vCAP; have := hiv.addrW; omega_t
    · show (if (k == StoreKind.rel) = true then max c.views.vRel (m.last + 1) else c.views.vRel) ≤ _
      rw [hlast]; have := hle.vRel; split <;> omega_t
    · intro l' f hf
      have hf' : (c.views.setFwd l { time := m.last + 1, view := νfwd, xcl, xclRead := xr }).getFwd l' = some f := hf
      rw [hlast, Views.getFwd_setFwd] at *
      split at hf'
      · cases hf'; show νfwd ≤ m.last + 1; omega_t
      · have := hle.fwd l' f hf'; omega_t
    · show (if (k == StoreKind.nt) = true then max c.views.vwOldNT (m.last + 1) else c.views.vwOldNT) ≤ _
      rw [hlast]; have := hle.vwOldNT; split <;> omega_t
    · intro t0 ν l0 h
      have h' : (if xcl = true then none else c.views.xclb) = some (t0, ν, l0) := h
      split at h'
      · cases h'
      · obtain ⟨h1, h2⟩ := hv.xclb t0 ν l0 h'
        refine ⟨by rw [hlast]; omega_t, fun t' w hlt hw hl => ?_⟩
        rcases m.get?_append_eq_some _ hw with ⟨_, hw'⟩ | ⟨_, rfl⟩
        · exact h2 t' w hlt hw' hl
        · rfl
  · intro ν hν
    show ν ≤ c.mem.last
    rw [hmem, hlast]; have := hload ν hν; omega_t
  · show (if A.succViewBot then 0 else m.last + 1) ≤ c.mem.last
    rw [hmem, hlast]; split <;> omega_t

/-- The `fulfil` rule from a `Seq` context, whose only option is "promise
now": appends the write and yields a `Seq` context, provided the exclusive
pairing timestamp `tr`, if any, is in memory and every later write to `l` is
by `tid`. -/
theorem writeSuccs_eq {c : Ctx} (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (tr : Option Time)
    (extra : View) {xr : View} (hc : c.Seq tid) (hiv : iv.Le c.mem.last) (hextra : extra ≤ c.mem.last)
    (htr : ∀ t0, tr = some t0 → t0 ≤ c.mem.last ∧
      ∀ (t' : Nat) (w : Msg), t0 < t' → c.mem.get? t' = some w → w.loc = l → w.tid = tid) :
    ∃ c', writeSuccs A tid iv c k xcl l v tr extra xr = [c'] ∧
      c'.mem = (c.mem.append { loc := l, val := v, tid }).1 ∧ c'.Seq tid := by
  have hbound : max (max (max iv.addrW (max iv.dataW (max iv.condW extra)))
      (max (max c.views.vwNew c.views.vCAP)
        (if (A.storeKind k == StoreKind.rel) = true then max (max c.views.vrOld c.views.vrOldNR) c.views.vwOld
          else if (A.storeKind k == StoreKind.nt) = true then max c.views.vrOld c.views.vrOldNR else 0)))
      (c.views.getCoh l) < (c.mem.append { loc := l, val := v, tid }).2 := by
    rw [Memory.append_time]
    have h1 := hiv.addrW; have h2 := hiv.dataW; have h3 := hiv.condW
    have h4 := hc.views.le.vwNew; have h5 := hc.views.le.vCAP; have h6 := hc.views.le.coh l
    have h7 : (if (A.storeKind k == StoreKind.rel) = true then max (max c.views.vrOld c.views.vrOldNR) c.views.vwOld
          else if (A.storeKind k == StoreKind.nt) = true then max c.views.vrOld c.views.vrOldNR else 0) ≤
        c.mem.last := by
      have := hc.views.le.vrOld; have := hc.views.le.vrOldNR; have := hc.views.le.vwOld
      split
      · omega_t
      · split
        · omega_t
        · exact Nat.zero_le _
    omega_t
  have hok : ∀ t0, tr = some t0 → (decide (t0 < (c.mem.append { loc := l, val := v, tid }).2) &&
      c.mem.atomic l tid t0 (c.mem.append { loc := l, val := v, tid }).2) = true := by
    intro t0 h
    obtain ⟨h1, h2⟩ := htr t0 h
    rw [Memory.append_time, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega_t, c.mem.atomic_of_forall l tid t0 _ fun t w ha hb hw hl => h2 t w ha hw hl⟩
  cases tr with
  | none =>
    simp only [writeSuccs, hc.prom, List.filterMap_nil, List.nil_append, Bool.and_true]
    rw [ite_eq_left (decide_eq_true hbound)]
    refine ⟨_, rfl, rfl, ?_⟩
    exact Ctx.Seq.write A tid iv rfl rfl hc.views hc.loadViews (by have := hiv.addrR; have := hiv.dataR; omega_t) hiv
  | some t0 =>
    simp only [writeSuccs, hc.prom, List.filterMap_nil, List.nil_append]
    rw [ite_eq_left (by rw [Bool.and_eq_true]; exact ⟨decide_eq_true hbound, hok t0 rfl⟩)]
    refine ⟨_, rfl, rfl, ?_⟩
    exact Ctx.Seq.write A tid iv rfl rfl hc.views hc.loadViews (by have := hiv.addrR; have := hiv.dataR; omega_t) hiv

/-- Reads are deterministic: the only timestamp read is the last write. -/
theorem readSuccs_map_fst {c : Ctx} (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (hc : c.Seq tid)
    (hiv : iv.Le c.mem.last) : (readSuccs A iv c k xcl l noRet).map (·.1) = [c.mem.lastWrite l] := by
  obtain ⟨c', h, _, _⟩ := readSuccs_eq A tid iv k xcl l noRet hc hiv
  rw [h]; rfl

/-- The value read is the final value of the location. -/
theorem readSuccs_map_val {c : Ctx} (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (hc : c.Seq tid)
    (hiv : iv.Le c.mem.last) : (readSuccs A iv c k xcl l noRet).map (·.2.1) = [c.mem.finalVal l] := by
  obtain ⟨c', h, _, _⟩ := readSuccs_eq A tid iv k xcl l noRet hc hiv
  rw [h]; rfl

/-- Writes append: every successor of a plain store has the message appended
and is `Seq`, and there is one. -/
theorem writeSuccs_plain {c : Ctx} (k : StoreKind) (l : Loc) (v : Val) (hc : c.Seq tid)
    (hiv : iv.Le c.mem.last) :
    writeSuccs A tid iv c k false l v none ≠ [] ∧
    ∀ c' ∈ writeSuccs A tid iv c k false l v none,
      c'.mem = (c.mem.append { loc := l, val := v, tid }).1 ∧ c'.Seq tid := by
  obtain ⟨c', h, hm, hs⟩ := writeSuccs_eq A tid iv k false l v none 0 hc hiv (Nat.zero_le _) (fun _ h => by cases h)
  rw [h]
  refine ⟨List.cons_ne_nil _ _, fun c'' hc'' => ?_⟩
  rw [List.mem_singleton] at hc''
  subst hc''
  exact ⟨hm, hs⟩

/-! ### Small view updates -/

theorem Views.Le.xclb {vs : Views} {n : Nat} (h : vs.Le n) (x : Option (Time × View × Loc)) :
    ({ vs with xclb := x } : Views).Le n :=
  ⟨h.coh, h.vrNew, h.vrOld, h.vrOldNR, h.vwNew, h.vwOld, h.vCAP, h.vRel, h.fwd, h.vwOldNT⟩

/-- Dropping the pending load exclusive. -/
theorem Views.Seq.xclbNone {vs : Views} {m : Memory} (hs : vs.Seq tid m) :
    ({ vs with xclb := none } : Views).Seq tid m :=
  ⟨hs.coh, hs.le.xclb none, fun _ _ _ h => by cases h⟩

/-- Raising `vrNew`/`vwNew` to anything at most `|M|`. -/
theorem Views.Seq.setNew {vs : Views} {m : Memory} (hs : vs.Seq tid m) {r w : View} (hr : r ≤ m.last)
    (hw : w ≤ m.last) : ({ vs with vrNew := r, vwNew := w } : Views).Seq tid m :=
  ⟨hs.coh, ⟨hs.le.coh, hr, hs.le.vrOld, hs.le.vrOldNR, hw, hs.le.vwOld, hs.le.vCAP, hs.le.vRel, hs.le.fwd, hs.le.vwOldNT⟩, hs.xclb⟩

theorem fenceStep_mem (c : Ctx) (k : FenceKind) : (fenceStep c k).mem = c.mem := by
  cases k <;> rfl

/-- The `fence` rule preserves `Seq`. -/
theorem fenceStep_seq {c : Ctx} (k : FenceKind) (hc : c.Seq tid) : (fenceStep c k).Seq tid := by
  have hle := hc.views.le
  have h1 := hle.vrNew; have h2 := hle.vwNew; have h3 := hle.vrOld; have h4 := hle.vwOld; have h5 := hle.vCAP
  have h6 := hle.vrOldNR; have h7 := hle.vwOldNT
  cases k
  all_goals
    simp only [fenceStep]
    exact ⟨hc.prom, Views.Seq.setNew tid hc.views (by omega_t) (by omega_t), hc.loadViews, hc.succView⟩

/-- The context on the failing branch of a store exclusive is `Seq`. -/
theorem Ctx.Seq.xclFail {c : Ctx} (hc : c.Seq tid) (l : Loc) :
    ({ c with views := { c.views with xclb := none }, succView := 0,
              log := c.log ++ [.xclFail l] } : Ctx).Seq tid :=
  ⟨hc.prom, hc.views.xclbNone, hc.loadViews, Nat.zero_le _⟩

theorem Ctx.Seq.rmwWrote {c : Ctx} (hc : c.Seq tid) : ({ c with rmwWrote := true } : Ctx).Seq tid :=
  ⟨hc.prom, hc.views, hc.loadViews, hc.succView⟩

/-- The optional `fence .sy` around an RMW under `rmwFence`. -/
theorem Ctx.Seq.fenceOpt {c : Ctx} (hc : c.Seq tid) (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).Seq tid ∧ (if b then fenceStep c k else c).mem = c.mem := by
  cases b
  · exact ⟨hc, rfl⟩
  · exact ⟨fenceStep_seq tid k hc, fenceStep_mem c k⟩

/-- The context after an RMW's write: `rmwWrote` set, the acquire-release
ordering folded into `vrNew`/`vwNew` under `b2`, the optional fence under
`b1`. The literals are the ones `runTree` builds. -/
theorem Ctx.Seq.rmwTail {c : Ctx} (hc : c.Seq tid) (l : Loc) (b1 b2 : Bool) :
    let c4 : Ctx := if b2 then
        { c with views := { c.views with vrNew := max c.views.vrNew (c.views.getCoh l),
                                          vwNew := max c.views.vwNew (c.views.getCoh l) },
                 rmwWrote := true }
      else { c with rmwWrote := true }
    let c5 := if b1 then fenceStep c4 .sy else c4
    c5.Seq tid ∧ c5.mem = c.mem := by
  intro c4 c5
  have h4 : c4.Seq tid ∧ c4.mem = c.mem := by
    have h1 := hc.views.le.vrNew; have h2 := hc.views.le.vwNew; have h3 := hc.views.le.coh l
    cases b2
    · exact ⟨Ctx.Seq.rmwWrote tid hc, rfl⟩
    · exact ⟨⟨hc.prom, Views.Seq.setNew tid hc.views (by omega_t) (by omega_t), hc.loadViews, hc.succView⟩, rfl⟩
  cases b1
  · exact h4
  · exact ⟨fenceStep_seq tid .sy h4.1, (fenceStep_mem c4 .sy).trans h4.2⟩

private theorem getLastD_le {xs : List Nat} {n : Nat} (h : ∀ x ∈ xs, x ≤ n) : xs.getLastD 0 ≤ n := by
  rw [List.getLastD_eq_getLast?]
  match hx : xs.getLast? with
  | none => exact Nat.zero_le _
  | some a => exact h a (List.mem_of_getLast? hx)

/-! ## Soundness: promising runs are sequential runs -/

/-- From a `Seq` context, every successful promising run of a tree is a run of
the sequential interpreter, and ends in a `Seq` context. -/
theorem runTree_sound {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx), c.Seq tid → iv.Le c.mem.last →
      ∀ (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
        (s, c'.mem) ∈ seqRun tid c.mem tree ∧ c'.Seq tid := by
  induction tree with
  | done s0 =>
    intro c hc _ s c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨List.mem_singleton.mpr rfl, hc⟩
  | fault msg =>
    intro c _ _ s c' h
    simp [runTree] at h
  | choose n k ih =>
    intro c hc hiv s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    obtain ⟨h1, h2⟩ := ih i c hc hiv s c' hi
    exact ⟨by simp only [seqRun, List.mem_flatMap]; exact ⟨i, List.mem_finRange i, h1⟩, h2⟩
  | load k xcl l ret ih =>
    intro c hc hiv s c' h
    obtain ⟨c0, hread, hm0, hs0⟩ := readSuccs_eq A tid iv k xcl l false hc hiv
    simp only [runTree, hread, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
    have := ih _ c0 hs0 (hm0 ▸ hiv) s c' h
    rw [hm0] at this
    exact this
  | store k xcl l v ret ih =>
    intro c hc hiv s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨hnp, c0, hc0, h⟩ := h
      have htr : ∀ t0, (if xcl then c.views.xclb.map (·.1) else none) = some t0 → t0 ≤ c.mem.last ∧
          ∀ (t' : Nat) (w : Msg), t0 < t' → c.mem.get? t' = some w → w.loc = l → w.tid = tid := by
        intro t0 ht0
        cases xcl with
        | false => simp at ht0
        | true =>
          simp only [ite_true, Option.map_eq_some_iff] at ht0
          obtain ⟨⟨t1, ν1, l1⟩, hx, rfl⟩ := ht0
          rw [hx] at hnp
          simp at hnp
          rw [hnp] at hx
          exact hc.views.xclb t1 ν1 l hx
      obtain ⟨c0', hw, hm0, hs0⟩ := writeSuccs_eq A tid _ k xcl l v _ 0
        (xr := if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0) hc (hiv.forStore c.stores)
        (Nat.zero_le _) htr
      rw [hw, List.mem_singleton] at hc0
      subst hc0
      have hlast : c.mem.last ≤ c0.mem.last := by rw [hm0, Memory.last_append]; omega_t
      have := ih true c0 hs0 (hiv.mono hlast) s c' h
      refine ⟨?_, this.2⟩
      simp only [seqRun, List.mem_append]
      left; rw [← hm0]; exact this.1
    · rw [List.mem_ite_nil_right] at h
      obtain ⟨hx, h⟩ := h
      have := ih false _ (Ctx.Seq.xclFail tid hc l) hiv s c' h
      refine ⟨?_, this.2⟩
      simp only [seqRun, List.mem_append, hx, ite_true]
      exact .inr this.1
  | fence k ret ih =>
    intro c hc hiv s c' h
    simp only [runTree] at h
    have := ih () _ (fenceStep_seq tid k hc) (by rw [fenceStep_mem]; exact hiv) s c' h
    rw [fenceStep_mem] at this
    exact this
  | rmw k noRet l op ret ih =>
    intro c hc hiv s c' h
    simp only [runTree] at h
    obtain ⟨hc1seq, hc1mem⟩ := Ctx.Seq.fenceOpt tid hc A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h hc1seq hc1mem
    obtain ⟨c2, hread, hm2, hs2⟩ :=
      readSuccs_eq A tid iv (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet hc1seq (hc1mem ▸ hiv)
    rw [hread] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h
    rw [hc1mem] at h hm2 hread
    cases hop : op (c.mem.finalVal l) with
    | none =>
      simp only [hop] at h
      simp only [seqRun, hop]
      obtain ⟨hc3, hm3⟩ := Ctx.Seq.fenceOpt tid hs2 A.rmwFence .sy
      have := ih _ _ hc3 (by rw [hm3, hm2]; exact hiv) s c' h
      rw [hm3, hm2] at this
      exact this
    | some new =>
      simp only [hop, List.mem_flatMap] at h
      simp only [seqRun, hop]
      obtain ⟨c3, hc3, h⟩ := h
      have hextra : c2.loadViews.getLastD 0 ≤ c2.mem.last := getLastD_le hs2.loadViews
      have htr : ∀ t0, some (c.mem.lastWrite l) = some t0 → t0 ≤ c2.mem.last ∧
          ∀ (t' : Nat) (w : Msg), t0 < t' → c2.mem.get? t' = some w → w.loc = l → w.tid = tid := by
        intro t0 ht0
        cases ht0
        rw [hm2]
        exact ⟨c.mem.lastWrite_le l, fun t' w hlt hw hl => absurd hl (c.mem.not_write_of_lastWrite_lt l hlt hw)⟩
      obtain ⟨c3', hw, hm3, hs3⟩ :=
        writeSuccs_eq A tid iv (A.rmwKind k).storeKind true l new _ _ hs2 (hm2 ▸ hiv) hextra htr
      rw [hw, List.mem_singleton] at hc3
      subst hc3
      obtain ⟨hc5, hm5⟩ := Ctx.Seq.rmwTail tid hs3 l A.rmwFence (A.rmwKind k == .acqRel && !noRet)
      have hlast : c.mem.last ≤ c3.mem.last := by rw [hm3, hm2, Memory.last_append]; omega_t
      have := ih _ _ hc5 (by rw [hm5]; exact hiv.mono hlast) s c' h
      rw [hm5, hm3, hm2] at this
      exact this

/-! ## Completeness on the exclusive-free fragment -/

/-- Without store exclusives and RMWs, every sequential run of a tree from a
`Seq` context is a promising run. -/
theorem runTree_complete {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx), tree.NoExcl → c.Seq tid → iv.Le c.mem.last →
      ∀ (s : σ) (m : Memory), (s, m) ∈ seqRun tid c.mem tree →
        ∃ c', .ok (s, c') ∈ runTree A tid iv c tree ∧ c'.mem = m ∧ c'.Seq tid := by
  induction tree with
  | done s0 =>
    intro c _ hc _ s m h
    simp only [seqRun, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨c, by simp [runTree], rfl, hc⟩
  | fault msg =>
    intro c _ _ _ s m h
    simp [seqRun] at h
  | choose n k ih =>
    intro c hne hc hiv s m h
    simp only [seqRun, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    obtain ⟨c', h1, h2, h3⟩ := ih i c (hne i) hc hiv s m hi
    exact ⟨c', by simp only [runTree, List.mem_flatMap]; exact ⟨i, List.mem_finRange i, h1⟩, h2, h3⟩
  | load k xcl l ret ih =>
    intro c hne hc hiv s m h
    obtain ⟨c0, hread, hm0, hs0⟩ := readSuccs_eq A tid iv k xcl l false hc hiv
    simp only [seqRun] at h
    rw [← hm0] at h
    obtain ⟨c', h1, h2, h3⟩ := ih _ c0 (hne _) hs0 (hm0 ▸ hiv) s m h
    refine ⟨c', ?_, h2, h3⟩
    simp only [runTree, hread, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← hm0]
    exact h1
  | store k xcl l v ret ih =>
    intro c hne hc hiv s m h
    obtain ⟨rfl, hne⟩ := hne
    simp only [seqRun, Bool.false_eq_true, ite_false, List.append_nil] at h
    obtain ⟨c0, hw, hm0, hs0⟩ := writeSuccs_eq A tid _ k false l v none 0 hc (hiv.forStore c.stores)
      (Nat.zero_le _) (fun _ h => by cases h)
    rw [← hm0] at h
    have hlast : c.mem.last ≤ c0.mem.last := by rw [hm0, Memory.last_append]; omega_t
    obtain ⟨c', h1, h2, h3⟩ := ih true c0 (hne true) hs0 (hiv.mono hlast) s m h
    refine ⟨c', ?_, h2, h3⟩
    simp only [runTree, Bool.false_and, Bool.false_eq_true, ite_false, List.append_nil]
    rw [hw]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact h1
  | rmw k noRet l op ret _ =>
    intro c hne
    exact absurd hne id
  | fence k ret ih =>
    intro c hne hc hiv s m h
    simp only [seqRun] at h
    rw [← fenceStep_mem c k] at h
    obtain ⟨c', h1, h2, h3⟩ := ih () _ hne (fenceStep_seq tid k hc) (by rw [fenceStep_mem]; exact hiv) s m h
    exact ⟨c', by simp only [runTree]; exact h1, h2, h3⟩

end Rules

/-! ## Memory grows along a sequential run -/

theorem seqRun_last_le {σ : Type} (tid : Nat) (tree : EvTree σ) :
    ∀ (m : Memory) (s : σ) (m' : Memory), (s, m') ∈ seqRun tid m tree → m.last ≤ m'.last := by
  induction tree with
  | done s0 =>
    intro m s m' h
    simp only [seqRun, List.mem_singleton, Prod.mk.injEq] at h
    rw [h.2]; exact Nat.le_refl _
  | fault _ => intro m s m' h; simp [seqRun] at h
  | choose n k ih =>
    intro m s m' h
    simp only [seqRun, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i m s m' hi
  | load k xcl l ret ih =>
    intro m s m' h
    exact ih _ m s m' h
  | store k xcl l v ret ih =>
    intro m s m' h
    simp only [seqRun, List.mem_append] at h
    rcases h with h | h
    · have := ih true _ s m' h
      rw [Memory.last_append] at this; omega_t
    · split at h
      · exact ih false m s m' h
      · simp at h
  | rmw k noRet l op ret ih =>
    intro m s m' h
    simp only [seqRun] at h
    split at h
    · have := ih _ _ s m' h
      rw [Memory.last_append] at this; omega_t
    · exact ih _ m s m' h
  | fence k ret ih =>
    intro m s m' h
    exact ih () m s m' h

/-! ## One instruction of a thread -/

section Machine

variable {I : ISA}

/-- A thread that has run alone, promise-free: no promises, `Views.Seq`, and
every register view at most `|M|`. -/
structure Thread.Seq (tid : Nat) (t : Thread I) (m : Memory) : Prop where
  prom : t.prom = []
  views : t.views.Seq tid m
  rview : ∀ v ∈ t.rview, v ≤ m.last
  wview : ∀ v ∈ t.wview, v ≤ m.last

/-- Register views bounded by `n`. -/
def Thread.RegsLe (t : Thread I) (n : Nat) : Prop :=
  (∀ v ∈ t.rview, v ≤ n) ∧ (∀ v ∈ t.wview, v ≤ n)

private theorem getElem!_le {a : Array Nat} {n i : Nat} (h : ∀ v ∈ a, v ≤ n) : a[i]! ≤ n := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  match hi : a[i]? with
  | none => exact Nat.zero_le _
  | some v => exact h v (Array.mem_iff_getElem?.mpr ⟨i, hi⟩)

theorem Thread.rviewOf_le {t : Thread I} {n : Nat} (h : t.RegsLe n) (r : I.RegId) : t.rviewOf r ≤ n :=
  getElem!_le h.1

theorem Thread.wviewOf_le {t : Thread I} {n : Nat} (h : t.RegsLe n) (r : I.RegId) : t.wviewOf r ≤ n :=
  getElem!_le h.2

theorem Thread.joinViews_le {t : Thread I} {n : Nat} (h : t.RegsLe n) (rs : List I.RegId) :
    (t.joinViews rs).1 ≤ n ∧ (t.joinViews rs).2 ≤ n := by
  unfold Thread.joinViews
  suffices ∀ (acc : View × View), acc.1 ≤ n → acc.2 ≤ n →
      (rs.foldl (fun (r, w) x => (max r (t.rviewOf x), max w (t.wviewOf x))) acc).1 ≤ n ∧
      (rs.foldl (fun (r, w) x => (max r (t.rviewOf x), max w (t.wviewOf x))) acc).2 ≤ n from
    this (0, 0) (Nat.zero_le _) (Nat.zero_le _)
  induction rs with
  | nil => intro acc h1 h2; exact ⟨h1, h2⟩
  | cons x xs ih =>
    intro acc h1 h2
    rw [List.foldl_cons]
    have := t.rviewOf_le h x; have := t.wviewOf_le h x
    exact ih (max acc.1 (t.rviewOf x), max acc.2 (t.wviewOf x)) (by simp only; omega_t) (by simp only; omega_t)

theorem instrViews_le {t : Thread I} {n : Nat} (h : t.RegsLe n) (d : InstrDeps I.RegId) :
    (instrViews t d).Le n :=
  have hd : (if d.dataRegsPer.isEmpty then t.joinViews d.dataRegs else (0, 0)).1 ≤ n ∧
      (if d.dataRegsPer.isEmpty then t.joinViews d.dataRegs else (0, 0)).2 ≤ n := by
    split
    · exact t.joinViews_le h d.dataRegs
    · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  ⟨(t.joinViews_le h d.addrRegs).1, (t.joinViews_le h d.addrRegs).2,
   hd.1, hd.2, (t.joinViews_le h d.condRegs).2,
   fun p hp => by
     obtain ⟨rs, _, rfl⟩ := List.mem_map.mp hp
     exact t.joinViews_le h rs⟩

private theorem forall_mem_setIfInBounds {a : Array Nat} {n i x : Nat} (h : ∀ v ∈ a, v ≤ n) (hx : x ≤ n) :
    ∀ v ∈ a.setIfInBounds i x, v ≤ n := by
  intro v hv
  rw [Array.mem_iff_getElem] at hv
  obtain ⟨j, hj, rfl⟩ := hv
  rw [Array.size_setIfInBounds] at hj
  rw [Array.getElem_setIfInBounds hj]
  split
  · exact hx
  · exact h _ (Array.getElem_mem hj)

theorem Thread.RegsLe.setRegView {t : Thread I} {n : Nat} (h : t.RegsLe n) (r : I.RegId) {rv wv : View}
    (hr : rv ≤ n) (hw : wv ≤ n) : (t.setRegView r rv wv).RegsLe n :=
  ⟨forall_mem_setIfInBounds h.1 hr, forall_mem_setIfInBounds h.2 hw⟩

theorem Thread.RegsLe.mono {t : Thread I} {n n' : Nat} (h : t.RegsLe n) (hn : n ≤ n') : t.RegsLe n' :=
  ⟨fun v hv => Nat.le_trans (h.1 v hv) hn, fun v hv => Nat.le_trans (h.2 v hv) hn⟩

/-- `setRegView` only touches the register views. -/
theorem Thread.setRegView_st (t : Thread I) (r : I.RegId) (rv wv : View) : (t.setRegView r rv wv).st = t.st := rfl
theorem Thread.setRegView_views (t : Thread I) (r : I.RegId) (rv wv : View) :
    (t.setRegView r rv wv).views = t.views := rfl
theorem Thread.setRegView_prom (t : Thread I) (r : I.RegId) (rv wv : View) :
    (t.setRegView r rv wv).prom = t.prom := rfl

private theorem foldl_invariant {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (xs : List α) (b : β), P b → (∀ b x, x ∈ xs → P b → P (f b x)) → P (xs.foldl f b)
  | [], _, hb, _ => hb
  | x :: xs, b, hb, hf =>
    foldl_invariant P f xs (f b x) (hf b x List.mem_cons_self hb)
      (fun b' x' hx' => hf b' x' (List.mem_cons_of_mem _ hx'))

/-- What a fold of `setRegView`s preserves: `st`, `views`, `prom`, and the
register bound when every value written is bounded. -/
private def SetRegInv (t0 : Thread I) (n : Nat) (t : Thread I) : Prop :=
  t.st = t0.st ∧ t.views = t0.views ∧ t.prom = t0.prom ∧ t.RegsLe n

private theorem SetRegInv.step {t0 : Thread I} {n : Nat} {t : Thread I} (h : SetRegInv t0 n t) (r : I.RegId)
    {rv wv : View} (hr : rv ≤ n) (hw : wv ≤ n) : SetRegInv t0 n (t.setRegView r rv wv) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.setRegView r hr hw⟩

/-- The threads `finishInstr` returns keep the ISA state the tree ended in and
are `Seq` for the context's memory. -/
theorem finishInstr_seq {tid : Nat} {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State}
    {c : Ctx} (hc : c.Seq tid) (hiv : iv.Le c.mem.last) (hregs : t.RegsLe c.mem.last) :
    ∀ th ∈ finishInstr t d iv st c, th.st = st ∧ th.Seq tid c.mem := by
  intro th hth
  have hload : c.loadViews.foldl max 0 ≤ c.mem.last := by
    have hlv := hc.loadViews
    suffices ∀ (xs : List View) (acc : View), (∀ ν ∈ xs, ν ≤ c.mem.last) → acc ≤ c.mem.last →
        xs.foldl max acc ≤ c.mem.last from this _ 0 hlv (Nat.zero_le _)
    intro xs
    induction xs with
    | nil => intro acc _ h; exact h
    | cons x xs ih =>
      intro acc hxs hacc
      rw [List.foldl_cons]
      have := hxs x List.mem_cons_self
      exact ih _ (fun ν hν => hxs ν (List.mem_cons_of_mem _ hν)) (by omega_t)
  -- the thread before the destination updates
  let t1 : Thread I := { t with st, views := c.views, prom := c.prom }
  have h1 : SetRegInv t1 c.mem.last t1 := ⟨rfl, rfl, rfl, hregs⟩
  have hinR : max iv.addrR iv.dataR ≤ c.mem.last := by have := hiv.addrR; have := hiv.dataR; omega_t
  have hinW : max (max iv.addrW iv.dataW) iv.condW ≤ c.mem.last := by
    have := hiv.addrW; have := hiv.dataW; have := hiv.condW; omega_t
  have hinR' : (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW) ≤ c.mem.last := by
    have := hiv.condW; split <;> omega_t
  -- after `defs` and `statusDefs`
  have h2 : SetRegInv t1 c.mem.last
      ((d.statusDefs.foldl (fun t r => t.setRegView r c.succView c.succView)
        (d.defs.foldl (fun t r => t.setRegView r
          (if d.isPick then max iv.addrR iv.dataR else max (max iv.addrR iv.dataR) iv.condW)
          (max (max iv.addrW iv.dataW) iv.condW)) t1))) := by
    apply foldl_invariant (SetRegInv t1 c.mem.last)
    · apply foldl_invariant (SetRegInv t1 c.mem.last) _ _ _ h1
      intro b x _ hb
      exact hb.step x hinR' hinW
    · intro b x _ hb
      exact hb.step x hc.succView hc.succView
  -- the conclusion from the invariant, for the thread after `branch`
  have finish : ∀ t2 : Thread I, SetRegInv t1 c.mem.last t2 →
      ∀ th, th = (if d.isBranch then { t2 with views := { t2.views with vCAP := max t2.views.vCAP iv.condW } } else t2) →
      th.st = st ∧ th.Seq tid c.mem := by
    intro t2 ⟨hst, hviews, hprom, hregs⟩ th hth
    have hvs : t2.views.Seq tid c.mem := hviews ▸ hc.views
    have hprom' : t2.prom = [] := hprom.trans hc.prom
    subst hth
    split
    · refine ⟨hst, hprom', ?_, hregs.1, hregs.2⟩
      have hle := hvs.le
      have := hiv.condW; have := hle.vCAP
      exact ⟨hvs.coh, ⟨hle.coh, hle.vrNew, hle.vrOld, hle.vrOldNR, hle.vwNew, hle.vwOld, by show max _ _ ≤ _; omega_t,
        hle.vRel, hle.fwd, hle.vwOldNT⟩, hvs.xclb⟩
    · exact ⟨hst, hprom', hvs, hregs.1, hregs.2⟩
  -- `fromLoads`
  have h3 : ∀ t2 : Thread I, SetRegInv t1 c.mem.last t2 → SetRegInv t1 c.mem.last
      (if d.loadDefs.length == c.loadViews.length then
        (d.loadDefs.zip c.loadViews).foldl (fun t (r, v) => t.setRegView r v v) t2
      else d.loadDefs.foldl (fun t r => t.setRegView r (c.loadViews.foldl max 0) (c.loadViews.foldl max 0)) t2) := by
    intro t2 h2
    split
    · apply foldl_invariant (SetRegInv t1 c.mem.last) _ _ _ h2
      intro b x hx hb
      obtain ⟨r, v⟩ := x
      have hv : v ≤ c.mem.last := hc.loadViews v (List.of_mem_zip hx).2
      exact hb.step r hv hv
    · apply foldl_invariant (SetRegInv t1 c.mem.last) _ _ _ h2
      intro _ x _ hb
      exact hb.step x hload hload
  simp only [finishInstr] at hth
  split at hth
  · -- a successful compare-and-swap: two threads
    rw [List.mem_cons, List.mem_singleton] at hth
    rcases hth with rfl | rfl
    · refine finish _ ?_ _ rfl
      apply foldl_invariant (SetRegInv t1 c.mem.last) _ _ _ h2
      intro b x _ hb
      have := b.rviewOf_le hb.2.2.2 x; have := b.wviewOf_le hb.2.2.2 x
      exact hb.step x (by omega_t) (by omega_t)
    · exact finish _ (h3 _ h2) _ rfl
  · rw [List.mem_singleton] at hth
    subst hth
    exact finish _ (h3 _ h2) _ rfl

/-- One instruction of a `Seq` thread run alone: every successful outcome's
memory is a sequential run of the instruction's event tree, and the thread
stays `Seq`. -/
theorem stepOne_sound (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} (ht : t.Seq tid mem)
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    ∃ tree, I.exec t.st = some tree ∧ (o.thread.st, o.mem) ∈ seqRun tid mem tree ∧ o.thread.Seq tid o.mem := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    refine ⟨tree, rfl, ?_⟩
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hregs : t.RegsLe mem.last := ⟨ht.rview, ht.wview⟩
      have hc : Ctx.Seq tid { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } :=
        ⟨ht.prom, ht.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
      have hiv := instrViews_le hregs (I.deps t.st)
      obtain ⟨hseq, hc'⟩ := runTree_sound A tid _ tree _ hc hiv st c' hr
      have hlast := seqRun_last_le tid tree mem st c'.mem hseq
      obtain ⟨hst, hth'⟩ := finishInstr_seq hc' (hiv.mono hlast) (hregs.mono hlast) th hth
      exact ⟨hst ▸ hseq, hth'⟩

/-! ## A promise-free machine step of a one-thread configuration -/

theorem Config.withThread_one (t t' : Thread I) (mem mem' : Memory) :
    (Config.withThread ⟨#[t], mem⟩ 0 t' mem').threads = #[t'] := rfl

theorem Config.withThread_one_mem (t t' : Thread I) (mem mem' : Memory) :
    (Config.withThread ⟨#[t], mem⟩ 0 t' mem').mem = mem' := rfl

theorem stepThread_one (A : Arch) (t : Thread I) (mem : Memory) :
    stepThread A ⟨#[t], mem⟩ 0 = stepOne A t 0 mem := rfl

/-- The instruction-step successors `succsL` collects: each is `withThread`
of a successful outcome. -/
private theorem foldl_outcomes_spec (A : Arch) (fuel : Nat) (c : Config I) (tid : Nat)
    (outs : List (Except String (Outcome I)))
    (init : List (Config I × List TraceEv) × Bool × List String × CertCache I) :
    ∀ x ∈ (outs.foldl (fun (next, bound, faults, cache) (o : Except String (Outcome I)) =>
        match o with
        | .error m => (next, bound, faults ++ [m], cache)
        | .ok o =>
          let c' := c.withThread tid o.thread o.mem
          if o.thread.prom.isEmpty then ((c', o.log) :: next, bound, faults, cache)
          else
            let (r, cache) := certify A cache o.thread tid o.mem fuel
            if r.certified then ((c', o.log) :: next, bound || r.boundHit, faults, cache)
            else (next, bound || r.boundHit, faults, cache)) init).1,
      x ∈ init.1 ∨ ∃ o, .ok o ∈ outs ∧ x = (c.withThread tid o.thread o.mem, o.log) := by
  apply foldl_invariant (fun acc : List (Config I × List TraceEv) × Bool × List String × CertCache I =>
    ∀ x ∈ acc.1, x ∈ init.1 ∨ ∃ o, .ok o ∈ outs ∧ x = (c.withThread tid o.thread o.mem, o.log))
  · intro x hx; exact .inl hx
  · intro acc o ho hacc x hx
    obtain ⟨next, bound, faults, cache⟩ := acc
    cases o with
    | error m => exact hacc x hx
    | ok o =>
      simp only at hx
      split at hx
      · rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .inr ⟨o, ho, rfl⟩
        · exact hacc x hx
      · split at hx
        · rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact .inr ⟨o, ho, rfl⟩
          · exact hacc x hx
        · exact hacc x hx

/-- A step of `succs` from a one-thread `Seq` configuration that leaves no
promise outstanding is an instruction step whose memory is a sequential run
of the instruction's tree, and the thread stays `Seq`. (The other successors
are certified promises; each leaves a promise outstanding.) -/
theorem succs_sound (A : Arch) (fuel : Nat) {t : Thread I} {mem : Memory} (ht : t.Seq 0 mem)
    {c' : Config I} (hc' : c' ∈ (succs A ⟨#[t], mem⟩ fuel).1)
    (hpf : ∀ t' ∈ c'.threads, t'.prom = []) :
    ∃ t' tree, c'.threads = #[t'] ∧ I.exec t.st = some tree ∧
      (t'.st, c'.mem) ∈ seqRun 0 mem tree ∧ t'.Seq 0 c'.mem := by
  have hr : List.range (#[t] : Array (Thread I)).size = [0] := rfl
  have hget : (#[t] : Array (Thread I))[0]? = some t := rfl
  -- a certified promise leaves a promise outstanding
  have hprom : ∀ (t' : Thread I) (ws : List Msg) (cache : CertCache I) (m' : Memory),
      c' ∈ List.map (fun x => x.1) (List.map (fun x => (x.1, [x.2]))
        (ws.map fun w => (Config.withThread ⟨#[t], m'⟩ 0 { t' with prom := t'.prom ++ [(mem.append { w with tid := 0 }).2] }
          (mem.append { w with tid := 0 }).1, TraceEv.promise 0 w.loc w.val (mem.append { w with tid := 0 }).2))) →
      False := by
    intro t' ws cache m' h
    simp only [List.map_map, List.mem_map, Function.comp] at h
    obtain ⟨w, _, rfl⟩ := h
    have := hpf _ (by rw [Config.withThread_one]; exact Array.mem_singleton.mpr rfl)
    simp at this
  cases hstep : stepOne A t 0 mem with
  | none =>
    simp only [succs, succsL, hr, List.foldl_cons, List.foldl_nil, stepThread_one, hstep, certifiedPromises, hget,
      List.reverse_nil, List.nil_append] at hc'
    exact (hprom t _ ∅ mem hc').elim
  | some outs =>
    simp only [succs, succsL, hr, List.foldl_cons, List.foldl_nil, stepThread_one, hstep, certifiedPromises, hget,
      List.map_append, List.mem_append] at hc'
    rcases hc' with h | h
    · rw [List.mem_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      rw [List.mem_reverse] at hx
      rcases foldl_outcomes_spec A fuel ⟨#[t], mem⟩ 0 outs ([], false, [], ∅) x hx with h | ⟨o, ho, rfl⟩
      · exact absurd h List.not_mem_nil
      · obtain ⟨tree, hex, hseq, hseq'⟩ := stepOne_sound A ht hstep ho
        exact ⟨o.thread, tree, rfl, hex, hseq, hseq'⟩
    · exact (hprom t _ ∅ mem h).elim

/-- No thread of the configuration has a promise outstanding. -/
def Config.PromFree (c : Config I) : Prop := ∀ t ∈ c.threads, t.prom = []

/-- Reachability along machine steps that never leave a promise outstanding:
the promise-free fragment of `Reachable`. -/
inductive ReachablePF (A : Arch) (fuel : Nat) : Config I → Config I → Prop
  | refl (c : Config I) : ReachablePF A fuel c c
  | step {c c' c'' : Config I} : c' ∈ (succs A c fuel).1 → c'.PromFree → ReachablePF A fuel c' c'' →
      ReachablePF A fuel c c''

theorem ReachablePF.reachable {A : Arch} {fuel : Nat} {c c' : Config I} (h : ReachablePF A fuel c c') :
    Reachable A fuel c c' := by
  induction h with
  | refl c => exact .refl c
  | step hs _ _ ih => exact .step hs ih

/-- The sequential run relation on (ISA state, memory): the instruction at the
pc, interpreted by `seqRun`. -/
inductive SeqReach (tid : Nat) : I.State × Memory → I.State × Memory → Prop
  | refl (p : I.State × Memory) : SeqReach tid p p
  | step {s : I.State} {m : Memory} {p p' : I.State × Memory} {tree : EvTree I.State} :
      I.exec s = some tree → p ∈ seqRun tid m tree → SeqReach tid p p' → SeqReach tid (s, m) p'

/-- Conservativity at the machine level: a promise-free run of the machine
from a one-thread `Seq` configuration is a sequential run of the ISA on the
memory, and the thread stays `Seq`. -/
theorem reachablePF_sound (A : Arch) (fuel : Nat) {c c'' : Config I} (h : ReachablePF A fuel c c'') :
    ∀ (t : Thread I) (mem : Memory), c = ⟨#[t], mem⟩ → t.Seq 0 mem →
      ∃ t'', c''.threads = #[t''] ∧ t''.Seq 0 c''.mem ∧ SeqReach 0 (t.st, mem) (t''.st, c''.mem) := by
  induction h with
  | refl c =>
    intro t mem hc ht
    subst hc
    exact ⟨t, rfl, ht, .refl _⟩
  | step hs hpf _ ih =>
    intro t mem hc ht
    subst hc
    obtain ⟨t', tree, hth, hex, hseq, ht'⟩ := succs_sound A fuel ht hs hpf
    obtain ⟨t'', h1, h2, h3⟩ := ih t' _ (by rw [← hth]) ht'
    exact ⟨t'', h1, h2, .step hex hseq h3⟩

end Machine

/-! ## Sanity checks -/

private def testMem : Memory :=
  { init := [(⟨0x10, 8⟩, 7)],
    msgs := #[⟨⟨0x10, 8⟩, 1, 0⟩, ⟨⟨0x18, 8⟩, 2, 0⟩, ⟨⟨0x10, 8⟩, 3, 1⟩, ⟨⟨0x20, 8⟩, 4, 0⟩] }

/-- info: [3, 2, 4, 0] -/
#guard_msgs in
#eval [testMem.lastWrite ⟨0x10, 8⟩, testMem.lastWrite ⟨0x18, 8⟩, testMem.lastWrite ⟨0x20, 8⟩,
  testMem.lastWrite ⟨0x28, 8⟩]

/-- info: [some 0x00000000000000000000000000000003#128,
 some 0x00000000000000000000000000000002#128,
 some 0x00000000000000000000000000000004#128,
 some 0x00000000000000000000000000000000#128] -/
#guard_msgs in
#eval [⟨0x10, 8⟩, ⟨0x18, 8⟩, ⟨0x20, 8⟩, ⟨0x28, 8⟩].map fun (l : Loc) => testMem.read? l (testMem.lastWrite l)

/-- A load of `x`, a store exclusive to `x` of the loaded value plus one, the
status returned: sequentially, success (memory grown) or spurious failure. -/
private def testTree : EvTree (Bool × Val) :=
  .load .plain true ⟨0x10, 8⟩ fun v => .store .plain true ⟨0x10, 8⟩ (v + 1) fun ok => .done (ok, v)

/-- info: [((true, 0x00000000000000000000000000000003#128), 5, 0x00000000000000000000000000000004#128),
 ((false, 0x00000000000000000000000000000003#128), 4, 0x00000000000000000000000000000003#128)] -/
#guard_msgs in
#eval (seqRun 0 testMem testTree).map fun (s, m) => (s, m.last, m.finalVal ⟨0x10, 8⟩)

end Kraken.Promising
