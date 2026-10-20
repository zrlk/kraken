/-
Simulation library, part 1: the relation. One simulation relation for "a thread's run survives a
change of the memory, views and promises underneath it".

Modules: `Sim.Rel` (this file: timestamp maps, the relation, map helpers),
`Sim.Event` (per-event simulations), `Sim.Run` (event trees, thread steps,
solo runs), `Sim.Instances` (memory extension, environment, certification).

ISA-neutral. Design prototype: the relation, the per-event simulation lemmas
(read, write, fence, the RMW / exclusive atomic check), their chaining through
one instruction's event tree (`runTree_sim`) and one thread step
(`stepOne_sim`), the `PromisePure` break event (`writeSuccs_break`), and the
prototype instance (memory extension of a promise-free run,
`readSuccs_memExt`, `runTree_memExt`). Everything is proved; nothing is
assumed.

**The relation** (`CtxRel ρ c c'`, source `c`, target `c'`):
- `ρ : TMap` is a *partial strictly monotone* map from (some of) the source
  memory's timestamps to the target memory's, with `0 ↦ 0`, and its *floor*
  `ρ.fv` on views: `ρ.fv v = ρ.f s` for the largest `s ∈ dom ρ` with `s ≤ v`.
  `ρ.fv` is monotone, so it commutes with `max`, which is all the rules do to
  views.
- memories: every source message at `s ∈ dom ρ` is the target message at
  `ρ.f s` (`MemRel`). Target messages outside the image are *foreign*.
- views: target views are at most the floor-image of the source views
  (`ViewsLe`); forwarding entries and the load-exclusive buffer have exactly
  mapped timestamps (and equal `xcl` / location), their views only `≤`.
- promises: target promises are exactly the images of the source promises
  in `dom ρ`.
- the event-level side condition, **gap freedom** (`GapFree`): no foreign
  target message to the accessed location in the event's window. At tree
  level it is discharged from `FgnSep` (where the foreign messages sit) and
  the source-run condition `StaleFree` (no stale read / exclusive pair on a
  location that has foreign messages).

Instances: B2 and O11 take `ρ = id` on
the base memory and shift the thread's own fresh writes past the foreign
messages; the whole-thread environment takes `ρ = id`, `M' = M` and the
`≤` on views; general `PromisePure` (A) takes `dom ρ = M ∖ {p}` up to the
fulfilling event and then needs a non-monotone *break* event
(`writeSuccs_break`).
-/

import Kraken.Promising.ReleasePrefixNT

namespace Kraken.Promising

namespace Sim

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Timestamp maps -/

/-- A partial, strictly monotone map of source timestamps to target
timestamps, with its floor extension to views. -/
structure TMap where
  dom : Time → Prop
  f : Time → Time
  /-- The floor extension to views: `fv v = f s` for the largest `s ∈ dom`
  below `v` (`fv_floor`, `fv_dom`). -/
  fv : View → View
  dom0 : dom 0
  f0 : f 0 = 0
  strict : ∀ a b, dom a → dom b → a < b → f a < f b
  fv_dom : ∀ a, dom a → fv a = f a
  fv_mono : ∀ a b, a ≤ b → fv a ≤ fv b
  fv_floor : ∀ v, ∃ s, dom s ∧ s ≤ v ∧ fv v = f s

namespace TMap

variable (ρ : TMap)

theorem fv_max (a b : View) : ρ.fv (max a b) = max (ρ.fv a) (ρ.fv b) := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (ρ.fv_mono _ _ h)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (ρ.fv_mono _ _ h)]

theorem fv_zero : ρ.fv 0 = 0 := by rw [ρ.fv_dom 0 ρ.dom0, ρ.f0]

theorem f_inj {a b : Time} (ha : ρ.dom a) (hb : ρ.dom b) (h : ρ.f a = ρ.f b) : a = b := by
  rcases Nat.lt_trichotomy a b with h' | h' | h'
  · have := ρ.strict a b ha hb h'; omega_t
  · exact h'
  · have := ρ.strict b a hb ha h'; omega_t

theorem f_le_iff {a b : Time} (ha : ρ.dom a) (hb : ρ.dom b) : ρ.f a ≤ ρ.f b ↔ a ≤ b := by
  constructor
  · intro h
    refine Nat.le_of_not_lt fun h' => ?_
    have := ρ.strict b a hb ha h'; omega_t
  · intro h
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Nat.le_of_lt (ρ.strict a b ha hb h)
    · rw [h]; exact Nat.le_refl _

theorem f_lt_iff {a b : Time} (ha : ρ.dom a) (hb : ρ.dom b) : ρ.f a < ρ.f b ↔ a < b := by
  have := ρ.f_le_iff hb ha; omega_t

/-- The key floor property: an image below the floor of `b` comes from a
timestamp below `b`. -/
theorem le_of_f_le_fv {s b : Time} (hs : ρ.dom s) (h : ρ.f s ≤ ρ.fv b) : s ≤ b := by
  obtain ⟨s0, hs0, hle, he⟩ := ρ.fv_floor b
  rw [he] at h
  exact Nat.le_trans ((ρ.f_le_iff hs hs0).mp h) hle

theorem f_lt_fv {s b : Time} (hs : ρ.dom s) (h : s < b) (hb : ρ.dom b) : ρ.f s < ρ.fv b := by
  rw [ρ.fv_dom b hb]; exact ρ.strict s b hs hb h

/-- The identity on `[0, n]`, floored at `n`: memory extension (prototype). -/
def idUpTo (n : Nat) : TMap where
  dom s := s ≤ n
  f s := s
  fv v := min v n
  dom0 := Nat.zero_le _
  f0 := rfl
  strict _ _ _ _ h := h
  fv_dom a h := Nat.min_eq_left h
  fv_mono a b h := by omega_t
  fv_floor v := ⟨min v n, Nat.min_le_right _ _, Nat.min_le_left _ _, rfl⟩

/-- Extend `ρ` by one new pair `a ↦ a'` above everything: a fresh write
("promise now") at the end of both memories. Monotone because `a` and `a'`
are above the domain and the image. -/
def extend (a a' : Time) (ha : ∀ s, ρ.dom s → s < a) (ha' : ∀ s, ρ.dom s → ρ.f s < a') : TMap where
  dom s := ρ.dom s ∨ s = a
  f s := if s = a then a' else ρ.f s
  fv v := if a ≤ v then a' else ρ.fv v
  dom0 := .inl ρ.dom0
  f0 := by
    have := ha 0 ρ.dom0
    rw [ite_eq_right (by omega_t), ρ.f0]
  strict x y hx hy hxy := by
    rcases hx with hx | rfl <;> rcases hy with hy | rfl
    · have := ha x hx; have := ha y hy
      rw [ite_eq_right (by omega_t), ite_eq_right (by omega_t)]; exact ρ.strict x y hx hy hxy
    · have := ha x hx
      rw [ite_eq_right (by omega_t), ite_eq_left rfl]; exact ha' x hx
    · have := ha y hy; omega_t
    · omega_t
  fv_dom x hx := by
    rcases hx with hx | rfl
    · have := ha x hx
      rw [ite_eq_right (by omega_t), ite_eq_right (by omega_t), ρ.fv_dom x hx]
    · simp
  fv_mono x y hxy := by
    by_cases hx : a ≤ x
    · rw [ite_eq_left hx, ite_eq_left (Nat.le_trans hx hxy)]; exact Nat.le_refl _
    · rw [ite_eq_right hx]
      by_cases hy : a ≤ y
      · rw [ite_eq_left hy]
        obtain ⟨s, hs, -, he⟩ := ρ.fv_floor x
        rw [he]; exact Nat.le_of_lt (ha' s hs)
      · rw [ite_eq_right hy]; exact ρ.fv_mono x y hxy
  fv_floor v := by
    by_cases hv : a ≤ v
    · exact ⟨a, .inr rfl, hv, by simp [hv]⟩
    · obtain ⟨s, hs, hle, he⟩ := ρ.fv_floor v
      have := ha s hs
      exact ⟨s, .inl hs, hle, by rw [ite_eq_right hv, ite_eq_right (by omega_t), he]⟩

end TMap

/-! ## The relation -/

/-- Pointwise relation of two lists (core has no `Rel2`). -/
inductive Rel2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Rel2 R [] []
  | cons {a b xs ys} : R a b → Rel2 R xs ys → Rel2 R (a :: xs) (b :: ys)

theorem Rel2.append {α β : Type} {R : α → β → Prop} {xs ys : List α} {xs' ys' : List β}
    (h : Rel2 R xs xs') (h' : Rel2 R ys ys') : Rel2 R (xs ++ ys) (xs' ++ ys') := by
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact .cons hab ih

theorem max_le_max' {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) : max a c ≤ max b d := by
  omega

theorem le_fv_max {ρ : TMap} {a' a b' b : View} (ha : a' ≤ ρ.fv a) (hb : b' ≤ ρ.fv b) :
    max a' b' ≤ ρ.fv (max a b) := by
  rw [ρ.fv_max]; exact max_le_max' ha hb

/-- Source messages in the domain are the target messages at their images. -/
structure MemRel (ρ : TMap) (M M' : Memory) : Prop where
  init : M'.init = M.init
  dom_le : ∀ s, ρ.dom s → s ≤ M.last
  f_le : ∀ s, ρ.dom s → ρ.f s ≤ M'.last
  get : ∀ s, ρ.dom s → M'.get? (ρ.f s) = M.get? s

/-- A target timestamp outside the image of `ρ`: a foreign message's. -/
def Foreign (ρ : TMap) (s' : Time) : Prop := ¬ ∃ s, ρ.dom s ∧ ρ.f s = s'

/-- No foreign target message to `l` in `(lo, hi]`. The one dynamic side
condition of the schema: it is vacuous when the target has no foreign
messages (environment instance, `PromisePure` instance), and it is the real
content of the B2 instance. -/
def GapFree (ρ : TMap) (M' : Memory) (l : Loc) (lo hi : Time) : Prop :=
  ∀ s' w, lo < s' → s' ≤ hi → Foreign ρ s' → M'.get? s' = some w → w.loc ≠ l

/-- Forwarding entries: the same entry up to `ρ` (exact timestamp, view
only `≤`). -/
def FwdLe (ρ : TMap) : Option FwdItem → Option FwdItem → Prop
  | none, none => True
  | some a, some b => ρ.dom a.time ∧ b.time = ρ.f a.time ∧ b.view ≤ ρ.fv a.view ∧ b.xcl = a.xcl ∧
      min b.xclRead b.time ≤ ρ.fv (min a.xclRead a.time)
  | _, _ => False

/-- Load-exclusive buffers: exact timestamp and location, view `≤`. -/
def XclLe (ρ : TMap) : Option (Time × View × Loc) → Option (Time × View × Loc) → Prop
  | none, none => True
  | some (t, v, l), some (t', v', l') => ρ.dom t ∧ t' = ρ.f t ∧ v' ≤ ρ.fv v ∧ l' = l
  | _, _ => False

theorem XclLe.xclRead {ρ : TMap} {a b : Option (Time × View × Loc)} (h : XclLe ρ a b) :
    (b.map (·.2.1)).getD 0 ≤ ρ.fv ((a.map (·.2.1)).getD 0) := by
  rcases a with _ | ⟨t, ν, l⟩ <;> rcases b with _ | ⟨t', ν', l'⟩
  · exact Nat.zero_le _
  · exact (h : False).elim
  · exact (h : False).elim
  · exact h.2.2.1

/-- Target views are at most the floor image of the source views. -/
structure ViewsLe (ρ : TMap) (vs' vs : Views) : Prop where
  coh : ∀ l, vs'.getCoh l ≤ ρ.fv (vs.getCoh l)
  vrNew : vs'.vrNew ≤ ρ.fv vs.vrNew
  vrOld : vs'.vrOld ≤ ρ.fv vs.vrOld
  vrOldNR : vs'.vrOldNR ≤ ρ.fv vs.vrOldNR
  vwNew : vs'.vwNew ≤ ρ.fv vs.vwNew
  vwOld : vs'.vwOld ≤ ρ.fv vs.vwOld
  vwOldNT : vs'.vwOldNT ≤ ρ.fv vs.vwOldNT
  vCAP : vs'.vCAP ≤ ρ.fv vs.vCAP
  vRel : vs'.vRel ≤ ρ.fv vs.vRel
  fwd : ∀ l, FwdLe ρ (vs.getFwd l) (vs'.getFwd l)
  xclb : XclLe ρ vs.xclb vs'.xclb

/-- Instruction views: target at most the floor image of the source. -/
structure IVLe (ρ : TMap) (iv' iv : InstrViews) : Prop where
  addrR : iv'.addrR ≤ ρ.fv iv.addrR
  addrW : iv'.addrW ≤ ρ.fv iv.addrW
  dataR : iv'.dataR ≤ ρ.fv iv.dataR
  dataW : iv'.dataW ≤ ρ.fv iv.dataW
  condW : iv'.condW ≤ ρ.fv iv.condW
  dataPer : Rel2 (fun p' p => p'.1 ≤ ρ.fv p.1 ∧ p'.2 ≤ ρ.fv p.2) iv'.dataPer iv.dataPer

/-- Promise lists: the target's are the images of the source's in the
domain, in order (an exact list relation, so that `erase` commutes even with
duplicate entries). -/
inductive PromRel (ρ : TMap) : List Time → List Time → Prop
  | nil : PromRel ρ [] []
  | keep {t xs ys} : ρ.dom t → PromRel ρ xs ys → PromRel ρ (t :: xs) (ρ.f t :: ys)
  | drop {t xs ys} : ¬ ρ.dom t → PromRel ρ xs ys → PromRel ρ (t :: xs) ys

namespace PromRel

theorem mem {ρ : TMap} {xs ys : List Time} (h : PromRel ρ xs ys) (t' : Time) :
    t' ∈ ys ↔ ∃ t ∈ xs, ρ.dom t ∧ ρ.f t = t' := by
  induction h with
  | nil => simp
  | keep hd _ ih =>
    simp only [List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨t, ht, hd', rfl⟩)
      · exact ⟨_, .inl rfl, hd, rfl⟩
      · exact ⟨t, .inr ht, hd', rfl⟩
    · rintro ⟨t, (rfl | ht), hd', rfl⟩
      · exact .inl rfl
      · exact .inr ⟨t, ht, hd', rfl⟩
  | drop hn _ ih =>
    simp only [List.mem_cons, ih]
    constructor
    · rintro ⟨t, ht, hd', rfl⟩; exact ⟨t, .inr ht, hd', rfl⟩
    · rintro ⟨t, (rfl | ht), hd', rfl⟩
      · exact absurd hd' hn
      · exact ⟨t, ht, hd', rfl⟩

theorem erase {ρ : TMap} {xs ys : List Time} (h : PromRel ρ xs ys) {t : Time} (ht : ρ.dom t) :
    PromRel ρ (xs.erase t) (ys.erase (ρ.f t)) := by
  induction h with
  | nil => exact .nil
  | @keep s xs ys hs h' ih =>
    by_cases e : s = t
    · subst e; rw [List.erase_cons_head, List.erase_cons_head]; exact h'
    · have e' : ρ.f s ≠ ρ.f t := fun h => e (ρ.f_inj hs ht h)
      rw [List.erase_cons_tail (by simpa using e), List.erase_cons_tail (by simpa using e')]
      exact .keep hs ih
  | @drop s xs ys hs _ ih =>
    have e : s ≠ t := fun h => hs (h ▸ ht)
    rw [List.erase_cons_tail (by simpa using e)]
    exact .drop hs ih

theorem append {ρ : TMap} {xs ys xs' ys' : List Time} (h : PromRel ρ xs ys) (h' : PromRel ρ xs' ys') :
    PromRel ρ (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => exact h'
  | keep hd _ ih => exact .keep hd ih
  | drop hn _ ih => exact .drop hn ih

/-- Transport along a map that agrees on the domain, when every promise is in
the domain. -/
theorem lift {ρ ρ' : TMap} {xs ys : List Time} (h : PromRel ρ xs ys)
    (hag : ∀ s, ρ.dom s → ρ'.dom s ∧ ρ'.f s = ρ.f s) (hd : ∀ s ∈ xs, ρ.dom s) : PromRel ρ' xs ys := by
  induction h with
  | nil => exact .nil
  | keep hs _ ih =>
    have := hag _ hs
    rw [← this.2]
    exact .keep this.1 (ih fun s hs' => hd s (List.mem_cons_of_mem _ hs'))
  | drop hn _ _ => exact absurd (hd _ List.mem_cons_self) hn

end PromRel

/-- **The relation** between a source context `c` and a target context `c'`
of the same instruction of the same thread. -/
structure CtxRel (ρ : TMap) (c c' : Ctx) : Prop where
  mem : MemRel ρ c.mem c'.mem
  views : ViewsLe ρ c'.views c.views
  prom : PromRel ρ c.prom c'.prom
  loadViews : Rel2 (fun a' a => a' ≤ ρ.fv a) c'.loadViews c.loadViews
  succView : c'.succView ≤ ρ.fv c.succView
  rmwWrote : c'.rmwWrote = c.rmwWrote
  stores : c'.stores = c.stores

/-- Every target message is an image: no foreign messages (the environment
and `PromisePure` instances). -/
def NoForeign (ρ : TMap) (M' : Memory) : Prop :=
  ∀ s', 1 ≤ s' → s' ≤ M'.last → ∃ s, ρ.dom s ∧ ρ.f s = s'

/-- Foreign target messages sit strictly between the images of the source's
base `[0, n]` and the images of the source's later timestamps, and are to
locations in `L`. B2: the other threads' messages `M_K ∖ M_J`, after `M_J`
(`n = |M_J|`) and before the thread's own fresh writes. O11: the other
threads' messages, after the base memory and before the advanced thread's
non-temporal messages. `NoForeign` is the case without foreign messages. -/
def FgnSep (ρ : TMap) (M' : Memory) (n : Nat) (L : Loc → Prop) : Prop :=
  ∀ s' w, Foreign ρ s' → M'.get? s' = some w → L w.loc ∧ ρ.fv n < s' ∧ ∀ s, ρ.dom s → n < s → s' < ρ.f s

theorem get?_some_le' {M : Memory} {s : Time} {w : Msg} (h : M.get? s = some w) : 1 ≤ s ∧ s ≤ M.last := by
  unfold Memory.get? at h
  split at h
  · cases h
  · refine ⟨by omega_t, Nat.le_of_not_lt fun hlt => ?_⟩
    rw [Array.getElem?_eq_none (by unfold Memory.last at hlt; omega_t)] at h
    cases h

/-- No foreign target message to `l` by another thread strictly inside
`(lo, hi)`: the side condition of an exclusive/RMW write (`Memory.atomic`). -/
def AtomGap (ρ : TMap) (M' : Memory) (l : Loc) (tid : Nat) (lo hi : Time) : Prop :=
  ∀ s' w, lo < s' → s' < hi → Foreign ρ s' → M'.get? s' = some w → w.loc = l → w.tid = tid

theorem get?_some_le {M : Memory} {s : Time} {w : Msg} (h : M.get? s = some w) : 1 ≤ s ∧ s ≤ M.last := by
  unfold Memory.get? at h
  split at h
  · cases h
  · refine ⟨by omega_t, Nat.le_of_not_lt fun hlt => ?_⟩
    rw [Array.getElem?_eq_none (by unfold Memory.last at hlt; omega_t)] at h
    cases h

/-! ## Foreign messages at several thresholds (interleaved foreign appends)

`FgnSep ρ M' n L` fixes *one* threshold `n` for all foreign messages: they lie
above the images of the source's base `[0, n]` and below the images of every
later source timestamp. When other threads append *between* the replayed
steps (B2 with interleaving, O11 with several append points), a foreign message
appended after the thread's own fresh write at `s > n` lies above `ρ.f s`, so
no single `n` works. `FgnSepAt ρ M' N L` gives every foreign message its own
threshold from a set `N`: the source memory size at the time it was appended.
The source-run condition becomes `StaleFree` at every threshold in `N`. -/

/-- Every foreign target message is to a location in `L` and is separated at
*some* threshold `n ∈ N`: above the floor image of `n`, below the images of
all source timestamps above `n`. -/
def FgnSepAt (ρ : TMap) (M' : Memory) (N : Nat → Prop) (L : Loc → Prop) : Prop :=
  ∀ s' w, Foreign ρ s' → M'.get? s' = some w →
    L w.loc ∧ ∃ n, N n ∧ ρ.fv n < s' ∧ ∀ s, ρ.dom s → n < s → s' < ρ.f s

theorem FgnSep.toAt {ρ : TMap} {M' : Memory} {n : Nat} {L : Loc → Prop} (h : FgnSep ρ M' n L) :
    FgnSepAt ρ M' (· = n) L := fun s' w hf hw =>
  let ⟨a, b, c⟩ := h s' w hf hw
  ⟨a, n, rfl, b, c⟩

theorem FgnSepAt.toSep {ρ : TMap} {M' : Memory} {n : Nat} {L : Loc → Prop} (h : FgnSepAt ρ M' (· = n) L) :
    FgnSep ρ M' n L := fun s' w hf hw => by
  obtain ⟨a, m, rfl, b, c⟩ := h s' w hf hw
  exact ⟨a, b, c⟩

theorem fgnSep_iff_at {ρ : TMap} {M' : Memory} {n : Nat} {L : Loc → Prop} :
    FgnSep ρ M' n L ↔ FgnSepAt ρ M' (· = n) L := ⟨FgnSep.toAt, FgnSepAt.toSep⟩

/-- More thresholds and more watched locations only weaken `FgnSepAt`. -/
theorem FgnSepAt.mono {ρ : TMap} {M' : Memory} {N N' : Nat → Prop} {L L' : Loc → Prop}
    (h : FgnSepAt ρ M' N L) (hN : ∀ n, N n → N' n) (hL : ∀ l, L l → L' l) : FgnSepAt ρ M' N' L' :=
  fun s' w hf hw =>
    let ⟨a, n, hn, b, c⟩ := h s' w hf hw
    ⟨hL _ a, n, hN n hn, b, c⟩

theorem NoForeign.fgnSepAt {ρ : TMap} {M' : Memory} (h : NoForeign ρ M') (N : Nat → Prop) (L : Loc → Prop) :
    FgnSepAt ρ M' N L := by
  intro s' w hfor hw
  obtain ⟨h1, h2⟩ := get?_some_le hw
  exact absurd (h s' h1 h2) hfor

/-- A foreign append keeps the memory relation (the images are unchanged). -/
theorem MemRel.appendForeign {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') (w : Msg) :
    MemRel ρ M (M'.append w).1 where
  init := hm.init
  dom_le := hm.dom_le
  f_le s hs := by rw [Memory.last_append]; exact Nat.le_succ_of_le (hm.f_le s hs)
  get s hs := by rw [Memory.get?_append_of_le _ _ _ (hm.f_le s hs)]; exact hm.get s hs

/-- The end of the target memory is above every image. -/
theorem MemRel.foreign_succ_last {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') : Foreign ρ (M'.last + 1) :=
  fun ⟨s, hs, he⟩ => by have := hm.f_le s hs; omega_t

/-- **Interleaved foreign append.** Another thread appends `w` (to a watched
location) to the target memory while the source memory is `M`: the new
foreign message is separated at the threshold `|M|`, and the old ones keep
theirs. Needs only `MemRel` (the domain is in `[0, |M|]`, the images in
`[0, |M'|]`). -/
theorem FgnSepAt.appendForeign {ρ : TMap} {M M' : Memory} {N : Nat → Prop} {L : Loc → Prop}
    (hm : MemRel ρ M M') (h : FgnSepAt ρ M' N L) {w : Msg} (hw : L w.loc) :
    FgnSepAt ρ (M'.append w).1 (fun n => N n ∨ n = M.last) L := by
  intro s' w' hfor hget
  have hle := (get?_some_le hget).2
  rw [Memory.last_append] at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · rw [Memory.get?_append_of_le _ _ _ (Nat.le_of_lt_succ hlt)] at hget
    obtain ⟨a, n, hn, b, c⟩ := h s' w' hfor hget
    exact ⟨a, n, .inl hn, b, c⟩
  · rw [Memory.get?_append_last] at hget
    cases hget
    refine ⟨hw, M.last, .inr rfl, ?_, fun s hs hlt => absurd (hm.dom_le s hs) (by omega_t)⟩
    obtain ⟨s0, hs0, -, he⟩ := ρ.fv_floor M.last
    rw [he]; exact Nat.lt_succ_of_le (hm.f_le s0 hs0)

/-- The exclusive-read timestamps of a write: the same up to `ρ`. -/
def TrRel (ρ : TMap) : Option Time → Option Time → Prop
  | none, none => True
  | some a, some a' => ρ.dom a ∧ a' = ρ.f a
  | _, _ => False

/-- A fresh write at the end of both memories extends `ρ`. -/
def freshMap (ρ : TMap) {M M' : Memory} (hm : MemRel ρ M M') : TMap :=
  ρ.extend (M.last + 1) (M'.last + 1) (fun s hs => Nat.lt_succ_of_le (hm.dom_le s hs))
    (fun s hs => Nat.lt_succ_of_le (hm.f_le s hs))

theorem freshMap_agree {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') (s : Time) (hs : ρ.dom s) :
    (freshMap ρ hm).dom s ∧ (freshMap ρ hm).f s = ρ.f s := by
  have := hm.dom_le s hs
  exact ⟨.inl hs, by simp only [freshMap, TMap.extend]; rw [ite_eq_right (by omega_t)]⟩

theorem freshMap_fv {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') {v : View} (hv : v ≤ M.last) :
    (freshMap ρ hm).fv v = ρ.fv v := by
  simp only [freshMap, TMap.extend]; rw [ite_eq_right (by omega_t)]

theorem freshMap_new {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') :
    (freshMap ρ hm).dom (M.last + 1) ∧ (freshMap ρ hm).f (M.last + 1) = M'.last + 1 :=
  ⟨.inr rfl, by simp [freshMap, TMap.extend]⟩

theorem freshMap_mem {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') (w : Msg) :
    MemRel (freshMap ρ hm) (M.append w).1 (M'.append w).1 where
  init := hm.init
  dom_le s hs := by
    rw [Memory.last_append]
    rcases hs with hs | rfl
    · exact Nat.le_succ_of_le (hm.dom_le s hs)
    · exact Nat.le_refl _
  f_le s hs := by
    rw [Memory.last_append]
    rcases hs with hs | rfl
    · rw [(freshMap_agree hm s hs).2]; exact Nat.le_succ_of_le (hm.f_le s hs)
    · rw [(freshMap_new hm).2]; exact Nat.le_refl _
  get s hs := by
    rcases hs with hs | rfl
    · rw [(freshMap_agree hm s hs).2, Memory.get?_append_of_le _ _ _ (hm.f_le s hs),
        Memory.get?_append_of_le _ _ _ (hm.dom_le s hs), hm.get s hs]
    · rw [(freshMap_new hm).2, Memory.get?_append_last, Memory.get?_append_last]

/-- Lift the relation to the fresh map, the memories and promises replaced by
related ones. Needs the source views bounded by `|M|` (`Ctx.Bnd`, an
invariant of every reachable configuration) and every promise in the domain. -/
theorem CtxRel.fresh {ρ : TMap} {c c' : Ctx} (hc : CtxRel ρ c c') (hb : c.Bnd) (hpd : ∀ s ∈ c.prom, ρ.dom s)
    (w : Msg) {pn pn' : List (Msg × View)} :
    CtxRel (freshMap ρ hc.mem)
      { c with mem := (c.mem.append w).1, prom := c.prom ++ [c.mem.last + 1], promisedNow := pn }
      { c' with mem := (c'.mem.append w).1, prom := c'.prom ++ [c'.mem.last + 1], promisedNow := pn' } := by
  have hv := hc.views
  have ag := freshMap_agree hc.mem
  have fv := fun {v} (h : v ≤ c.mem.last) => freshMap_fv hc.mem h
  have hl := hb.views.le
  refine ⟨freshMap_mem hc.mem w, ⟨fun l => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun l => ?_, ?_⟩, ?_, ?_, ?_,
    hc.rmwWrote, hc.stores⟩
  · show c'.views.getCoh l ≤ _; rw [fv (hl.coh l)]; exact hv.coh l
  · show c'.views.vrNew ≤ _; rw [fv hl.vrNew]; exact hv.vrNew
  · show c'.views.vrOld ≤ _; rw [fv hl.vrOld]; exact hv.vrOld
  · show c'.views.vrOldNR ≤ _; rw [fv hl.vrOldNR]; exact hv.vrOldNR
  · show c'.views.vwNew ≤ _; rw [fv hl.vwNew]; exact hv.vwNew
  · show c'.views.vwOld ≤ _; rw [fv hl.vwOld]; exact hv.vwOld
  · show c'.views.vwOldNT ≤ _; rw [fv hl.vwOldNT]; exact hv.vwOldNT
  · show c'.views.vCAP ≤ _; rw [fv hl.vCAP]; exact hv.vCAP
  · show c'.views.vRel ≤ _; rw [fv hl.vRel]; exact hv.vRel
  · show FwdLe _ (c.views.getFwd l) (c'.views.getFwd l)
    have h1 := hv.fwd l
    cases e : c.views.getFwd l with
    | none =>
      cases e' : c'.views.getFwd l with
      | none => trivial
      | some _ => rw [e, e'] at h1; exact h1.elim
    | some a =>
      rw [e] at h1
      cases e' : c'.views.getFwd l with
      | none => rw [e'] at h1; exact h1.elim
      | some b =>
        rw [e'] at h1
        obtain ⟨d, t, vw, x, xr⟩ := h1
        exact ⟨(ag _ d).1, by rw [(ag _ d).2]; exact t, by rw [fv (hl.fwd l a e)]; exact vw, x,
          by rw [fv (Nat.le_trans (Nat.min_le_right _ _) (hb.views.fwdTime l a e))]; exact xr⟩
  · show XclLe _ c.views.xclb c'.views.xclb
    have h1 := hv.xclb
    cases e : c.views.xclb with
    | none =>
      cases e' : c'.views.xclb with
      | none => trivial
      | some _ => rw [e, e'] at h1; exact h1.elim
    | some p =>
      obtain ⟨t, ν, l⟩ := p
      rw [e] at h1
      cases e' : c'.views.xclb with
      | none => rw [e'] at h1; exact h1.elim
      | some q =>
        obtain ⟨t', ν', l'⟩ := q
        rw [e'] at h1
        obtain ⟨d, h2, h3, h4⟩ := h1
        exact ⟨(ag _ d).1, by rw [(ag _ d).2]; exact h2, by rw [fv (hb.views.xclb t ν l e).2]; exact h3, h4⟩
  · show PromRel _ (c.prom ++ [c.mem.last + 1]) (c'.prom ++ [c'.mem.last + 1])
    refine (hc.prom.lift ag hpd).append ?_
    rw [← (freshMap_new hc.mem).2]
    exact .keep (freshMap_new hc.mem).1 .nil
  · show Rel2 _ c'.loadViews c.loadViews
    have key : ∀ (ys xs : List View), Rel2 (fun a' a => a' ≤ ρ.fv a) ys xs → (∀ ν ∈ xs, ν ≤ c.mem.last) →
        Rel2 (fun a' a => a' ≤ (freshMap ρ hc.mem).fv a) ys xs := by
      intro ys xs h hb'
      induction h with
      | nil => exact .nil
      | @cons a b xs ys hab _ ih =>
        refine .cons ?_ (ih fun ν hν => hb' ν (List.mem_cons_of_mem _ hν))
        rw [freshMap_fv hc.mem (hb' b List.mem_cons_self)]; exact hab
    exact key _ _ hc.loadViews hb.loadViews
  · show c'.succView ≤ _; rw [fv hb.succView]; exact hc.succView

theorem Rel2.get? {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β} (h : Rel2 R xs ys) (i : Nat) :
    (xs[i]? = none ∧ ys[i]? = none) ∨ ∃ a b, xs[i]? = some a ∧ ys[i]? = some b ∧ R a b := by
  induction h generalizing i with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => exact .inr ⟨a, b, rfl, rfl, hab⟩
    | succ i => exact ih i

theorem Rel2.getLastD {ρ : TMap} {ys xs : List View} (h : Rel2 (fun a' a => a' ≤ ρ.fv a) ys xs) :
    ∀ d' d, d' ≤ ρ.fv d → ys.getLastD d' ≤ ρ.fv (xs.getLastD d) := by
  induction h with
  | nil => intro d' d hd; exact hd
  | @cons a b ys xs hab _ ih => intro _ _ _; rw [List.getLastD_cons, List.getLastD_cons]; exact ih a b hab

theorem getLastD_le {xs : List View} {n : Nat} (h : ∀ ν ∈ xs, ν ≤ n) : ∀ d, d ≤ n → xs.getLastD d ≤ n := by
  induction xs with
  | nil => intro d hd; exact hd
  | cons x xs ih =>
    intro _ _
    rw [List.getLastD_cons]
    exact ih (fun ν hν => h ν (List.mem_cons_of_mem _ hν)) x (h x List.mem_cons_self)

theorem IVLe.forStore {ρ : TMap} {iv iv' : InstrViews} (h : IVLe ρ iv' iv) (i : Nat) :
    IVLe ρ (iv'.forStore i) (iv.forStore i) := by
  unfold InstrViews.forStore
  rcases h.dataPer.get? i with ⟨e1, e2⟩ | ⟨a, b, e1, e2, hab⟩
  · rw [e1, e2]; exact h
  · rw [e1, e2]; exact ⟨h.addrR, h.addrW, hab.1, hab.2, h.condW, h.dataPer⟩

theorem IVLe.lift {ρ ρ' : TMap} {iv iv' : InstrViews} {n : Nat} (h : IVLe ρ iv' iv) (hb : iv.Le n)
    (hfv : ∀ x ≤ n, ρ'.fv x = ρ.fv x) : IVLe ρ' iv' iv := by
  refine ⟨by rw [hfv _ hb.addrR]; exact h.addrR, by rw [hfv _ hb.addrW]; exact h.addrW,
    by rw [hfv _ hb.dataR]; exact h.dataR, by rw [hfv _ hb.dataW]; exact h.dataW,
    by rw [hfv _ hb.condW]; exact h.condW, ?_⟩
  have key : ∀ (ps' ps : List (View × View)),
      Rel2 (fun p' p => p'.1 ≤ ρ.fv p.1 ∧ p'.2 ≤ ρ.fv p.2) ps' ps → (∀ p ∈ ps, p.1 ≤ n ∧ p.2 ≤ n) →
      Rel2 (fun p' p => p'.1 ≤ ρ'.fv p.1 ∧ p'.2 ≤ ρ'.fv p.2) ps' ps := by
    intro ps' ps hr hp
    induction hr with
    | nil => exact .nil
    | @cons a b xs ys hab _ ih =>
      have := hp b List.mem_cons_self
      refine .cons ⟨?_, ?_⟩ (ih fun q hq => hp q (List.mem_cons_of_mem _ hq))
      · rw [hfv _ this.1]; exact hab.1
      · rw [hfv _ this.2]; exact hab.2
  exact key _ _ h.dataPer hb.dataPer

/-- `ρ'` extends `ρ`: it agrees on the domain, and on views up to `m`. -/
def Ext (ρ ρ' : TMap) (m : Nat) : Prop :=
  (∀ s, ρ.dom s → ρ'.dom s ∧ ρ'.f s = ρ.f s) ∧ ∀ x ≤ m, ρ'.fv x = ρ.fv x

theorem Ext.refl (ρ : TMap) (m : Nat) : Ext ρ ρ m := ⟨fun _ h => ⟨h, rfl⟩, fun _ _ => rfl⟩

theorem Ext.trans {ρ ρ' ρ'' : TMap} {m m' : Nat} (h : Ext ρ ρ' m) (h' : Ext ρ' ρ'' m') (hm : m ≤ m') :
    Ext ρ ρ'' m :=
  ⟨fun s hs => ⟨(h'.1 s (h.1 s hs).1).1, by rw [(h'.1 s (h.1 s hs).1).2, (h.1 s hs).2]⟩,
   fun x hx => by rw [h'.2 x (Nat.le_trans hx hm), h.2 x hx]⟩

section Thread

variable {I : ISA}

/-- Threads: same machine state, register views at most the floor images,
`ViewsLe` and `PromRel`. -/
structure ThreadRel (ρ : TMap) (t t' : Thread I) : Prop where
  st : t'.st = t.st
  rsize : t'.rview.size = t.rview.size
  wsize : t'.wview.size = t.wview.size
  rv : ∀ i : Nat, t'.rview[i]! ≤ ρ.fv t.rview[i]!
  wv : ∀ i : Nat, t'.wview[i]! ≤ ρ.fv t.wview[i]!
  views : ViewsLe ρ t'.views t.views
  prom : PromRel ρ t.prom t'.prom

end Thread

end Sim

end Kraken.Promising
