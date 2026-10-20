/-
**Part 1: the iterated take.** ISA-neutral.

The take rule of `SLR/TakeRule.lean` moves the resource of *one*
slot `((l, ts), ι, R)` into the taking thread, swapping `ι` for a fresh id.
On the `EnvG` route an acquire load takes **all** the thread's exposed slots
of the message it reads (a deterministic choice): for every acquire id `ι` of `l` the
thread holds once (`Ghost.acqIds`), in increasing order, if the ghost has a
slot `((l, ts), ι, R)` (`slotAt`), take it (`takeStep`). `takeAll` folds
this; `TakeAcc.ren` records the renaming `ι ↦ ι'` (for `seen`).

What is proved:

- `takeFold_spec` / `takeAll_spec`: the iterated take keeps erasure (with the
  taking thread exempt from promise validity, `T tid`, as `Erase.take`), is
  an `RStepS` (K2 scoped to the ids allocated before it, K1 at a floor `≥
  ts`), grows the ghost (`Ghost.Le`), keeps pending marks, and does not let
  the thread write anything new (`mayWrite` back, the `acqLe` conjunct).
- `takeAll_noSlot`, `takeAll_of_no_ids`: with no exposed slot (in particular
  holding no acquire id of `l`) nothing changes, which is how the existing
  `LoadOut` is the no-slot case of `LoadOutT` (`EnvG/TakeFacts.lean`).
- `takeAll_wr_pos` / `takeAll_wr_pos_of_slot`: write permissions survive the
  take, and those of every taken slot are gained.

Phase-1 limits (as for the take rule): only non-forwarded acquire loads take
(the floor bound `ts ≤ wfloor`); no fence-node take; a take and the use of
what it takes are in different instructions (single-access trees).
-/
import Kraken.Promising.SLR.TakeRuleThread
import Kraken.Promising.SLR.EnvG.State

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View`/`PredId` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View, PredId] at *); omega))

/-! ## Definitions -/

/-- The state of an iterated take: the thread's resource, the ghost, and the
renaming of acquire ids done so far (`(ι, ι')`: `ι` was swapped for `ι'`). -/
structure TakeAcc where
  r : Res
  g : Ghost
  ren : List (PredId × PredId) := []

/-- The slot of message `k` and id `ι` in `g`, if any (the first; erasure
makes it unique, `Erase.slotsNodup`). -/
def slotAt (g : Ghost) (k : Key) (ι : PredId) : Option Slot :=
  g.u.find? fun s => decide (s.key = k ∧ s.id = ι)

/-- **One step of the iterated take** at message `(l, tr)`: if the ghost has
a slot `((l, tr), ι, R)`, take it (`takeRes`/`takeGhost` with the fresh id
`g.acqTab.length`), else nothing. -/
def takeStep (l : Loc) (tr : Time) (a : TakeAcc) (ι : PredId) : TakeAcc :=
  match slotAt a.g (l, tr) ι with
  | some s => ⟨takeRes a.r l ι a.g.acqTab.length s.res, takeGhost a.g l ι tr, a.ren ++ [(ι, a.g.acqTab.length)]⟩
  | none => a

/-- **The iterated take** of an acquire load of `(l, tr)` by a thread holding
`r` at ghost `g`: every acquire id of `l` held once, in increasing order. -/
def takeAll (l : Loc) (tr : Time) (r : Res) (g : Ghost) : TakeAcc :=
  (g.acqIds r.acq l).foldl (takeStep l tr) ⟨r, g, []⟩

/-! ## `slotAt` -/

theorem slotAt_some {g : Ghost} {k : Key} {ι : PredId} {s : Slot} (h : slotAt g k ι = some s) :
    s ∈ g.u ∧ s.key = k ∧ s.id = ι := by
  unfold slotAt at h
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [decide_eq_true_eq] at h2
  exact ⟨h1, h2⟩

theorem slotAt_none {g : Ghost} {k : Key} {ι : PredId} (h : slotAt g k ι = none) :
    ∀ s ∈ g.u, ¬ (s.key = k ∧ s.id = ι) := by
  unfold slotAt at h
  intro s hs hk
  have := List.find?_eq_none.mp h s hs
  simp only [decide_eq_true_eq] at this
  exact this hk

/-- Two members of a list with the same image under a map whose image list
has no duplicates are equal. -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {L : List α}, (L.map f).Nodup → ∀ {a b : α}, a ∈ L → b ∈ L → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: L, h, a, b, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (by rw [e]; exact List.mem_map_of_mem hb') h.1
    · exact absurd (by rw [← e]; exact List.mem_map_of_mem ha') h.1
    · exact eq_of_nodup_map h.2 ha' hb' e

/-- With no duplicate `(key, id)` (`Erase.slotsNodup`), `slotAt` finds the
slot. -/
theorem slotAt_of_mem {g : Ghost} (hnd : (g.u.map fun s => (s.key, s.id)).Nodup) {s : Slot} (hs : s ∈ g.u) :
    slotAt g s.key s.id = some s := by
  unfold slotAt
  cases hf : g.u.find? (fun s' => decide (s'.key = s.key ∧ s'.id = s.id)) with
  | none =>
    have := List.find?_eq_none.mp hf s hs
    simp at this
  | some s' =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [decide_eq_true_eq] at h2
    rw [eq_of_nodup_map hnd h1 hs (by rw [h2.1, h2.2])]

/-- A take of another id (neither `ι` nor the fresh id) does not change
`slotAt … ι`. -/
theorem slotAt_takeGhost {g : Ghost} {l : Loc} {ι₀ ι : PredId} {ts : Time} {k : Key} (hne : ι ≠ ι₀)
    (hnf : ι ≠ g.acqTab.length) : slotAt (takeGhost g l ι₀ ts) k ι = slotAt g k ι := by
  unfold slotAt takeGhost
  simp only
  rw [List.find?_map]
  have hp : ((fun s => decide (s.key = k ∧ s.id = ι)) ∘ takeSlot l ι₀ g.acqTab.length ts) =
      fun s => decide (s.key = k ∧ s.id = ι) := by
    funext s
    simp only [Function.comp]
    unfold takeSlot
    by_cases h : s.key.1 = l ∧ s.id = ι₀
    · simp only [h, and_self, ↓reduceIte]
      have h1 : ¬ (g.acqTab.length = ι) := fun e => hnf e.symm
      have h3 : ¬ (ι₀ = ι) := fun e => hne e.symm
      simp only [h1, h3, and_false]
    · simp only [h, ↓reduceIte]
  rw [hp]
  cases hf : g.u.find? (fun s => decide (s.key = k ∧ s.id = ι)) with
  | none => rfl
  | some s =>
    have h2 := List.find?_some hf
    simp only [decide_eq_true_eq] at h2
    simp only [Option.map_some]
    unfold takeSlot
    have : ¬ (s.key.1 = l ∧ s.id = ι₀) := fun h => hne (h2.2 ▸ h.2)
    simp only [this, ↓reduceIte]

/-! ## Structural facts -/

theorem takeGhost_pend (g : Ghost) (l : Loc) (ι : PredId) (ts : Time) : (takeGhost g l ι ts).pend = g.pend := rfl

theorem takeRes_wr_pos {r R : Res} {l : Loc} {ι ι' : PredId} {x : Loc} (h : 0 < (r.wr x).q) :
    0 < ((takeRes r l ι ι' R).wr x).q :=
  Res.pos_op.mpr (.inl h)

theorem takeRes_wr_pos_R {r R : Res} {l : Loc} {ι ι' : PredId} {x : Loc} (h : 0 < (R.wr x).q) :
    0 < ((takeRes r l ι ι' R).wr x).q :=
  Res.pos_op.mpr (.inr h)

/-- An id other than the swapped pair keeps (at least) its count. -/
theorem takeRes_acq_ge {r R : Res} {l : Loc} {ι ι' j : PredId} (h1 : j ≠ ι) (h2 : j ≠ ι') :
    r.acq l j ≤ (takeRes r l ι ι' R).acq l j := by
  simp only [takeRes, Res.op, swapAcq, true_and, h1, h2, ↓reduceIte]
  omega

theorem takeFold_pend (l : Loc) (tr : Time) :
    ∀ (ids : List PredId) (a : TakeAcc), (ids.foldl (takeStep l tr) a).g.pend = a.g.pend
  | [], _ => rfl
  | ι :: ids, a => by
    rw [List.foldl_cons, takeFold_pend l tr ids]
    unfold takeStep
    split <;> rfl

theorem takeFold_wr_pos (l : Loc) (tr : Time) {x : Loc} :
    ∀ (ids : List PredId) (a : TakeAcc), 0 < (a.r.wr x).q → 0 < ((ids.foldl (takeStep l tr) a).r.wr x).q
  | [], _, h => h
  | ι :: ids, a, h => by
    rw [List.foldl_cons]
    refine takeFold_wr_pos l tr ids _ ?_
    unfold takeStep
    split
    · exact takeRes_wr_pos h
    · exact h

theorem takeFold_le (l : Loc) (tr : Time) :
    ∀ (ids : List PredId) (a : TakeAcc), a.g.Le (ids.foldl (takeStep l tr) a).g
  | [], a => Ghost.Le.refl a.g
  | ι :: ids, a => by
    rw [List.foldl_cons]
    refine Ghost.Le.trans ?_ (takeFold_le l tr ids _)
    unfold takeStep
    split
    · exact takeGhost_le _ _ _ _
    · exact Ghost.Le.refl _

theorem takeFold_length (l : Loc) (tr : Time) :
    ∀ (ids : List PredId) (a : TakeAcc), a.g.acqTab.length ≤ (ids.foldl (takeStep l tr) a).g.acqTab.length :=
  fun ids a => (takeFold_le l tr ids a).acqTab.length_le

/-- With no exposed slot, the iterated take changes nothing. -/
theorem takeFold_noSlot (l : Loc) (tr : Time) :
    ∀ (ids : List PredId) (a : TakeAcc), (∀ ι ∈ ids, slotAt a.g (l, tr) ι = none) →
      ids.foldl (takeStep l tr) a = a
  | [], _, _ => rfl
  | ι :: ids, a, h => by
    rw [List.foldl_cons]
    have e : takeStep l tr a ι = a := by
      unfold takeStep
      rw [h ι (List.mem_cons_self ..)]
    rw [e]
    exact takeFold_noSlot l tr ids a fun j hj => h j (List.mem_cons_of_mem _ hj)

theorem takeAll_noSlot {l : Loc} {tr : Time} {r : Res} {g : Ghost}
    (h : ∀ ι ∈ g.acqIds r.acq l, slotAt g (l, tr) ι = none) : takeAll l tr r g = ⟨r, g, []⟩ :=
  takeFold_noSlot l tr _ _ h

/-- Holding no acquire id of `l`, the iterated take changes nothing. -/
theorem takeAll_of_no_ids {l : Loc} {tr : Time} {r : Res} {g : Ghost} (h : ∀ ι, r.acq l ι ≠ 1) :
    takeAll l tr r g = ⟨r, g, []⟩ := by
  refine takeAll_noSlot fun ι hι => ?_
  unfold Ghost.acqIds at hι
  have := (List.mem_filter.mp hι).2
  simp only [beq_iff_eq] at this
  exact absurd this (h ι)

/-- **Every taken slot's write permissions are gained**: if, at its turn,
the slot of `ι` is `s` (true at the start for an id not yet taken, by
`slotAt_takeGhost`), its positive write permissions end in the thread. -/
theorem takeFold_wr_pos_of_slot (l : Loc) (tr : Time) {x : Loc} {ι : PredId} {s : Slot}
    (hx : 0 < (s.res.wr x).q) :
    ∀ (ids : List PredId) (a : TakeAcc), ι ∈ ids → ids.Nodup → (∀ j ∈ ids, j < a.g.acqTab.length) →
      slotAt a.g (l, tr) ι = some s → 0 < ((ids.foldl (takeStep l tr) a).r.wr x).q
  | [], _, h, _, _, _ => absurd h List.not_mem_nil
  | j :: ids, a, hm, hnd, hlt, hs => by
    rw [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with rfl | hm
    · refine takeFold_wr_pos l tr ids _ ?_
      unfold takeStep
      rw [hs]
      exact takeRes_wr_pos_R hx
    · have hne : ι ≠ j := fun e => hnd.1 (e ▸ hm)
      have hlt' : ∀ j' ∈ ids, j' < (takeStep l tr a j).g.acqTab.length := fun j' hj' =>
        Nat.lt_of_lt_of_le (hlt j' (List.mem_cons_of_mem _ hj')) (by
          unfold takeStep; split
          · rw [takeGhost_length]; exact Nat.le_succ _
          · exact Nat.le_refl _)
      refine takeFold_wr_pos_of_slot l tr hx ids _ hm hnd.2 hlt' ?_
      unfold takeStep
      split
      · rw [slotAt_takeGhost hne (Nat.ne_of_lt (hlt ι (List.mem_cons_of_mem _ hm)))]
        exact hs
      · exact hs

theorem acqIds_nodup (g : Ghost) (A : Loc → PredId → Nat) (x : Loc) : (g.acqIds A x).Nodup :=
  (List.nodup_range).filter _

theorem mem_acqIds {g : Ghost} {A : Loc → PredId → Nat} {x : Loc} {ι : PredId} (h : ι ∈ g.acqIds A x) :
    A x ι = 1 ∧ ι < g.acqTab.length := by
  unfold Ghost.acqIds at h
  obtain ⟨h1, h2⟩ := List.mem_filter.mp h
  simp only [beq_iff_eq] at h2
  exact ⟨h2, List.mem_range.mp h1⟩

/-- **The write permissions of a taken slot**: a slot `s` of the message
`(l, tr)` for an acquire id the thread holds once is taken whole. -/
theorem takeAll_wr_pos_of_slot {l : Loc} {tr : Time} {r : Res} {g : Ghost} {s : Slot} {x : Loc}
    (hι : s.id ∈ g.acqIds r.acq l) (hs : slotAt g (l, tr) s.id = some s) (hx : 0 < (s.res.wr x).q) :
    0 < ((takeAll l tr r g).r.wr x).q :=
  takeFold_wr_pos_of_slot l tr hx _ _ hι (acqIds_nodup _ _ _) (fun _ hj => (mem_acqIds hj).2) hs

theorem takeAll_wr_pos {l : Loc} {tr : Time} {r : Res} {g : Ghost} {x : Loc} (h : 0 < (r.wr x).q) :
    0 < ((takeAll l tr r g).r.wr x).q :=
  takeFold_wr_pos l tr _ _ h

/-! ## Erasure, reach and `acqLe` of the iterated take -/

/-- `RStepS` is reflexive. -/
theorem RStepS.refl (B : Time) (r : Res) (g : Ghost) (cx : Ctx) : RStepS B r g r g cx :=
  ⟨Nat.le_refl _, fun _ _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- **The iterated take, by induction on the ids**: erasure (taking thread
exempt, `T tid`), `RStepS` at any context whose floor is at least `tr`,
ghost growth, `acqLe`. The ids are distinct, held (at least once) and
allocated below `n₀ ≤` the table's length. -/
theorem takeFold_spec {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {tid : Nat} {l : Loc} {tr : Time}
    {cx : Ctx} {B : Time} (hn : tid < c.threads.size) (hT : T tid) (hfl : tr ≤ cx.views.wfloor) (n₀ : Nat) :
    ∀ (ids : List PredId) (a : TakeAcc), ids.Nodup → (∀ ι ∈ ids, 1 ≤ a.r.acq l ι ∧ ι < n₀) →
      n₀ ≤ a.g.acqTab.length → Erase (setRes rF tid a.r) a.g T c →
      Erase (setRes rF tid (ids.foldl (takeStep l tr) a).r) (ids.foldl (takeStep l tr) a).g T c ∧
        RStepS B a.r a.g (ids.foldl (takeStep l tr) a).r (ids.foldl (takeStep l tr) a).g cx ∧
        (∀ x, mayWrite (ids.foldl (takeStep l tr) a).r (ids.foldl (takeStep l tr) a).g x → mayWrite a.r a.g x)
  | [], a, _, _, _, E => ⟨E, RStepS.refl _ _ _ _, fun _ h => h⟩
  | ι :: ids, a, hnd, hids, hn₀, E => by
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    obtain ⟨hι, hιn⟩ := hids ι (List.mem_cons_self ..)
    have hιlt : ι < a.g.acqTab.length := Nat.lt_of_lt_of_le hιn hn₀
    cases hsl : slotAt a.g (l, tr) ι with
    | none =>
      have e : takeStep l tr a ι = a := by unfold takeStep; rw [hsl]
      rw [e]
      exact takeFold_spec hn hT hfl n₀ ids a hnd.2 (fun j hj => hids j (List.mem_cons_of_mem _ hj)) hn₀ E
    | some s =>
      obtain ⟨hs, hk, hid⟩ := slotAt_some hsl
      have hs' : (⟨(l, tr), ι, s.res⟩ : Slot) ∈ a.g.u := by
        obtain ⟨k, j, R⟩ := s
        simp only at hk hid
        subst hk hid
        exact hs
      have e : takeStep l tr a ι =
          ⟨takeRes a.r l ι a.g.acqTab.length s.res, takeGhost a.g l ι tr, a.ren ++ [(ι, a.g.acqTab.length)]⟩ := by
        unfold takeStep; rw [hsl]
      rw [e]
      have E1 := Erase.take E hn hT hι hs'
      have hR1 := Erase.rStepS_take (B := B) E hι hιlt hs' hfl
      have hmw1 := takeMayWrite (ts := tr) E.take_fresh (E.take_free l) (E.take_upd l) hι hιlt hs'
      have hids' : ∀ j ∈ ids, 1 ≤ (takeRes a.r l ι a.g.acqTab.length s.res).acq l j ∧ j < n₀ := by
        intro j hj
        obtain ⟨h1, h2⟩ := hids j (List.mem_cons_of_mem _ hj)
        have hne1 : j ≠ ι := fun e => hnd.1 (e ▸ hj)
        have hne2 : j ≠ a.g.acqTab.length := fun e => by omega_t
        exact ⟨Nat.le_trans h1 (takeRes_acq_ge hne1 hne2), h2⟩
      have hn₀' : n₀ ≤ (takeGhost a.g l ι tr).acqTab.length := by rw [takeGhost_length]; omega
      obtain ⟨E2, hR2, hmw2⟩ := takeFold_spec hn hT hfl n₀ ids
        ⟨takeRes a.r l ι a.g.acqTab.length s.res, takeGhost a.g l ι tr, a.ren ++ [(ι, a.g.acqTab.length)]⟩ hnd.2 hids'
        hn₀' E1
      exact ⟨E2, hR1.trans hR2 (Nat.le_refl _), fun x hx => hmw1 x (hmw2 x hx)⟩

/-- **The iterated take of an acquire load** (`takeFold_spec` at the held
ids): erasure, `RStepS`, `acqLe`, ghost growth, pending marks. -/
theorem takeAll_spec {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {tid : Nat} {l : Loc} {tr : Time}
    {cx : Ctx} {B : Time} {r : Res} {g : Ghost} (hn : tid < c.threads.size) (hT : T tid)
    (hfl : tr ≤ cx.views.wfloor) (E : Erase (setRes rF tid r) g T c) :
    Erase (setRes rF tid (takeAll l tr r g).r) (takeAll l tr r g).g T c ∧
      RStepS B r g (takeAll l tr r g).r (takeAll l tr r g).g cx ∧
      (∀ x, mayWrite (takeAll l tr r g).r (takeAll l tr r g).g x → mayWrite r g x) ∧
      g.Le (takeAll l tr r g).g ∧ (takeAll l tr r g).g.pend = g.pend := by
  obtain ⟨E', hR, hmw⟩ := takeFold_spec (a := ⟨r, g, []⟩) (B := B) hn hT hfl g.acqTab.length (g.acqIds r.acq l)
    (acqIds_nodup _ _ _) (fun ι hι => ⟨Nat.le_of_eq (mem_acqIds hι).1.symm, (mem_acqIds hι).2⟩)
    (Nat.le_refl _) E
  exact ⟨E', hR, hmw, takeFold_le l tr (g.acqIds r.acq l) ⟨r, g, []⟩,
    takeFold_pend l tr (g.acqIds r.acq l) ⟨r, g, []⟩⟩

#print axioms takeAll_spec
#print axioms takeAll_wr_pos_of_slot

end Kraken.Promising.SLR.EnvG
