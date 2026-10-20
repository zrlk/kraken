/-
**Part 1: what an iterated take gives,
exactly.** ISA-neutral. Additive (new file; `EnvG/TakeAll.lean` unchanged).

`EnvG/TakeAll.lean` proves that a take keeps erasure and that the write
permissions of a taken slot become positive in the thread. A program that
*writes* with what it took and then argues about final values needs more:
the thread's whole write permission and write set after the take.

- `takeFold_wr` / `takeFold_wr_of_slot`: the write permission of `x` after an
  iterated take is the thread's before, plus (when the slot `s` of a held id
  is taken) `s`'s, plus a remainder `d` (the other taken slots), fraction-wise
  and write-set-wise.
- `takeAll_erase`: the iterated take keeps validity-free erasure at any
  anchor (`takeAll_spec` at a context of floor `ts`).
- `takeAll_wr_full`: **a taken slot holding all of `x` is all of the
  thread's `x` after the take**: fraction `1`, and the write set is the
  slot's (validity forces the thread's old share and the remainder to `0`).
- `takeFold_held` / `takeAll_held`: an acquire id the thread holds survives
  the take, possibly renamed to a fresh id whose predicate is the old one
  relaxed at the message read (`Pred.takeAt`). A spinning reader needs this:
  an acquire load that reads a message whose slot it does not want (e.g. a
  zero flag) still takes it.
- `Erase.thread_q_le`, `Erase.thread_acq_le`: a thread's own fraction and
  acquire counts are at most `1` under any erasure.

Phase-1 limits as `EnvG/TakeAll.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeAll
import Kraken.Promising.SLR.StoreHelpers

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## Validity of the thread's own resource -/

theorem _root_.Kraken.Promising.SLR.Erase.thread_q_le {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {r : Res}
    (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size) (x : Loc) : (r.wr x).q ≤ 1 := by
  have h1 := (sub_total_thread (rF := setRes rF tid r) (g := g) hn).q_le x
  rw [setRes_self] at h1
  have h2 := E.q_le_one x
  grind

theorem _root_.Kraken.Promising.SLR.Erase.thread_acq_le {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {r : Res}
    (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size) (x : Loc) (ι : PredId) : r.acq x ι ≤ 1 := by
  have h1 := sub_acq_le (sub_total_thread (rF := setRes rF tid r) (g := g) hn) x ι
  rw [setRes_self] at h1
  have h2 := E.valid.2 x ι
  omega

/-! ## The write permission after a take -/

/-- One step adds a permission (the taken slot's, or nothing). -/
theorem takeStep_wr (l : Loc) (tr : Time) (x : Loc) (a : TakeAcc) (j : PredId) :
    ∃ e : Perm, ((takeStep l tr a j).r.wr x).q = (a.r.wr x).q + e.q ∧
      ∀ p, ((takeStep l tr a j).r.wr x).X p ↔ (a.r.wr x).X p ∨ e.X p := by
  unfold takeStep
  split
  · next s _ => exact ⟨s.res.wr x, rfl, fun _ => Iff.rfl⟩
  · exact ⟨Perm.unit, (Rat.add_zero _).symm, fun _ => ⟨.inl, fun h => h.elim id False.elim⟩⟩

/-- **The iterated take adds a permission.** -/
theorem takeFold_wr (l : Loc) (tr : Time) (x : Loc) :
    ∀ (ids : List PredId) (a : TakeAcc), ∃ d : Perm,
      ((ids.foldl (takeStep l tr) a).r.wr x).q = (a.r.wr x).q + d.q ∧
        ∀ p, ((ids.foldl (takeStep l tr) a).r.wr x).X p ↔ (a.r.wr x).X p ∨ d.X p
  | [], _ => ⟨Perm.unit, (Rat.add_zero _).symm, fun _ => ⟨.inl, fun h => h.elim id False.elim⟩⟩
  | j :: ids, a => by
    rw [List.foldl_cons]
    obtain ⟨e, he, hX⟩ := takeStep_wr l tr x a j
    obtain ⟨d, hd, hXd⟩ := takeFold_wr l tr x ids (takeStep l tr a j)
    refine ⟨e.op d, ?_, fun p => ?_⟩
    · rw [hd, he]; show _ = _ + (e.q + d.q); rw [Rat.add_assoc]
    · rw [hXd, hX]; show _ ↔ _ ∨ (e.X p ∨ d.X p); exact or_assoc

/-- **The iterated take adds the slot of a held id**, and a remainder. -/
theorem takeFold_wr_of_slot (l : Loc) (tr : Time) (x : Loc) {ι : PredId} {s : Slot} :
    ∀ (ids : List PredId) (a : TakeAcc), ι ∈ ids → ids.Nodup → (∀ j ∈ ids, j < a.g.acqTab.length) →
      slotAt a.g (l, tr) ι = some s → ∃ d : Perm,
        ((ids.foldl (takeStep l tr) a).r.wr x).q = (a.r.wr x).q + (s.res.wr x).q + d.q ∧
        ∀ p, ((ids.foldl (takeStep l tr) a).r.wr x).X p ↔ (a.r.wr x).X p ∨ (s.res.wr x).X p ∨ d.X p
  | [], _, h, _, _, _ => absurd h List.not_mem_nil
  | j :: ids, a, hm, hnd, hlt, hs => by
    rw [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with rfl | hm
    · have e : takeStep l tr a ι =
          ⟨takeRes a.r l ι a.g.acqTab.length s.res, takeGhost a.g l ι tr, a.ren ++ [(ι, a.g.acqTab.length)]⟩ := by
        unfold takeStep; rw [hs]
      rw [e]
      obtain ⟨d, hd, hXd⟩ := takeFold_wr l tr x ids
        ⟨takeRes a.r l ι a.g.acqTab.length s.res, takeGhost a.g l ι tr, a.ren ++ [(ι, a.g.acqTab.length)]⟩
      exact ⟨d, hd, fun p => by rw [hXd]; exact or_assoc⟩
    · have hne : ι ≠ j := fun e => hnd.1 (e ▸ hm)
      have hlt' : ∀ j' ∈ ids, j' < (takeStep l tr a j).g.acqTab.length := fun j' hj' =>
        Nat.lt_of_lt_of_le (hlt j' (List.mem_cons_of_mem _ hj')) (by
          unfold takeStep; split
          · rw [takeGhost_length]; exact Nat.le_succ _
          · exact Nat.le_refl _)
      have hs' : slotAt (takeStep l tr a j).g (l, tr) ι = some s := by
        unfold takeStep
        split
        · rw [slotAt_takeGhost hne (Nat.ne_of_lt (hlt ι (List.mem_cons_of_mem _ hm)))]
          exact hs
        · exact hs
      obtain ⟨d, hd, hXd⟩ := takeFold_wr_of_slot l tr x ids _ hm hnd.2 hlt' hs'
      obtain ⟨e, he, hX⟩ := takeStep_wr l tr x a j
      refine ⟨e.op d, ?_, fun p => ?_⟩
      · rw [hd, he]; show _ = _ + _ + (e.q + d.q); grind
      · rw [hXd, hX]; show _ ↔ _ ∨ _ ∨ (e.X p ∨ d.X p); grind

/-- **The iterated take keeps validity-free erasure** (`takeAll_spec` at a
context whose floor is the message read). -/
theorem takeAll_erase {rF : Nat → Res} {c : Config I} {tid : Nat} {l : Loc} {tr : Time} {r : Res} {g : Ghost}
    (hn : tid < c.threads.size) (E : Erase (setRes rF tid r) g (fun _ => True) c) :
    Erase (setRes rF tid (takeAll l tr r g).r) (takeAll l tr r g).g (fun _ => True) c :=
  (takeAll_spec (cx := { views := { vwNew := tr }, prom := [], mem := c.mem }) (B := 0) hn trivial
    (Nat.le_max_left _ _) E).1

/-- **A taken slot holding all of `x` is all of the thread's `x`** after the
take: fraction `1`, write set the slot's. -/
theorem takeAll_wr_full {rF : Nat → Res} {c : Config I} {tid : Nat} {l : Loc} {tr : Time} {r : Res} {g : Ghost}
    (hn : tid < c.threads.size) (E : Erase (setRes rF tid r) g (fun _ => True) c) {s : Slot} (hs : s ∈ g.u)
    (hk : s.key = (l, tr)) (hι : r.acq l s.id = 1) {x : Loc} (hq : (s.res.wr x).q = 1) :
    ((takeAll l tr r g).r.wr x).q = 1 ∧ ∀ p, ((takeAll l tr r g).r.wr x).X p ↔ (s.res.wr x).X p := by
  have hsl := slotAt_of_mem E.slotsNodup hs
  rw [hk] at hsl
  have hmem : s.id ∈ g.acqIds r.acq l := by
    unfold Ghost.acqIds
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (E.slotIds s hs), by simp [hι]⟩
  obtain ⟨d, hd, hXd⟩ := takeFold_wr_of_slot l tr x _ ⟨r, g, []⟩ hmem (acqIds_nodup _ _ _)
    (fun _ hj => (mem_acqIds hj).2) hsl
  have hle := (takeAll_erase (l := l) (tr := tr) hn E).thread_q_le hn x
  change ((takeAll l tr r g).r.wr x).q = (r.wr x).q + (s.res.wr x).q + d.q at hd
  change ∀ p, ((takeAll l tr r g).r.wr x).X p ↔ (r.wr x).X p ∨ (s.res.wr x).X p ∨ d.X p at hXd
  have h0 := (r.wr x).nonneg
  have h1 := d.nonneg
  have hr0 : (r.wr x).q = 0 := by grind
  have hd0 : d.q = 0 := by grind
  refine ⟨by grind, fun p => ?_⟩
  rw [hXd]
  exact ⟨fun h => h.elim (fun h' => absurd h' ((r.wr x).zero hr0 p))
    (fun h' => h'.elim id fun h'' => absurd h'' (d.zero hd0 p)), fun h => .inr (.inl h)⟩

/-! ## A held acquire id survives the take -/

/-- **A held id survives the iterated take** (possibly swapped for a fresh
id whose predicate is the old one relaxed at the message, once taken; a
swapped id is not among the ids still to take). -/
theorem takeFold_held (l : Loc) (tr : Time) (P0 : Pred) :
    ∀ (ids : List PredId) (a : TakeAcc), ids.Nodup → (∀ j ∈ ids, j < a.g.acqTab.length) →
      (∃ ι, 1 ≤ a.r.acq l ι ∧ ι < a.g.acqTab.length ∧
        (a.g.acqPred ι = P0 ∨ (a.g.acqPred ι = P0.takeAt tr ∧ ι ∉ ids))) →
      ∃ ι', 1 ≤ (ids.foldl (takeStep l tr) a).r.acq l ι' ∧ ι' < (ids.foldl (takeStep l tr) a).g.acqTab.length ∧
        ((ids.foldl (takeStep l tr) a).g.acqPred ι' = P0 ∨
          (ids.foldl (takeStep l tr) a).g.acqPred ι' = P0.takeAt tr)
  | [], a, _, _, ⟨ι, h1, h2, h3⟩ => ⟨ι, h1, h2, h3.imp id And.left⟩
  | j :: ids, a, hnd, hlt, ⟨ι, h1, h2, h3⟩ => by
    rw [List.foldl_cons]
    rw [List.nodup_cons] at hnd
    have hlt' : ∀ j' ∈ ids, j' < (takeStep l tr a j).g.acqTab.length := fun j' hj' =>
      Nat.lt_of_lt_of_le (hlt j' (List.mem_cons_of_mem _ hj')) (by
        unfold takeStep; split
        · rw [takeGhost_length]; exact Nat.le_succ _
        · exact Nat.le_refl _)
    refine takeFold_held l tr P0 ids _ hnd.2 hlt' ?_
    by_cases hj : j = ι
    · subst hj
      have hP : a.g.acqPred j = P0 := by
        rcases h3 with h | ⟨-, h⟩
        · exact h
        · exact absurd (List.mem_cons_self ..) h
      unfold takeStep
      split
      · refine ⟨a.g.acqTab.length, ?_, by rw [takeGhost_length]; exact Nat.lt_succ_self _, .inr ⟨?_, ?_⟩⟩
        · have hne : a.g.acqTab.length ≠ j := Nat.ne_of_gt h2
          simp only [takeRes, Res.op, swapAcq, true_and, hne, ↓reduceIte]
          omega
        · rw [takeGhost_acqPred_new, hP]
        · intro hm
          exact Nat.lt_irrefl _ (hlt _ (List.mem_cons_of_mem _ hm))
      · exact ⟨j, h1, h2, .inl hP⟩
    · have hnin : ι ∈ ids → a.g.acqPred ι = P0 := fun hm => by
        rcases h3 with h | ⟨-, h⟩
        · exact h
        · exact absurd (List.mem_cons_of_mem _ hm) h
      unfold takeStep
      split
      · have hne2 : ι ≠ a.g.acqTab.length := Nat.ne_of_lt h2
        refine ⟨ι, Nat.le_trans h1 (takeRes_acq_ge (Ne.symm hj) hne2),
          by rw [takeGhost_length]; exact Nat.lt_succ_of_lt h2, ?_⟩
        rw [takeGhost_acqPred_old h2]
        rcases h3 with h | ⟨h, h'⟩
        · exact .inl h
        · exact .inr ⟨h, fun hm => h' (List.mem_cons_of_mem _ hm)⟩
      · rcases h3 with h | ⟨h, h'⟩
        · exact ⟨ι, h1, h2, .inl h⟩
        · exact ⟨ι, h1, h2, .inr ⟨h, fun hm => h' (List.mem_cons_of_mem _ hm)⟩⟩

/-- **A held id survives `takeAll`**, with its predicate or its predicate
relaxed at the message read. -/
theorem takeAll_held {l : Loc} {tr : Time} {r : Res} {g : Ghost} {ι : PredId} (h1 : 1 ≤ r.acq l ι)
    (h2 : ι < g.acqTab.length) :
    ∃ ι', 1 ≤ (takeAll l tr r g).r.acq l ι' ∧ ι' < (takeAll l tr r g).g.acqTab.length ∧
      ((takeAll l tr r g).g.acqPred ι' = g.acqPred ι ∨
        (takeAll l tr r g).g.acqPred ι' = (g.acqPred ι).takeAt tr) :=
  takeFold_held l tr (g.acqPred ι) _ ⟨r, g, []⟩ (acqIds_nodup _ _ _) (fun _ hj => (mem_acqIds hj).2)
    ⟨ι, h1, h2, .inl rfl⟩

/-! ## The take only adds (from `EnvG/TicketLockVC.lean`) -/

/-- The take does not decrease any fraction. -/
theorem takeAll_q_ge (l : Loc) (tr : Time) (r : Res) (g : Ghost) (x : Loc) :
    (r.wr x).q ≤ ((takeAll l tr r g).r.wr x).q := by
  obtain ⟨d, hd, -⟩ := takeFold_wr l tr x (g.acqIds r.acq l) ⟨r, g, []⟩
  show (r.wr x).q ≤ (((g.acqIds r.acq l).foldl (takeStep l tr) ⟨r, g, []⟩).r.wr x).q
  rw [hd]; have := d.nonneg; grind

/-- The take adds the slot of a held id (`takeAll_wr_full`'s first steps). -/
theorem takeAll_q_slot {rF : Nat → Res} {c : Config I} {tid : Nat} {l : Loc} {tr : Time} {r : Res} {g : Ghost}
    (E : Erase (setRes rF tid r) g (fun _ => True) c) {s : Slot} (hs : s ∈ g.u)
    (hk : s.key = (l, tr)) (hι : r.acq l s.id = 1) (x : Loc) :
    (r.wr x).q + (s.res.wr x).q ≤ ((takeAll l tr r g).r.wr x).q := by
  have hsl := slotAt_of_mem E.slotsNodup hs
  rw [hk] at hsl
  have hmem : s.id ∈ g.acqIds r.acq l := by
    unfold Ghost.acqIds
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (E.slotIds s hs), by simp [hι]⟩
  obtain ⟨d, hd, -⟩ := takeFold_wr_of_slot l tr x _ ⟨r, g, []⟩ hmem (acqIds_nodup _ _ _)
    (fun _ hj => (mem_acqIds hj).2) hsl
  change ((takeAll l tr r g).r.wr x).q = (r.wr x).q + (s.res.wr x).q + d.q at hd
  rw [hd]; have := d.nonneg; grind

#print axioms takeAll_wr_full
#print axioms takeAll_held

end Kraken.Promising.SLR.EnvG
