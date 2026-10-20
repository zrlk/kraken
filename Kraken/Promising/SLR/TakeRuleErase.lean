/-
**Prototype.** The erasure law of the take rule
(`SLR/TakeRule.lean`): erasure survives the swap `(l, ι) ↦ (l, ι')`
(`Erase.take`, `takeEraseLaw`; the stepping thread is exempt from promise
validity, `T tid`, as in `NPSafe`'s weak erasure and `ErAt.hval_store`).

## Structure of the proof

- The total resource: `total₀ = r • Q` before and `total₁ = swapAcq r • Q`
  after, for one `Q` (the other threads and the slots after the take; the
  taken resource `R` moves from the slots into the thread,
  `prod_takeSlot`). So write permissions are unchanged and acquire ids
  change only by `(l, ι) ↦ (l, ι')` (`take_total_acq`).
- `relAcq`: the held list of `l` loses `φ = W.acq ι` and gains
  `φ.takeAt ts ⊇ φ` (`Pred.SepList.perm`, `Pred.SepList.mono_head`).
- `slotsNodup`/`slotsDom`/`slotsPred`: the renaming is injective on
  `(key, id)` and `slotsDom` for `(l, ι)` gives the renamed slots exactly
  at the release messages of `l`.
- `promValid` (other threads): `(l, ι)` is held by the taking thread alone,
  so no other thread's chain passes through a renamed slot
  (`CanAcq.take_fwd`).

Nothing imports this file.
-/
import Kraken.Promising.SLR.TakeRule

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View`/`PredId` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View, PredId] at *); omega))

private theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

private theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

/-! ## Separating lists -/

/-- `SepList` is invariant under permutation. -/
theorem Pred.SepList.perm {L L' : List Pred} (h : L.Perm L') :
    ∀ {v : Val} {m : Memory} {V : View} {r : Res}, Pred.SepList L v m V r → Pred.SepList L' v m V r := by
  induction h with
  | nil => exact fun h => h
  | cons φ _ ih => exact fun ⟨r₁, r₂, e, h1, h2⟩ => ⟨r₁, r₂, e, h1, ih h2⟩
  | swap φ ψ L =>
    intro v m V r h
    obtain ⟨a, r₂, e, ha, b, c, e', hb, hc⟩ := h
    exact ⟨b, a.op c, by rw [e, e', Res.op_left_comm], hb, a, c, rfl, ha, hc⟩
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)

/-- `SepList` is monotone in its head predicate. -/
theorem Pred.SepList.mono_head {φ ψ : Pred} {L : List Pred} {v : Val} {m : Memory} {V : View} {r : Res}
    (hφ : ∀ r, φ.P v m V r → ψ.P v m V r) (h : Pred.SepList (φ :: L) v m V r) : Pred.SepList (ψ :: L) v m V r :=
  let ⟨r₁, r₂, e, h1, h2⟩ := h
  ⟨r₁, r₂, e, hφ r₁ h1, h2⟩

/-! ## The slots after the take -/

section Slots

variable {l : Loc} {ι ι' : PredId} {ts : Time}

theorem takeSlot_key (s : Slot) : (takeSlot l ι ι' ts s).key = s.key := by
  unfold takeSlot; split <;> rfl

theorem takeSlot_id (s : Slot) :
    (takeSlot l ι ι' ts s).id = if s.key.1 = l ∧ s.id = ι then ι' else s.id := by
  unfold takeSlot; split <;> rfl

theorem takeSlot_res (s : Slot) :
    (takeSlot l ι ι' ts s).res = if s.key = (l, ts) ∧ s.id = ι then Res.unit else s.res := by
  obtain ⟨⟨x, t⟩, j, res⟩ := s
  unfold takeSlot
  by_cases h1 : x = l ∧ j = ι
  · obtain ⟨rfl, rfl⟩ := h1
    simp only [and_true, true_and, Prod.mk.injEq, ite_true]
  · simp only [ite_f h1]
    rw [ite_f]
    rintro ⟨hk, hj⟩
    simp only [Prod.mk.injEq] at hk
    exact h1 ⟨hk.1, hj⟩

theorem takeSlot_eq_of_not {s : Slot} (h : ¬ (s.key.1 = l ∧ s.id = ι)) : takeSlot l ι ι' ts s = s := by
  unfold takeSlot; rw [ite_f h]

/-- The slot resources without the taken slot are unchanged. -/
theorem prod_takeSlot_noKey {L : List Slot} (h : ∀ s ∈ L, ¬ (s.key = (l, ts) ∧ s.id = ι)) :
    Res.prod ((L.map (takeSlot l ι ι' ts)).map (·.res)) = Res.prod (L.map (·.res)) := by
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun s hs => ?_
  simp only [Function.comp, takeSlot_res, ite_f (h s hs)]

/-- **The taken resource moves out of the slots**: with at most one slot per
message and id, the slot resources before are `R` times those after. -/
theorem prod_takeSlot {L : List Slot} {R : Res} (hnd : (L.map fun s => (s.key, s.id)).Nodup)
    (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ L) :
    Res.prod (L.map (·.res)) = R.op (Res.prod ((L.map (takeSlot l ι ι' ts)).map (·.res))) := by
  induction L with
  | nil => cases hT
  | cons s L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hnd⟩ := hnd
    by_cases hs : s.key = (l, ts) ∧ s.id = ι
    · have hL : ∀ s' ∈ L, ¬ (s'.key = (l, ts) ∧ s'.id = ι) := by
        rintro s' hs' ⟨hk, hi⟩
        apply hnot
        rw [hs.1, hs.2, ← hk, ← hi]
        exact List.mem_map_of_mem hs'
      have hsT : s = ⟨(l, ts), ι, R⟩ := by
        rcases List.mem_cons.mp hT with h | h
        · exact h.symm
        · exact absurd ⟨rfl, rfl⟩ (hL _ h)
      subst hsT
      simp only [List.map_cons, Res.prod_cons, takeSlot_res, and_self, ite_true, Res.unit_op,
        prod_takeSlot_noKey hL]
    · have hT' : (⟨(l, ts), ι, R⟩ : Slot) ∈ L := by
        rcases List.mem_cons.mp hT with h | h
        · exact absurd (by rw [← h]; exact ⟨rfl, rfl⟩) hs
        · exact h
      simp only [List.map_cons, Res.prod_cons, takeSlot_res, ite_f hs]
      rw [ih hnd hT', Res.op_left_comm]

end Slots

/-! ## The total resource -/

section Total

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {r R : Res} {l : Loc}
  {ι : PredId} {ts : Time}

/-- **The total resource before and after the take**: `r • Q` and
`swapAcq r • Q`. -/
theorem take_total (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) :
    ∃ Q, total (setRes rF tid r) g c = r.op Q ∧
      total (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) c =
        (swapAcq r l ι g.acqTab.length).op Q := by
  obtain ⟨rest, hrest⟩ := threadsRes_split rF hn
  have h0 := hrest (setRes rF tid r) fun i hi => setRes_ne rF r hi
  have h1 := hrest (setRes rF tid (takeRes r l ι g.acqTab.length R)) fun i hi => setRes_ne rF _ hi
  have hS := prod_takeSlot (ι' := g.acqTab.length) E.slotsNodup hT
  refine ⟨rest.op (R.op (Res.prod ((g.u.map (takeSlot l ι g.acqTab.length ts)).map (·.res)))), ?_, ?_⟩
  · simp only [total, Ghost.slotsRes, h0, setRes_self, hS, Res.op_assoc]
  · rw [total, Ghost.slotsRes]
    simp only [takeGhost]
    rw [h1, setRes_self]
    unfold takeRes
    simp only [Res.op_assoc]
    rw [Res.op_left_comm R rest]

theorem take_total_wr (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) :
    (total (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) c).wr =
      (total (setRes rF tid r) g c).wr := by
  obtain ⟨Q, h0, h1⟩ := take_total E hn hT
  rw [h0, h1]; rfl

/-- **Acquire ids after the take**: `(l, ι)` is gone, `(l, ι')` is held
once, everything else is unchanged. -/
theorem take_total_acq (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) (hι : 1 ≤ r.acq l ι) (x : Loc) (j : PredId) :
    (total (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) c).acq x j =
      if x = l ∧ j = ι then 0 else if x = l ∧ j = g.acqTab.length then 1
      else (total (setRes rF tid r) g c).acq x j := by
  obtain ⟨Q, h0, h1⟩ := take_total E hn hT
  have hv := E.valid.2 l ι
  have ha := E.acqIds l g.acqTab.length
  rw [h0] at hv ha
  rw [h0, h1]
  simp only [Res.op, swapAcq] at hv ha ⊢
  by_cases h1 : x = l ∧ j = ι
  · rw [ite_t h1, ite_t h1]
    obtain ⟨rfl, rfl⟩ := h1
    omega
  · rw [ite_f h1, ite_f h1]
    by_cases h2 : x = l ∧ j = g.acqTab.length
    · rw [ite_t h2, ite_t h2]
      obtain ⟨rfl, rfl⟩ := h2
      have : ¬ (1 ≤ r.acq x g.acqTab.length + Q.acq x g.acqTab.length) := fun h => by
        have := ha h; omega_t
      omega
    · rw [ite_f h2, ite_f h2]

theorem take_ι_lt (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) (hι : 1 ≤ r.acq l ι) : ι < g.acqTab.length := by
  obtain ⟨Q, h0, -⟩ := take_total (ts := ts) E hn hT
  refine E.acqIds l ι ?_
  rw [h0]; simp only [Res.op]; omega

theorem take_total_ι (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) (hι : 1 ≤ r.acq l ι) : (total (setRes rF tid r) g c).acq l ι = 1 := by
  obtain ⟨Q, h0, -⟩ := take_total (ts := ts) E hn hT
  have hv := E.valid.2 l ι
  rw [h0] at hv ⊢; simp only [Res.op] at hv ⊢; omega

theorem mem_acqIds_lt {g : Ghost} {A : Loc → PredId → Nat} {x : Loc} {j : PredId} (h : j ∈ g.acqIds A x) :
    j < g.acqTab.length := by
  simp only [Ghost.acqIds, List.mem_filter, List.mem_range] at h
  exact h.1

/-- **The held ids after the take.** -/
theorem take_acqIds (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) (hι : 1 ≤ r.acq l ι) (x : Loc) :
    (takeGhost g l ι ts).acqIds
        (total (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) c).acq x =
      if x = l then (g.acqIds (total (setRes rF tid r) g c).acq x).erase ι ++ [g.acqTab.length]
      else g.acqIds (total (setRes rF tid r) g c).acq x := by
  have hlt := take_ι_lt E hn hT hι
  have hfree : (total (setRes rF tid r) g c).acq x g.acqTab.length ≠ 1 := fun h =>
    absurd (E.acqIds x _ (by omega)) (Nat.lt_irrefl _)
  simp only [Ghost.acqIds, takeGhost_length, List.range_succ, List.filter_append,
    take_total_acq E hn hT hι]
  by_cases hx : x = l
  · subst hx
    rw [ite_t rfl, List.Nodup.erase_eq_filter (List.nodup_range.filter _), List.filter_filter]
    congr 1
    · refine List.filter_congr fun j hj => ?_
      simp only [List.mem_range] at hj
      by_cases hj' : j = ι
      · subst hj'; simp
      · have : ¬ j = g.acqTab.length := by omega_t
        simp [hj', this]
    · have : ¬ g.acqTab.length = ι := by omega_t
      simp [this]
  · rw [ite_f hx]
    have e2 : List.filter (fun j => (if x = l ∧ j = ι then 0 else if x = l ∧ j = g.acqTab.length then 1
        else (total (setRes rF tid r) g c).acq x j) == 1) [g.acqTab.length] = [] := by
      simp [hx, hfree]
    rw [e2, List.append_nil]
    refine List.filter_congr fun j _ => ?_
    simp [hx]

/-- **`relAcq` after the take**: the held list of `l` loses `φ` and gains
`φ.takeAt ts ⊇ φ`. -/
theorem take_relAcq (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) (hι : 1 ≤ r.acq l ι) :
    ∀ x v m V r', ((takeGhost g l ι ts).rel x).P v m V r' →
      Pred.SepList ((takeGhost g l ι ts).acqPreds
          (total (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) c).acq x ++
        (takeGhost g l ι ts).updPreds x) v m V r' := by
  intro x v m V r' hrel
  have h0 := E.relAcq x v m V r' hrel
  have hlt := take_ι_lt E hn hT hι
  have hupd : (takeGhost g l ι ts).updPreds x = g.updPreds x := by
    simp only [Ghost.updPreds]
    refine List.map_congr_left fun j hj => takeGhost_acqPred_old ((E.updIds x).2 j hj).1
  have hold : ∀ L : List PredId, (∀ j ∈ L, j < g.acqTab.length) →
      L.map (takeGhost g l ι ts).acqPred = L.map g.acqPred :=
    fun L hL => List.map_congr_left fun j hj => takeGhost_acqPred_old (hL j hj)
  simp only [Ghost.acqPreds, take_acqIds E hn hT hι, hupd]
  by_cases hx : x = l
  · subst hx
    rw [ite_t rfl, List.map_append, hold _ (fun j hj => mem_acqIds_lt (List.mem_of_mem_erase hj)),
      List.map_singleton, takeGhost_acqPred_new, List.append_assoc, List.singleton_append]
    refine Pred.SepList.perm List.perm_middle.symm ?_
    refine Pred.SepList.mono_head (φ := g.acqPred ι) (fun r h => Pred.le_takeAt _ _ h) ?_
    have hmem : ι ∈ g.acqIds (total (setRes rF tid r) g c).acq x := by
      simp only [Ghost.acqIds, List.mem_filter, List.mem_range, take_total_ι E hn hT hι]
      exact ⟨hlt, rfl⟩
    have hp := (List.perm_cons_erase hmem).map g.acqPred
    rw [List.map_cons] at hp
    exact Pred.SepList.perm (hp.append_right _) h0
  · rw [ite_f hx, hold _ (fun j hj => mem_acqIds_lt hj)]
    exact h0

/-! ## The slot clauses -/

private theorem nodup_map_on {α β : Type} {f : α → β} {L : List α}
    (hinj : ∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) (h : L.Nodup) : (L.map f).Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a L ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) h.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    exact h.1 (hinj a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hfb.symm ▸ hb)

theorem take_slotsNodup (E : Erase (setRes rF tid r) g T c) :
    ((g.u.map (takeSlot l ι g.acqTab.length ts)).map fun s => (s.key, s.id)).Nodup := by
  have heq : (g.u.map (takeSlot l ι g.acqTab.length ts)).map (fun s => (s.key, s.id)) =
      (g.u.map fun s => (s.key, s.id)).map
        (fun p : Key × PredId => (p.1, if p.1.1 = l ∧ p.2 = ι then g.acqTab.length else p.2)) := by
    simp only [List.map_map]
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp, takeSlot_key, takeSlot_id]
  rw [heq]
  refine nodup_map_on (fun a ha b hb hab => ?_) E.slotsNodup
  obtain ⟨sa, hsa, rfl⟩ := List.mem_map.mp ha
  obtain ⟨sb, hsb, rfl⟩ := List.mem_map.mp hb
  have la := E.slotIds sa hsa
  have lb := E.slotIds sb hsb
  simp only [Prod.mk.injEq] at hab ⊢
  obtain ⟨hk, hi⟩ := hab
  refine ⟨hk, ?_⟩
  by_cases h1 : sa.key.1 = l ∧ sa.id = ι <;> by_cases h2 : sb.key.1 = l ∧ sb.id = ι
  · exact h1.2.trans h2.2.symm
  · rw [ite_t h1, ite_f h2] at hi; omega_t
  · rw [ite_f h1, ite_t h2] at hi; omega_t
  · rwa [ite_f h1, ite_f h2] at hi

theorem take_mem_u {s : Slot} (hs : s ∈ g.u) (h : ¬ (s.key.1 = l ∧ s.id = ι)) :
    s ∈ (takeGhost g l ι ts).u := by
  have := List.mem_map_of_mem (f := takeSlot l ι g.acqTab.length ts) hs
  rwa [takeSlot_eq_of_not h] at this

theorem take_slotsDom (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) (hι : 1 ≤ r.acq l ι) (k : Key) (j : PredId) :
    (∃ s ∈ (takeGhost g l ι ts).u, s.key = k ∧ s.id = j) ↔
      (k ∈ (takeGhost g l ι ts).relMsgs ∧
        ((total (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) c).acq k.1 j = 1 ∨
          (j ∈ (takeGhost g l ι ts).upd k.1 ∧ ¬ (takeGhost g l ι ts).Claimed k))) := by
  have hlt := take_ι_lt E hn hT hι
  have h1ι := take_total_ι E hn hT hι
  have hU : ι ∉ g.upd l := fun h => by have := ((E.updIds l).2 ι h).2; omega
  simp only [take_total_acq E hn hT hι]
  show (∃ s ∈ g.u.map (takeSlot l ι g.acqTab.length ts), s.key = k ∧ s.id = j) ↔
    (k ∈ g.relMsgs ∧ ((if k.1 = l ∧ j = ι then 0 else if k.1 = l ∧ j = g.acqTab.length then 1
      else (total (setRes rF tid r) g c).acq k.1 j) = 1 ∨ (j ∈ g.upd k.1 ∧ ¬ g.Claimed k)))
  simp only [List.mem_map]
  by_cases ha : k.1 = l ∧ j = g.acqTab.length
  · have hne : ¬ (k.1 = l ∧ j = ι) := fun h => by omega_t
    rw [ite_f hne, ite_t ha]
    have hd := E.slotsDom k ι
    rw [ha.1, h1ι] at hd
    constructor
    · rintro ⟨-, ⟨s, hs, rfl⟩, hk, hj⟩
      rw [takeSlot_key] at hk
      rw [takeSlot_id] at hj
      by_cases h : s.key.1 = l ∧ s.id = ι
      · exact ⟨(hd.mp ⟨s, hs, hk, h.2⟩).1, .inl rfl⟩
      · rw [ite_f h, ha.2] at hj
        exact absurd (hj ▸ E.slotIds s hs) (Nat.lt_irrefl _)
    · rintro ⟨hk, -⟩
      obtain ⟨s, hs, hsk, hsi⟩ := hd.mpr ⟨hk, .inl rfl⟩
      refine ⟨_, ⟨s, hs, rfl⟩, by rw [takeSlot_key]; exact hsk, ?_⟩
      rw [takeSlot_id, ite_t ⟨by rw [hsk, ha.1], hsi⟩, ha.2]
  · by_cases hb : k.1 = l ∧ j = ι
    · rw [ite_t hb]
      constructor
      · rintro ⟨-, ⟨s, hs, rfl⟩, hk, hj⟩
        rw [takeSlot_key] at hk
        rw [takeSlot_id] at hj
        by_cases h : s.key.1 = l ∧ s.id = ι
        · rw [ite_t h, hb.2] at hj; omega_t
        · rw [ite_f h, hb.2] at hj
          exact absurd ⟨by rw [hk, hb.1], hj⟩ h
      · rintro ⟨-, h | ⟨hj, -⟩⟩
        · cases h
        · rw [hb.1, hb.2] at hj; exact absurd hj hU
    · rw [ite_f hb, ite_f ha, ← E.slotsDom k j]
      constructor
      · rintro ⟨-, ⟨s, hs, rfl⟩, hk, hj⟩
        rw [takeSlot_key] at hk
        rw [takeSlot_id] at hj
        by_cases h : s.key.1 = l ∧ s.id = ι
        · rw [ite_t h] at hj
          exact absurd ⟨by rw [← hk, h.1], hj.symm⟩ ha
        · rw [ite_f h] at hj
          exact ⟨s, hs, hk, hj⟩
      · rintro ⟨s, hs, hk, hj⟩
        have h : ¬ (s.key.1 = l ∧ s.id = ι) := fun h => hb ⟨by rw [← hk, h.1], by rw [← hj, h.2]⟩
        exact ⟨_, ⟨s, hs, rfl⟩, by rw [takeSlot_key]; exact hk, by rw [takeSlot_id, ite_f h]; exact hj⟩

theorem take_slotsPred (E : Erase (setRes rF tid r) g T c) :
    ∀ s ∈ (takeGhost g l ι ts).u, ∀ v, c.mem.read? s.key.1 s.key.2 = some v →
      ((takeGhost g l ι ts).acqPred s.id).P v c.mem s.key.2 s.res := by
  intro s' hs' v hv
  simp only [takeGhost, List.mem_map] at hs'
  obtain ⟨s, hs, rfl⟩ := hs'
  rw [takeSlot_key] at hv
  by_cases h : s.key.1 = l ∧ s.id = ι
  · have e : takeSlot l ι g.acqTab.length ts s =
        { key := s.key, id := g.acqTab.length, res := if s.key.2 = ts then Res.unit else s.res } := by
      unfold takeSlot; rw [ite_t h]
    rw [e]
    show ((takeGhost g l ι ts).acqPred g.acqTab.length).P v c.mem s.key.2 _
    rw [takeGhost_acqPred_new]
    by_cases ht : s.key.2 = ts
    · rw [ite_t ht]; exact .inl ⟨ht, rfl⟩
    · rw [ite_f ht]; refine .inr ?_
      have := E.slotsPred s hs v hv
      rwa [h.2] at this
  · rw [takeSlot_eq_of_not h]
    show ((takeGhost g l ι ts).acqPred s.id).P v c.mem s.key.2 s.res
    rw [takeGhost_acqPred_old (E.slotIds s hs)]
    exact E.slotsPred s hs v hv

/-! ## Promise validity of the other threads -/

/-- A chain at `g` of a resource that does not hold `(l, ι)`, where no slot
resource holds `(l, ι)` and `ι` is not an update id of `l`, never passes
through a renamed slot, so it is a chain after the take. -/
theorem CanAcq.take_fwd {A : Loc → PredId → Nat} (hA : A l ι = 0) (hS : ∀ s ∈ g.u, s.res.acq l ι = 0)
    (hU : ι ∉ g.upd l) {k : Key} {j : PredId} (h : CanAcq g.u g.upd A k j) :
    ¬ (k.1 = l ∧ j = ι) ∧ CanAcq (takeGhost g l ι ts).u (takeGhost g l ι ts).upd A k j := by
  induction h with
  | @base s hs ha =>
    have hn : ¬ (s.key.1 = l ∧ s.id = ι) := fun h => by rw [h.1, h.2] at ha; omega
    exact ⟨hn, .base (take_mem_u hs hn) ha⟩
  | @upd s hs hu =>
    have hn : ¬ (s.key.1 = l ∧ s.id = ι) := fun h => by rw [h.1, h.2] at hu; exact hU hu
    exact ⟨hn, .upd (take_mem_u hs hn) hu⟩
  | @step s s' _ hs hs' ha ih =>
    have hn : ¬ (s'.key.1 = l ∧ s'.id = ι) := fun h => by
      rw [h.1, h.2] at ha; have := hS s hs; omega
    exact ⟨hn, .step ih.2 (take_mem_u hs ih.1) (take_mem_u hs' hn) ha⟩

theorem mayWrite.take_fwd {ρ : Res} {x : Loc} (hA : ρ.acq l ι = 0) (hS : ∀ s ∈ g.u, s.res.acq l ι = 0)
    (hU : ι ∉ g.upd l) (h : mayWrite ρ g x) : mayWrite ρ (takeGhost g l ι ts) x := by
  rcases h with h | ⟨s, hs, hc, hq⟩
  · exact .inl h
  · obtain ⟨hn, hc'⟩ := hc.take_fwd (ts := ts) hA hS hU
    exact .inr ⟨s, take_mem_u hs hn, hc', hq⟩

/-- Two distinct threads' resources are both part of the threads' product. -/
theorem threadsRes_two (rF : Nat → Res) {n i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≠ j) (x : Loc)
    (k : PredId) : (rF i).acq x k + (rF j).acq x k ≤ (threadsRes rF n).acq x k := by
  obtain ⟨rest, hrest⟩ := threadsRes_split rF hi
  have h1 := hrest rF fun _ _ => rfl
  have h2 := hrest (setRes rF i Res.unit) fun m hm => setRes_ne rF _ hm
  rw [setRes_self, Res.unit_op] at h2
  obtain ⟨rest', hrest'⟩ := threadsRes_split (setRes rF i Res.unit) hj
  have h3 := hrest' (setRes rF i Res.unit) fun _ _ => rfl
  rw [setRes_ne rF _ (Ne.symm hij)] at h3
  rw [h1, ← h2, h3]
  simp only [Res.op]
  omega

end Total

/-! ## The erasure law -/

/-- **Erasure survives the take** (`TakeEraseLaw`, with the taking thread
exempt from promise validity, `T tid`). -/
theorem Erase.take {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {r R : Res}
    {l : Loc} {ι : PredId} {ts : Time} (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hTt : T tid) (hι : 1 ≤ r.acq l ι) (hT : (⟨(l, ts), ι, R⟩ : Slot) ∈ g.u) :
    Erase (setRes rF tid (takeRes r l ι g.acqTab.length R)) (takeGhost g l ι ts) T c := by
  have hlt := take_ι_lt E hn hT hι
  have h1ι := take_total_ι E hn hT hι
  have hwr := take_total_wr E hn hT
  have hacq := take_total_acq E hn hT hι
  refine
    { valid := ⟨fun x => ?_, fun x j => ?_⟩
      slotIds := fun s hs => ?_
      acqIds := fun x j hj => ?_
      relAcq := take_relAcq E hn hT hι
      writes := fun x hx p => ?_
      pure := E.pure
      relExists := E.relExists
      slotsNodup := take_slotsNodup E
      slotsDom := take_slotsDom E hn hT hι
      slotsPred := take_slotsPred E
      promWf := E.promWf
      promValid := fun i t ht hi ts' hts hp w hw => ?_
      pend := E.pend
      updIds := fun x => ⟨(E.updIds x).1, fun j hj => ?_⟩
      relSettled := E.relSettled
      claimsNodup := E.claimsNodup
      claimsAt := E.claimsAt
      claimFulf := E.claimFulf }
  · rw [hwr]; exact E.valid.1 x
  · rw [hacq]; have := E.valid.2 x j
    split
    · omega
    · split
      · omega
      · exact this
  · rw [takeGhost_length]
    simp only [takeGhost, List.mem_map] at hs
    obtain ⟨s, hs, rfl⟩ := hs
    rw [takeSlot_id]; have := E.slotIds s hs
    split
    · omega_t
    · omega_t
  · rw [takeGhost_length]
    rw [hacq] at hj
    split at hj
    · omega
    · split at hj
      · omega_t
      · have := E.acqIds x j hj; omega_t
  · have hx' : Tracked c g (total (setRes rF tid r) g c) x := by
      unfold Tracked at hx ⊢; rw [hwr] at hx; exact hx
    rw [hwr]; exact E.writes x hx' p
  · have hne : i ≠ tid := fun h => hi (h ▸ hTt)
    rw [setRes_ne rF _ hne]
    have h0 := E.promValid i t ht hi ts' hts hp w hw
    rw [setRes_ne rF _ hne] at h0
    have hni : i < c.threads.size := lt_size_of_get? ht
    have h2 := threadsRes_two (setRes rF tid r) hni hn hne l ι
    rw [setRes_self, setRes_ne rF _ hne] at h2
    have hv := E.valid.2 l ι
    have hthr : (total (setRes rF tid r) g c).acq l ι =
        (threadsRes (setRes rF tid r) c.threads.size).acq l ι + g.slotsRes.acq l ι := rfl
    refine mayWrite.take_fwd (by omega) (fun s hs => ?_) (fun h => ?_) h0
    · have := slotsRes_acq_le hs l ι; omega
    · have := ((E.updIds l).2 ι h).2; omega
  · obtain ⟨h1, h2⟩ := (E.updIds x).2 j hj
    refine ⟨by rw [takeGhost_length]; omega_t, ?_⟩
    rw [hacq]
    have hjι : ¬ (x = l ∧ j = ι) := fun h => by
      obtain ⟨rfl, rfl⟩ := h; omega
    have hjn : ¬ (x = l ∧ j = g.acqTab.length) := fun h => by omega_t
    rw [ite_f hjι, ite_f hjn]; exact h2

/-- **`TakeEraseLaw` holds.** -/
theorem takeEraseLaw : TakeEraseLaw I :=
  fun _ _ _ _ _ _ _ _ _ _ E hn hTt hι hT => E.take hn hTt hι hT

#print axioms Erase.take
#print axioms takeEraseLaw

end Kraken.Promising.SLR
