/-
Plans for the `EnvG` environment: validity and the resource algebra of a planned
release. ISA-neutral.

The plan itself (`Plan`, `Plan.Entry`, `rel`, `gives`, `give`, `keep`,
`after`, `afterRmw`) is in `EnvG/State.lean`, beside the state, because the
step outcomes (`EnvG/Facts.lean`) mention it.

- `Plan.Valid`: the static checks, decidable (`decide` on concrete locations;
  `simp` with disjointness hypotheses on symbolic ones). Each entry keeps a
  positive share of its own location: the location written is not among the
  ones given away (`WpPostR`'s written-location check and `hpos` of the
  release rules, §1d). The dynamic check of §3 (a release only on a store of
  effective kind `.rel`, `effRel`) is part of the store's `ok`
  (`EnvG/Env.lean`): it depends on the fence bits.
- `Plan.keep_op_give`: a release's split is exact,
  `(keep cl r).addW l p • give cl r = r.addW l p` (`eraseWPR_store_rel`'s
  `r'.op R = r.addW l (v, tw)`), for whole entries and for `Plan.Split`s
  (F1) alike.
- `Plan.keep_q_pos`/`Plan.after_q_pos`: a release keeps a positive share of
  its location. For whole releases (`Plan.Whole`: no split) the pre-F1
  equalities `Plan.keep_wr_self`/`Plan.after_q_self` hold.
-/
import Kraken.Promising.SLR.EnvG.State

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

/-- **Validity of a plan** (§1d): no entry gives away its own location. -/
def Plan.Valid (pl : Plan) : Prop := ∀ e ∈ pl.entries, e.loc ∉ e.gives

instance (pl : Plan) : Decidable pl.Valid := by unfold Plan.Valid; infer_instance

namespace Plan

theorem find?_loc {pl : Plan} {l : Loc} {v : Val} {e : Plan.Entry} (h : pl.find? l v = some e) :
    e ∈ pl.entries ∧ e.loc = l := by
  unfold find? at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨hm, hp.1⟩

/-- **A valid plan's release keeps its own location.** -/
theorem Valid.not_mem_gives {pl : Plan} (hv : pl.Valid) (l : Loc) (v : Val) : l ∉ pl.gives l v := by
  unfold gives
  cases h : pl.find? l v with
  | none => simp
  | some e =>
    obtain ⟨hm, hl⟩ := find?_loc h
    simp only [Option.map_some, Option.getD_some]
    exact hl ▸ hv e hm

@[simp] theorem rel_nil (l : Loc) (v : Val) : (⟨[]⟩ : Plan).rel l v = false := rfl

@[simp] theorem gives_nil (l : Loc) (v : Val) : (⟨[]⟩ : Plan).gives l v = [] := rfl

/-- The empty plan (no releases) is valid. -/
theorem valid_nil : (⟨[]⟩ : Plan).Valid := fun _ h => absurd h List.not_mem_nil

end Plan

/-! ## The resource algebra of a planned release -/

theorem Res.only_op_drop (L : List Loc) (r : Res) : (Res.drop L r).op (Res.only L r) = r := by
  apply Res.ext
  · funext x
    simp only [Res.op, Res.drop, Res.only]
    split
    · exact Perm.unit_op _
    · exact Perm.op_unit _
  · funext x ι
    simp only [Res.op, Res.drop, Res.only]
    split <;> omega

/-- `addW` at a location with no permission changes nothing. -/
theorem Res.addW_of_q_zero {r : Res} {x : Loc} (h : (r.wr x).q = 0) (p : Val × Time) : r.addW x p = r := by
  apply Res.ext
  · funext y
    simp only [Res.addW]
    split
    · next hy =>
      subst hy
      apply Perm.ext
      · rfl
      · funext p'; simp only [Perm.addW, h, Rat.lt_irrefl, false_and, or_false]
    · rfl
  · rfl

/-- The `none`-split of an entry is exact for a location outside `gives`. -/
theorem Plan.Entry.keep_op_give (e : Plan.Entry) {l : Loc} (he : e.loc = l) (hl : e.split = none → l ∉ e.gives)
    (cl : Prop) (r : Res) (p : Val × Time) : ((e.keep cl r).addW l p).op (e.give cl r) = r.addW l p := by
  unfold Plan.Entry.keep Plan.Entry.give
  cases hs : e.split with
  | none =>
    have hl := hl hs
    apply Res.ext
    · funext x
      simp only [Res.op, Res.drop, Res.only, Res.addW]
      by_cases hx : x = l
      · subst hx
        simp only [hl, ↓reduceIte]
        exact Perm.op_unit _
      · simp only [hx, ↓reduceIte]
        split
        · exact Perm.unit_op _
        · exact Perm.op_unit _
    · funext x ι
      simp only [Res.op, Res.drop, Res.only, Res.addW_acq]
      split <;> omega
  | some sp =>
    simp only
    subst he
    by_cases hq : 0 < (r.wr e.loc).q
    · rw [Res.addW_op _ _ (sp.pos cl r hq), sp.op_eq]
    · have h0 : (r.wr e.loc).q = 0 := by have := (r.wr e.loc).nonneg; grind
      have hk : ((sp.keep cl r).wr e.loc).q = 0 := by
        have e1 := congrArg (fun r => (r.wr e.loc).q) (sp.op_eq cl r)
        simp only [Res.op, Perm.op] at e1
        have := ((sp.keep cl r).wr e.loc).nonneg; have := ((sp.give cl r).wr e.loc).nonneg
        grind
      rw [Res.addW_of_q_zero hk, Res.addW_of_q_zero h0, sp.op_eq]

/-- **The split of a planned release is exact**: what the release keeps,
with the message added to its write set, composed with what it gives away,
is the resource with the message added (the location written is kept). -/
theorem Plan.keep_op_give (pl : Plan) {l : Loc} {v : Val} (hl : l ∉ pl.gives l v) (cl : Prop) (r : Res)
    (p : Val × Time) : ((pl.keep l v cl r).addW l p).op (pl.give l v cl r) = r.addW l p := by
  unfold Plan.keep Plan.give
  cases h : pl.find? l v with
  | none =>
    apply Res.ext
    · funext x
      simp only [Res.op, Res.drop, Res.only, Res.addW, List.not_mem_nil, ↓reduceIte]
      exact Perm.op_unit _
    · funext x ι
      simp only [Res.op, Res.drop, Res.only, Res.addW_acq, List.not_mem_nil, ↓reduceIte]
      omega
  | some e =>
    simp only
    have hg : pl.gives l v = e.gives := by unfold Plan.gives; rw [h]; rfl
    exact e.keep_op_give (Plan.find?_loc h).2 (fun _ => hg ▸ hl) cl r p

/-- **A planned release keeps a positive share of its own location.** -/
theorem Plan.keep_q_pos (pl : Plan) {l : Loc} {v : Val} (hl : l ∉ pl.gives l v) (cl : Prop) (r : Res)
    (hq : 0 < (r.wr l).q) : 0 < ((pl.keep l v cl r).wr l).q := by
  unfold Plan.keep
  cases h : pl.find? l v with
  | none => simpa [Res.drop] using hq
  | some e =>
    simp only [Plan.Entry.keep]
    have hg : pl.gives l v = e.gives := by unfold Plan.gives; rw [h]; rfl
    cases hs : e.split with
    | none => simpa [Res.drop, hg ▸ hl] using hq
    | some sp =>
      have he := (Plan.find?_loc h).2
      subst he
      exact sp.pos cl r hq

/-- The virtual resource after a store keeps a positive fraction of the
location written (of a valid plan). -/
theorem Plan.after_q_pos (pl : Plan) (hv : pl.Valid) (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res)
    (hq : 0 < (r.wr l).q) : 0 < ((pl.after l v tw cl r).wr l).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q]; exact pl.keep_q_pos (hv.not_mem_gives l v) cl r hq
  · rw [Res.addW_q]; exact hq

/-! ## Whole-location releases (no split)

A release of `v` to `l` is *whole* when its plan entry, if any, has no split:
it gives exactly `Res.only (pl.gives l v)` and keeps `Res.drop (pl.gives l v)`,
whatever the knowledge `cl`. Before splits, plans had only such entries; the
whole-entry equalities `keep_wr_self`/`after_q_self` hold for them. Release RMWs
are restricted to whole entries (`RmwOk`). -/

/-- **The planned release of `v` to `l`, if any, has no split.** -/
def Plan.Whole (pl : Plan) (l : Loc) (v : Val) : Prop := ∀ e ∈ pl.find? l v, e.split = none

/-- Every release of a plan without split entries is whole. -/
theorem Plan.Whole.of_entries {pl : Plan} (h : ∀ e ∈ pl.entries, e.split = none) (l : Loc) (v : Val) :
    pl.Whole l v := fun e he => h e (Plan.find?_loc (Option.mem_def.mp he)).1

/-- A whole release gives `Res.only (pl.gives l v)`. -/
theorem Plan.give_of_whole (pl : Plan) {l : Loc} {v : Val} (hs : pl.Whole l v) (cl : Prop) (r : Res) :
    pl.give l v cl r = Res.only (pl.gives l v) r := by
  unfold Plan.give Plan.gives
  cases h : pl.find? l v with
  | none => rfl
  | some e => simp only [Plan.Entry.give, hs e h, Option.map_some, Option.getD_some]

/-- A whole release keeps `Res.drop (pl.gives l v)`. -/
theorem Plan.keep_of_whole (pl : Plan) {l : Loc} {v : Val} (hs : pl.Whole l v) (cl : Prop) (r : Res) :
    pl.keep l v cl r = Res.drop (pl.gives l v) r := by
  unfold Plan.keep Plan.gives
  cases h : pl.find? l v with
  | none => rfl
  | some e => simp only [Plan.Entry.keep, hs e h, Option.map_some, Option.getD_some]

/-- The permission a planned whole release keeps at its own location. -/
theorem Plan.keep_wr_self (pl : Plan) {l : Loc} {v : Val} (hl : l ∉ pl.gives l v) (hs : pl.Whole l v)
    (cl : Prop) (r : Res) : (pl.keep l v cl r).wr l = r.wr l := by
  simp only [pl.keep_of_whole hs, Res.drop, hl, ↓reduceIte]

/-- The virtual resource after a store keeps the fraction of the location
written (of a valid plan, for a whole release). -/
theorem Plan.after_q_self (pl : Plan) (hv : pl.Valid) (l : Loc) (v : Val) (hs : pl.Whole l v) (tw : Time)
    (cl : Prop) (r : Res) : ((pl.after l v tw cl r).wr l).q = (r.wr l).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q, pl.keep_wr_self (hv.not_mem_gives l v) hs]
  · rw [Res.addW_q]

/-- Decidability smoke test: a concrete plan is checked by `decide`. -/
example : (⟨[{ loc := ⟨0x10, 4⟩, val := some 1, gives := [⟨0x20, 4⟩] }]⟩ : Plan).Valid := by decide

end Kraken.Promising.SLR.EnvG
