/-
Simulation library: timestamp-map helpers for the instances that renumber
memory ((A) general `PromisePure`, O11 non-temporal stores, B2 with
interleaved foreign appends).

- `TMap.extend` facts, stated generally: domain, values, floor below and above
  the new pair, and `Ext ρ (ρ.extend a a') m` for `m < a`.
- `MemRel.extend` / `MemRel.appendSource` / `MemRel.extendAppend`: a new
  source message mapped to an *arbitrary* target message above every image
  (`freshMap` is the case "both at the end of memory"; O11 maps an NT message
  to its later real position, B2 maps an own write past interleaved foreign
  messages).
- `ViewsLe.lift`, `CtxRel.lift`: the relation transported along any map
  extension `Ext ρ ρ' |M|` of a bounded source.
- `TMap.shiftAt p n`: the shift map that erases the source timestamp `p`
  from `[0, n]` (`s ↦ s` below `p`, `s ↦ s − 1` above, `p ∉ dom`), with its
  monotonicity, partiality and surjectivity lemmas (so there are no foreign
  target messages, `shiftAt_noForeign`) and its memory relation
  (`MemRel.shiftAt`).
-/
import Kraken.Promising.SLR.Sim.Rel

namespace Kraken.Promising

namespace Sim

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## `TMap.extend`, stated generally -/

namespace TMap

variable (ρ : TMap) {a a' : Time} (ha : ∀ s, ρ.dom s → s < a) (ha' : ∀ s, ρ.dom s → ρ.f s < a')

theorem extend_dom_iff (s : Time) : (ρ.extend a a' ha ha').dom s ↔ ρ.dom s ∨ s = a := Iff.rfl

theorem extend_dom_old {s : Time} (hs : ρ.dom s) : (ρ.extend a a' ha ha').dom s := .inl hs

theorem extend_dom_new : (ρ.extend a a' ha ha').dom a := .inr rfl

theorem extend_f_old {s : Time} (hs : ρ.dom s) : (ρ.extend a a' ha ha').f s = ρ.f s := by
  have := ha s hs
  show (if s = a then a' else ρ.f s) = ρ.f s
  rw [ite_eq_right (by omega_t)]

theorem extend_f_new : (ρ.extend a a' ha ha').f a = a' := by
  show (if a = a then a' else ρ.f a) = a'
  simp

theorem extend_fv_lt {v : View} (hv : v < a) : (ρ.extend a a' ha ha').fv v = ρ.fv v := by
  show (if a ≤ v then a' else ρ.fv v) = ρ.fv v
  rw [ite_eq_right (by omega_t)]

theorem extend_fv_ge {v : View} (hv : a ≤ v) : (ρ.extend a a' ha ha').fv v = a' := by
  show (if a ≤ v then a' else ρ.fv v) = a'
  rw [ite_eq_left hv]

/-- Agreement on the old domain. -/
theorem extend_agree (s : Time) (hs : ρ.dom s) :
    (ρ.extend a a' ha ha').dom s ∧ (ρ.extend a a' ha ha').f s = ρ.f s :=
  ⟨.inl hs, ρ.extend_f_old ha ha' hs⟩

/-- `extend` is an extension in the sense of `Ext`, below the new pair. -/
theorem extend_ext {m : Nat} (hm : m < a) : Ext ρ (ρ.extend a a' ha ha') m :=
  ⟨ρ.extend_agree ha ha', fun x hx => ρ.extend_fv_lt ha ha' (by omega_t)⟩

end TMap

/-- `freshMap` is `extend` at the ends of both memories. -/
theorem freshMap_eq {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') :
    freshMap ρ hm = ρ.extend (M.last + 1) (M'.last + 1) (fun s hs => Nat.lt_succ_of_le (hm.dom_le s hs))
      (fun s hs => Nat.lt_succ_of_le (hm.f_le s hs)) := rfl

theorem freshMap_ext {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') : Ext ρ (freshMap ρ hm) M.last :=
  ⟨freshMap_agree hm, fun _ hx => freshMap_fv hm hx⟩

/-! ## New source messages at arbitrary target positions -/

/-- Map a source message at `a` (above the domain) to a target message at `a'`
(above the image) with the same contents. -/
theorem MemRel.extend {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') {a a' : Time}
    (ha : ∀ s, ρ.dom s → s < a) (ha' : ∀ s, ρ.dom s → ρ.f s < a') (hal : a ≤ M.last) (hal' : a' ≤ M'.last)
    (hget : M'.get? a' = M.get? a) : MemRel (ρ.extend a a' ha ha') M M' where
  init := hm.init
  dom_le s hs := by
    rcases hs with hs | rfl
    · exact hm.dom_le s hs
    · exact hal
  f_le s hs := by
    rcases hs with hs | rfl
    · rw [ρ.extend_f_old ha ha' hs]; exact hm.f_le s hs
    · rw [ρ.extend_f_new ha ha']; exact hal'
  get s hs := by
    rcases hs with hs | rfl
    · rw [ρ.extend_f_old ha ha' hs]; exact hm.get s hs
    · rw [ρ.extend_f_new ha ha']; exact hget

/-- A source append keeps the memory relation (the domain is unchanged). -/
theorem MemRel.appendSource {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') (w : Msg) :
    MemRel ρ (M.append w).1 M' where
  init := hm.init
  dom_le s hs := by rw [Memory.last_append]; exact Nat.le_succ_of_le (hm.dom_le s hs)
  f_le := hm.f_le
  get s hs := by rw [Memory.get?_append_of_le _ _ _ (hm.dom_le s hs)]; exact hm.get s hs

/-- **Own write past foreign messages.** The source appends `w`; the target
already holds `w` at `a'`, above every image (for instance after foreign
appends and the thread's own write). The map extended by
`|M| + 1 ↦ a'` relates the new memories. `freshMap` is the case
`a' = |M'| + 1` with `M'` appended. -/
theorem MemRel.extendAppend {ρ : TMap} {M M' : Memory} (hm : MemRel ρ M M') (w : Msg) {a' : Time}
    (ha' : ∀ s, ρ.dom s → ρ.f s < a') (hal' : a' ≤ M'.last) (hget : M'.get? a' = some w) :
    MemRel (ρ.extend (M.last + 1) a' (fun s hs => Nat.lt_succ_of_le (hm.dom_le s hs)) ha') (M.append w).1 M' :=
  (hm.appendSource w).extend _ ha' (by rw [Memory.last_append]; exact Nat.le_refl _) hal'
    (by rw [Memory.get?_append_last]; exact hget)

/-! ## The relation along a map extension -/

/-- Views transport along an extension `Ext ρ ρ' m` when the source views are
bounded by `m` (`Views.Bnd`). -/
theorem ViewsLe.lift {ρ ρ' : TMap} {vs vs' : Views} {m : Nat} (h : ViewsLe ρ vs' vs) (hb : vs.Bnd m)
    (hext : Ext ρ ρ' m) : ViewsLe ρ' vs' vs := by
  have hl := hb.le
  have fv := fun {v} (hv : v ≤ m) => hext.2 v hv
  have ag := hext.1
  refine ⟨fun l => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun l => ?_, ?_⟩
  · rw [fv (hl.coh l)]; exact h.coh l
  · rw [fv hl.vrNew]; exact h.vrNew
  · rw [fv hl.vrOld]; exact h.vrOld
  · rw [fv hl.vrOldNR]; exact h.vrOldNR
  · rw [fv hl.vwNew]; exact h.vwNew
  · rw [fv hl.vwOld]; exact h.vwOld
  · rw [fv hl.vwOldNT]; exact h.vwOldNT
  · rw [fv hl.vCAP]; exact h.vCAP
  · rw [fv hl.vRel]; exact h.vRel
  · have h1 := h.fwd l
    cases e : vs.getFwd l with
    | none =>
      cases e' : vs'.getFwd l with
      | none => trivial
      | some _ => rw [e, e'] at h1; exact h1.elim
    | some a =>
      rw [e] at h1
      cases e' : vs'.getFwd l with
      | none => rw [e'] at h1; exact h1.elim
      | some b =>
        rw [e'] at h1
        obtain ⟨d, t, vw, x, xr⟩ := h1
        exact ⟨(ag _ d).1, by rw [(ag _ d).2]; exact t, by rw [fv (hl.fwd l a e)]; exact vw, x,
          by rw [fv (Nat.le_trans (Nat.min_le_right _ _) (hb.fwdTime l a e))]; exact xr⟩
  · have h1 := h.xclb
    cases e : vs.xclb with
    | none =>
      cases e' : vs'.xclb with
      | none => trivial
      | some _ => rw [e, e'] at h1; exact h1.elim
    | some p =>
      obtain ⟨t, ν, l⟩ := p
      rw [e] at h1
      cases e' : vs'.xclb with
      | none => rw [e'] at h1; exact h1.elim
      | some q =>
        obtain ⟨t', ν', l'⟩ := q
        rw [e'] at h1
        obtain ⟨d, h2, h3, h4⟩ := h1
        exact ⟨(ag _ d).1, by rw [(ag _ d).2]; exact h2, by rw [fv (hb.xclb t ν l e).2]; exact h3, h4⟩

/-- **Renumbering.** The context relation transports along any extension
`Ext ρ ρ' |M|` of the map, for a bounded source context whose promises are in
the domain, given the memory relation for the new map (`MemRel.extend`,
`MemRel.extendAppend`, `freshMap_mem`). -/
theorem CtxRel.lift {ρ ρ' : TMap} {c c' : Ctx} (hc : CtxRel ρ c c') (hb : c.Bnd) (hpd : ∀ s ∈ c.prom, ρ.dom s)
    (hext : Ext ρ ρ' c.mem.last) (hm : MemRel ρ' c.mem c'.mem) : CtxRel ρ' c c' := by
  refine ⟨hm, hc.views.lift hb.views hext, hc.prom.lift hext.1 hpd, ?_, ?_, hc.rmwWrote, hc.stores⟩
  · have key : ∀ (ys xs : List View), Rel2 (fun a' a => a' ≤ ρ.fv a) ys xs → (∀ ν ∈ xs, ν ≤ c.mem.last) →
        Rel2 (fun a' a => a' ≤ ρ'.fv a) ys xs := by
      intro ys xs h hb'
      induction h with
      | nil => exact .nil
      | @cons a b xs ys hab _ ih =>
        refine .cons ?_ (ih fun ν hν => hb' ν (List.mem_cons_of_mem _ hν))
        rw [hext.2 _ (hb' b List.mem_cons_self)]; exact hab
    exact key _ _ hc.loadViews hb.loadViews
  · rw [hext.2 _ hb.succView]; exact hc.succView

/-! ## The shift map: erasing one source timestamp

`shiftAt p n` is the map of (A) general `PromisePure`: the source memory has
`n` messages, the target is the source without the message at `p` (the
thread's erased promise). It is partial (`p ∉ dom`), strictly monotone, and
onto `[0, n − 1]`: every target timestamp is an image, so there are no foreign
target messages (`shiftAt_noForeign`). -/

namespace TMap

/-- The shift map erasing `p ≥ 1` from `[0, n]`: `s ↦ s` below `p`,
`s ↦ s − 1` above, floored at `n`. -/
def shiftAt (p n : Time) (hp : 0 < p) : TMap where
  dom s := s ≤ n ∧ s ≠ p
  f s := if s < p then s else s - 1
  fv v := if min v n < p then min v n else min v n - 1
  dom0 := ⟨Nat.zero_le _, by omega_t⟩
  f0 := by simp [hp]
  strict a b ha hb hab := by
    obtain ⟨-, ha⟩ := ha; obtain ⟨-, hb⟩ := hb
    show (if a < p then a else a - 1) < (if b < p then b else b - 1)
    split <;> split <;> omega_t
  fv_dom a ha := by
    show (if min a n < p then min a n else min a n - 1) = (if a < p then a else a - 1)
    rw [Nat.min_eq_left ha.1]
  fv_mono a b hab := by
    show (if min a n < p then min a n else min a n - 1) ≤ (if min b n < p then min b n else min b n - 1)
    have : min a n ≤ min b n := by omega_t
    split <;> split <;> omega_t
  fv_floor v := by
    by_cases hv : min v n = p
    · refine ⟨p - 1, ⟨by omega_t, by omega_t⟩, by omega_t, ?_⟩
      show (if min v n < p then min v n else min v n - 1) = (if p - 1 < p then p - 1 else p - 1 - 1)
      rw [ite_eq_right (by omega_t), ite_eq_left (by omega_t), hv]
    · exact ⟨min v n, ⟨Nat.min_le_right _ _, hv⟩, Nat.min_le_left _ _, by
        show (if min v n < p then min v n else min v n - 1) = (if min v n < p then min v n else min v n - 1)
        rfl⟩

variable {p n : Time} {hp : 0 < p}

theorem shiftAt_dom_iff (s : Time) : (shiftAt p n hp).dom s ↔ s ≤ n ∧ s ≠ p := Iff.rfl

/-- **Partiality.** The erased timestamp is outside the domain. -/
theorem shiftAt_not_dom : ¬ (shiftAt p n hp).dom p := fun h => h.2 rfl

theorem shiftAt_f_lt {s : Time} (hs : s < p) : (shiftAt p n hp).f s = s := ite_eq_left hs

theorem shiftAt_f_gt {s : Time} (hs : p < s) : (shiftAt p n hp).f s = s - 1 := ite_eq_right (by omega_t)

theorem shiftAt_fv_lt {v : View} (hv : v < p) (hvn : v ≤ n) : (shiftAt p n hp).fv v = v := by
  show (if min v n < p then min v n else min v n - 1) = v
  rw [Nat.min_eq_left hvn, ite_eq_left hv]

theorem shiftAt_fv_ge {v : View} (hv : p ≤ v) (hvn : v ≤ n) : (shiftAt p n hp).fv v = v - 1 := by
  show (if min v n < p then min v n else min v n - 1) = v - 1
  rw [Nat.min_eq_left hvn, ite_eq_right (by omega_t)]

/-- The shift never raises a view. -/
theorem shiftAt_fv_le (v : View) : (shiftAt p n hp).fv v ≤ v := by
  show (if min v n < p then min v n else min v n - 1) ≤ v
  split <;> omega_t

/-- **Monotonicity** (on the domain, strict). -/
theorem shiftAt_f_lt_f {a b : Time} (ha : (shiftAt p n hp).dom a) (hb : (shiftAt p n hp).dom b) (hab : a < b) :
    (shiftAt p n hp).f a < (shiftAt p n hp).f b :=
  (shiftAt p n hp).strict a b ha hb hab

/-- **Onto** `[0, n − 1]`: `s'` below `p` is the image of itself, `s' ≥ p`
of `s' + 1`. -/
theorem shiftAt_surj {s' : Time} (hs' : s' < n) :
    ∃ s, (shiftAt p n hp).dom s ∧ (shiftAt p n hp).f s = s' := by
  by_cases h : s' < p
  · exact ⟨s', ⟨by omega_t, by omega_t⟩, shiftAt_f_lt h⟩
  · exact ⟨s' + 1, ⟨by omega_t, by omega_t⟩, by rw [shiftAt_f_gt (by omega_t)]; rfl⟩

/-- The preimage of a target timestamp. -/
theorem shiftAt_f_eq_iff {s s' : Time} (hs : s ≠ p) :
    (shiftAt p n hp).f s = s' ↔ (s < p ∧ s = s') ∨ (p < s ∧ s = s' + 1) := by
  show (if s < p then s else s - 1) = s' ↔ _
  split <;> omega_t

end TMap

/-- Under the shift map no target message is foreign, when the target has
fewer than `n` messages. -/
theorem shiftAt_noForeign {p n : Time} (hp : 0 < p) {M' : Memory} (hM' : M'.last < n) :
    NoForeign (TMap.shiftAt p n hp) M' :=
  fun _ _ h2 => TMap.shiftAt_surj (Nat.lt_of_le_of_lt h2 hM')

/-- The memory relation of the shift map, from its pointwise content: the
target is the source with the message at `p` removed (one message shorter,
the same initial state, every message above `p` shifted down by one). -/
theorem MemRel.shiftAt {p : Time} (hp : 0 < p) {M M' : Memory} (hinit : M'.init = M.init)
    (hlast : M'.last + 1 = M.last) (hpl : p ≤ M.last)
    (hlo : ∀ s, s < p → M'.get? s = M.get? s) (hhi : ∀ s, p < s → M'.get? (s - 1) = M.get? s) :
    MemRel (TMap.shiftAt p M.last hp) M M' where
  init := hinit
  dom_le _ hs := hs.1
  f_le s hs := by
    obtain ⟨h1, h2⟩ := hs
    show (if s < p then s else s - 1) ≤ M'.last
    split <;> omega_t
  get s hs := by
    by_cases h : s < p
    · rw [TMap.shiftAt_f_lt h]; exact hlo s h
    · have : p < s := by have : s ≠ p := hs.2; omega_t
      rw [TMap.shiftAt_f_gt this]; exact hhi s this

end Sim

end Kraken.Promising
