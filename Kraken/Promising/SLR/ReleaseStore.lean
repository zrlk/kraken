/-
ISA-neutral facts for a **release store's** `WpPostR` obligations
(`SLR/NPSafeInvR.lean`), at the non-pending branch of
`EvTree.eraseWPR_store_rel` (`SLR/RuleShapes.lean`): the thread splits
`r ⊎ {(v, tw)}` into `r' ⋅ R`, `R` goes to the message's slots `ss`.

- `mayWrite_release`: `mayWrite` after the store is covered by `mayWrite`
  before (`WpPostR`'s `acqLe` conjunct), when the slots carry no acquire ids
  and are on a message newer than every existing slot (`Erase.slot_key_le`).
- `writtenCx_fresh`: a store that appends a fresh message writes only that
  message (`WpPostR`'s ownership conjunct).
- `Erase.fresh_of_impure`: a write that fulfils an outstanding non-pending
  promise writes a value at which the release predicate is pure (`Erase.pure`
  through `relSettled`), so at an impure value the write is a fresh append.
-/
import Kraken.Promising.SLR.RuleShapes
import Kraken.Promising.Conservative

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

theorem read?_of_get?' {m : Memory} {ts : Time} {w : Msg} (hw : m.get? ts = some w) :
    m.read? w.loc ts = some w.val := by
  have h0 : ts ≠ 0 := by rintro rfl; rw [m.get?_zero] at hw; cases hw
  unfold Memory.read?
  rw [ite_eq_right h0, hw]
  simp

/-! ## Acquirability with fresh slots that carry no acquire ids -/

/-- A component's acquire ids are below the product's. -/
theorem acq_le_prod_slots {L : List Slot} {s : Slot} (hs : s ∈ L) (y : Loc) (ι : PredId) :
    s.res.acq y ι ≤ (Res.prod (L.map (·.res))).acq y ι := by
  induction L with
  | nil => cases hs
  | cons s' L ih =>
    simp only [List.map_cons, Res.prod_cons, Res.op]
    rcases List.mem_cons.mp hs with rfl | hs
    · omega
    · have := ih hs; omega

/-- Adding slots that carry no acquire ids, on keys distinct from the old
slots', makes nothing new acquirable but the new slots themselves. -/
theorem canAcq_append {u ss : List Slot} {U : Loc → List PredId} {A : Loc → PredId → Nat}
    (h0 : ∀ s ∈ ss, ∀ y ι, s.res.acq y ι = 0) (hdisj : ∀ s ∈ u, ∀ s' ∈ ss, s.key ≠ s'.key)
    {k : Key} {ι : PredId} (h : CanAcq (u ++ ss) U A k ι) : CanAcq u U A k ι ∨ ∃ s ∈ ss, s.key = k := by
  induction h with
  | base hs ha =>
    rcases List.mem_append.mp hs with hs | hs
    · exact .inl (.base hs ha)
    · exact .inr ⟨_, hs, rfl⟩
  | upd hs hu =>
    rcases List.mem_append.mp hs with hs | hs
    · exact .inl (.upd hs hu)
    · exact .inr ⟨_, hs, rfl⟩
  | @step s s' _ hs hs' ha ih =>
    rcases List.mem_append.mp hs with hs | hs
    · rcases ih with ih | ⟨s0, hs0, hk⟩
      · rcases List.mem_append.mp hs' with hs' | hs'
        · exact .inl (.step ih hs hs' ha)
        · exact .inr ⟨s', hs', rfl⟩
      · exact absurd hk.symm (hdisj s hs s0 hs0)
    · rw [h0 s hs] at ha; exact absurd ha (by decide)

/-- **`acqLe` for a release store**: the thread keeps `r'`, gives `R` (no
acquire ids) to the slots `ss`, all on keys distinct from the existing
slots'. -/
theorem mayWrite_release {g : Ghost} {r r' R : Res} {x : Loc} {tw : Time} {p : Val × Time} {ss : List Slot}
    (hres : r'.op R = r.addW x p) (hprod : Res.prod (ss.map (·.res)) = R) (hR : ∀ y ι, R.acq y ι = 0)
    (hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key) {y : Loc}
    (h : mayWrite r' (storeGhost g x tw true ss) y) : mayWrite r g y := by
  have hq : ∀ z, (r'.wr z).q + (R.wr z).q = (r.wr z).q := by
    intro z
    have := congrArg (fun ρ => (ρ.wr z).q) hres
    simpa [Res.op, Perm.op] using this
  have hacq : r'.acq = r.acq := by
    funext z ι
    have := congrArg (fun ρ => ρ.acq z ι) hres
    simp only [Res.op, Res.addW_acq, hR z ι, Nat.add_zero] at this
    exact this
  have h0 : ∀ s ∈ ss, ∀ y ι, s.res.acq y ι = 0 := by
    intro s hs y ι
    have := acq_le_prod_slots hs y ι
    rw [hprod, hR] at this
    omega
  rcases h with h | ⟨s, hs, hc, hpos⟩
  · have := hq y; have := (R.wr y).nonneg
    exact .inl (by grind)
  · rcases mem_store_u.mp hs with hs | hs
    · rcases canAcq_append h0 hdisj hc with hc | ⟨s0, hs0, hk⟩
      · rw [hacq] at hc
        exact .inr ⟨s, hs, hc, hpos⟩
      · exact absurd hk.symm (hdisj s hs s0 hs0)
    · have h1 : 0 < (R.wr y).q := by
        rw [← hprod]
        exact Res.pos_prod_of_mem (List.mem_map_of_mem hs) hpos
      have := hq y; have := (r'.wr y).nonneg
      exact .inl (by grind)

/-- Every existing slot is on a message in memory. -/
theorem Erase.slot_key_le {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {s : Slot} (hs : s ∈ g.u) : s.key.2 ≤ c.mem.last := by
  obtain ⟨hrel, -⟩ := (E.slotsDom s.key s.id).mp ⟨s, hs, rfl, rfl⟩
  obtain ⟨v, hv⟩ := E.relExists _ hrel
  exact read?_le_last' hv

/-! ## Fresh appends -/

/-- **A write at a value where the release predicate is impure is a fresh
append**: a fulfilled outstanding promise that is not pending is not settled,
hence relaxed (`relSettled`), hence pure (`Erase.pure`). -/
theorem Erase.fresh_of_impure {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat}
    {t : Thread I} (E : Erase rF g T c) (ht : c.threads[tid]? = some t) {cx cx' : Ctx} (hcx : cx.prom = t.prom)
    (hm : cx.mem = c.mem) {l : Loc} {v : Val} {trOpt : Option Time} {tw : Time}
    (hev : WriteEv tid cx cx' l v trOpt tw) (hpd : tw ∉ g.pend) (himp : ¬ Pred.Pure (g.rel l) v) :
    cx'.mem = (c.mem.append ⟨l, v, tid⟩).1 ∧ tw = c.mem.last + 1 := by
  rcases hev.cases with ⟨-, hp, hget⟩ | ⟨h1, h2⟩
  · exfalso
    rw [hcx] at hp
    rw [hm] at hget
    have hout : Outstanding c tw := ⟨tid, t, ht, hp⟩
    have hnrel : (l, tw) ∉ g.relMsgs := by
      intro hk
      rcases E.relSettled _ hk with h | h
      · exact h hout
      · exact hpd h
    exact himp (E.pure l tw v (read?_of_get?' hget) hnrel)
  · rw [hm] at h1 h2
    exact ⟨h1, h2⟩

/-- **A fresh append writes only the new message**: `WrittenCx` of a store
that appended `⟨l, v, tid⟩` at `|M| + 1` (context starting from the thread's
promises and `c`'s memory) is that message. -/
theorem writtenCx_fresh {c : Config I} {t : Thread I} {tid : Nat} {cx cx' : Ctx} (hcx : cx.prom = t.prom) {l : Loc} {v : Val}
    {trOpt : Option Time} {tw : Time} (hev : WriteEv tid cx cx' l v trOpt tw)
    (hm' : cx'.mem = (c.mem.append ⟨l, v, tid⟩).1) (htw : tw = c.mem.last + 1) {w : Msg}
    (hw : WrittenCx c t cx' w) : w.loc = l := by
  obtain ⟨ts, hget, hnp, hnew⟩ := hw
  rw [hm'] at hget
  rcases Memory.get?_append_eq_some _ _ hget with ⟨hle, hget'⟩ | ⟨-, rfl⟩
  · rcases hnew with hlt | hp
    · omega_t
    · exfalso
      apply hnp
      rw [hev.prom, hcx]
      refine (List.mem_erase_of_ne ?_).mpr hp
      omega_t
  · rfl

end Kraken.Promising.SLR
