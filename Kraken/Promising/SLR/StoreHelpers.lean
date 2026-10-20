/-
ISA-neutral helpers for store and load cells of the spinlock workers,
restated from `SLR/SwpStore.lean` (which imports the AArch64 syntax,
so the x64 cells cannot import it). Same statements and proofs; the AArch64
file can switch to these.

- `erase_inj`, `writeSuccs_tw`, `writtenCx_writeEv`: a plain store's write
  event (its timestamp, `WriteOk`, `vwOld`; the only message it writes);
- `storeGhost_plain`, `setWidth_ofNat_32`;
- `fulf_read?`, `read_max`: a read under a full permission returns the
  holder's maximal write; `read_max_gen` (the full permission anywhere in
  the total, no one else may write) and `read_max_slot` (held by a slot
  whose acquire id the reader holds) generalise it;
- `sub_acq_le`, `canAcq_inv`, `total_max_of_slot`, `not_mayWrite_of_slot`:
  slot facts behind `read_max_slot`.
-/
import Kraken.Promising.SLR.RuleShapes
import Kraken.Promising.SLR.SwpSpec

namespace Kraken.Promising.SLR

open Kraken Kraken.Promising

variable {I : ISA}

/-- Erasing two members of a duplicate-free list gives the same list only
for the same member. -/
theorem erase_inj {l : List Nat} {a b : Nat} (hn : l.Nodup) (hb : b ∈ l) (h : l.erase a = l.erase b) :
    a = b := by
  refine Classical.byContradiction fun hne => ?_
  have hb' : b ∈ l.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  rw [h] at hb'
  exact ((List.Nodup.mem_erase_iff hn).mp hb').1 rfl

/-- **The timestamp of a plain store's write event**: `WriteOk` holds at it
and the new `vwOld` takes it (for a non-NT store). -/
theorem writeSuccs_tw {A : Arch} {tid : Nat} {iv : InstrViews} {cx cx' : Ctx} {k : StoreKind} {l : Loc}
    {v : Val} {extra : View} {tw : Time} (hn : cx.prom.Nodup)
    (hc : cx' ∈ writeSuccs A tid iv cx k false l v none extra) (hev : WriteEv tid cx cx' l v none tw) :
    WriteOk A tid iv cx k l none extra tw ∧
      cx'.views.vwOld = if A.storeKind k == .nt then cx.views.vwOld else max cx.views.vwOld tw := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, ht, w, hw, -, -, -, hok, rfl⟩ | ⟨hok, rfl⟩
  · rcases hev.cases with ⟨-, htw, -⟩ | ⟨hm, -⟩
    · have hp := hev.prom
      obtain rfl : t = tw := erase_inj hn htw hp
      exact ⟨hok, rfl⟩
    · exfalso
      have := congrArg Memory.last hm
      simp only [afterWrite, Memory.last_append] at this
      exact Nat.succ_ne_self _ this.symm
  · rcases hev.cases with ⟨hm, -, -⟩ | ⟨-, rfl⟩
    · exfalso
      have := congrArg Memory.last hm
      simp only [afterWrite, Memory.last_append] at this
      exact Nat.succ_ne_self _ this
    · exact ⟨hok, rfl⟩

/-- The only message a write event writes is its own. -/
theorem writtenCx_writeEv {c : Config I} {t : Thread I} {tid : Nat} {cx' : Ctx} {l : Loc} {v : Val}
    {tr : Option Time} {tw : Time} {w : Msg} (hev : WriteEv tid (ctx₀ t tid c.mem) cx' l v tr tw)
    (hw : WrittenCx c t cx' w) : w = ⟨l, v, tid⟩ := by
  obtain ⟨ts, hget, hnp, hnew⟩ := hw
  have hts : ts = tw := by
    rcases hnew with hlt | hpr
    · rcases hev.cases with ⟨hm, -, -⟩ | ⟨hm, rfl⟩
      · rw [hm] at hget
        exact absurd (Memory.last_le_of_get?_eq_some _ hget) (Nat.not_le.mpr hlt)
      · have := Memory.last_le_of_get?_eq_some _ hget
        rw [hm, Memory.last_append] at this
        exact Nat.le_antisymm this hlt
    · refine Classical.byContradiction fun hne => hnp ?_
      rw [hev.prom]
      exact (List.mem_erase_of_ne hne).mpr hpr
  subst hts
  rcases hev.cases with ⟨hm, -, hg⟩ | ⟨hm, rfl⟩
  · rw [hm] at hget
    exact Option.some.inj (hget.symm.trans hg)
  · rw [hm, Memory.get?_append_last] at hget
    exact (Option.some.inj hget).symm

/-- A store without slots in non-release mode leaves the ghost state as is. -/
theorem storeGhost_plain (g : Ghost) (x : Loc) (tw : Time) : storeGhost g x tw false [] = g := by
  cases g; simp [storeGhost]

theorem setWidth_ofNat_32 {n : Nat} (h : n < 2 ^ 32) :
    BitVec.setWidth 128 (BitVec.ofNat 32 n) = BitVec.ofNat 128 n := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 2 ^ 32 < 2 ^ 128))]

/-- A settled pair is what memory reads at its timestamp. -/
theorem fulf_read? {c : Config I} {g : Ghost} {x : Loc} {p : Val × Time} (h : Fulf c g x p) :
    c.mem.read? x p.2 = some p.1 := by
  rcases h with ⟨h0, h1⟩ | ⟨w, hw, hl, hv, -⟩
  · simp [Memory.read?, h0, h1]
  · have h0 : p.2 ≠ 0 := fun h => by rw [h] at hw; simp [Memory.get?] at hw
    simp [Memory.read?, h0, hw, hl, hv]

/-- A sub-resource holds at most the acquire ids of the larger one. -/
theorem sub_acq_le {a b : Res} (h : a.Sub b) (x : Loc) (ι : PredId) : a.acq x ι ≤ b.acq x ι := by
  obtain ⟨d, rfl⟩ := h
  show a.acq x ι ≤ a.acq x ι + d.acq x ι
  omega

/-- **Inversion of `CanAcq`**: a slot is acquirable through an acquire id
held directly, an update id, or an acquire id held by some slot. -/
theorem canAcq_inv {u : List Slot} {U : Loc → List PredId} {A : Loc → PredId → Nat} {k : Key} {ι : PredId}
    (h : CanAcq u U A k ι) : 1 ≤ A k.1 ι ∨ ι ∈ U k.1 ∨ ∃ s ∈ u, 1 ≤ s.res.acq k.1 ι := by
  cases h with
  | base _ ha => exact .inl ha
  | upd _ hu => exact .inr (.inl hu)
  | step _ hs _ ha => exact .inr (.inr ⟨_, hs, ha⟩)

section Slot

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- A slot with all of `x` and maximal write `(v0, ts)` gives the total's
maximal write of `x`. -/
theorem total_max_of_slot (E : Erase rF g T c) {s : Slot} (hs : s ∈ g.u) {x : Loc}
    (hq : (s.res.wr x).q = 1) {v0 : Val} {ts : Time} (hX : (s.res.wr x).X (v0, ts))
    (hmax : ∀ p, (s.res.wr x).X p → p.2 ≤ ts) :
    0 < ((total rF g c).wr x).q ∧ ((total rF g c).wr x).X (v0, ts) ∧
      ∀ p, ((total rF g c).wr x).X p → p.2 ≤ ts := by
  refine ⟨?_, (sub_total_slot hs).X hX, fun p hp => ?_⟩
  · have := (sub_total_slot (rF := rF) (c := c) hs).q_le x
    rw [hq] at this
    grind
  · rcases X_total_cases hp with ⟨i, hi, hXi⟩ | ⟨s', hs', hXs'⟩
    · exact absurd hXi (((rF i).wr x).zero (E.unique_holder_slot hs hq i hi) p)
    · by_cases he : s' = s
      · subst he; exact hmax p hXs'
      · have h2 := E.q_add_le_one_slots hs hs' he x
        rw [hq] at h2
        exact absurd hXs' ((s'.res.wr x).zero (by have := (s'.res.wr x).nonneg; grind) p)

/-- **A thread holding all of `x` holds the total's maximal write** (clean
erasure): `total_max_of_slot` for a thread. -/
theorem total_max_of_thread (E : Erase rF g T c) {j : Nat} (hj : j < c.threads.size) {x : Loc}
    (hq : ((rF j).wr x).q = 1) {v0 : Val} {ts : Time} (hX : ((rF j).wr x).X (v0, ts))
    (hmax : ∀ p, ((rF j).wr x).X p → p.2 ≤ ts) :
    0 < ((total rF g c).wr x).q ∧ ((total rF g c).wr x).X (v0, ts) ∧
      ∀ p, ((total rF g c).wr x).X p → p.2 ≤ ts := by
  obtain ⟨hth, hsl⟩ := E.unique_holder hj hq
  refine ⟨?_, (sub_total_thread hj).X hX, fun p hp => ?_⟩
  · have := (sub_total_thread (rF := rF) (g := g) hj).q_le x
    rw [hq] at this
    grind
  · rcases X_total_cases hp with ⟨i, hi, hXi⟩ | ⟨s, hs, hXs⟩
    · by_cases hij : i = j
      · subst hij; exact hmax p hXi
      · exact (((rF i).wr x).zero (hth i hi hij) _ hXi).elim
    · exact ((s.res.wr x).zero (hsl s hs) _ hXs).elim

/-- **Only the holder of `ι` may write `x`** when the slot of `ι` holds all
of `x`: thread `tid` holds `ι` once, so no other thread and no slot holds it,
and it is not an update id. -/
theorem not_mayWrite_of_slot (E : Erase rF g T c) {s : Slot} (hs : s ∈ g.u) {x : Loc}
    (hq : (s.res.wr x).q = 1) {tid : Nat} (htid : tid < c.threads.size) (hacq : (rF tid).acq s.key.1 s.id = 1)
    {i : Nat} (hi : i < c.threads.size) (hit : i ≠ tid) : ¬ mayWrite (rF i) g x := by
  have hval := E.valid
  rintro (hpos | ⟨s', hs', hca, hpos⟩)
  · rw [E.unique_holder_slot hs hq i hi] at hpos; exact Rat.lt_irrefl hpos
  · by_cases he : s' = s
    · subst he
      rcases canAcq_inv hca with h | h | ⟨s'', hs'', h⟩
      · have := sub_acq_le (sub_total_pair (rF := rF) (g := g) hi htid hit) s'.key.1 s'.id
        have := hval.2 s'.key.1 s'.id
        change 1 ≤ (rF i).acq s'.key.1 s'.id at h
        simp only [Res.op] at *
        omega
      · have h0 := ((E.updIds s'.key.1).2 _ h).2
        have := sub_acq_le (sub_total_thread (g := g) (rF := rF) htid) s'.key.1 s'.id
        omega
      · have := sub_acq_le (sub_total_thread_slot (rF := rF) (g := g) htid hs'') s'.key.1 s'.id
        have := hval.2 s'.key.1 s'.id
        simp only [Res.op] at *
        omega
    · have h2 := E.q_add_le_one_slots hs hs' he x
      rw [hq] at h2
      have := (s'.res.wr x).nonneg
      grind

/-- **A read under a full permission held anywhere** (clean erasure): the
total write set of `x` has the maximum `(v0, ts)`, no thread other than
`tid` may write `x`, and thread `tid` reads `x` at `tr` (not its own promise)
with no write to `x` in `(tr, B]`, `ts ≤ B`. Then it reads `(v0, ts)`. -/
theorem read_max_gen (E : Erase rF g (fun _ => False) c) {tid : Nat} {t : Thread I}
    (ht : c.threads[tid]? = some t) {x : Loc} (hq : 0 < ((total rF g c).wr x).q) {v0 val : Val}
    {ts tr B : Time} (hX : ((total rF g c).wr x).X (v0, ts))
    (hmax : ∀ p, ((total rF g c).wr x).X p → p.2 ≤ ts)
    (hmw : ∀ i t', i ≠ tid → c.threads[i]? = some t' → ¬ mayWrite (rF i) g x)
    (hrd : c.mem.read? x tr = some val) (hnp : t.prom.contains tr = false)
    (hwi : c.mem.writeIn x tr B = false) (hB : ts ≤ B) : tr = ts ∧ val = v0 := by
  have htr : Tracked c g (total rF g c) x := .inl hq
  have hF0 := (E.writes x htr _).mp hX
  have hr0 := fulf_read? hF0
  have hle : ts ≤ tr := by
    refine Nat.le_of_not_lt fun hlt => ?_
    rcases hF0 with ⟨h0, -⟩ | ⟨w, hw, hl, -, -⟩
    · simp only at h0; rw [h0] at hlt; exact Nat.not_lt_zero _ hlt
    · have := (Memory.writeIn_iff _ _ _ _).mpr ⟨ts, w, hlt, hB, hw, hl⟩
      rw [hwi] at this; cases this
  have hge : tr ≤ ts := by
    refine Nat.le_of_not_lt fun hlt => ?_
    have htr0 : tr ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le ts) hlt)
    obtain ⟨w, hw, hl, hv⟩ : ∃ w, c.mem.get? tr = some w ∧ w.loc = x ∧ w.val = val := by
      simp only [Memory.read?, htr0, ↓reduceIte] at hrd
      split at hrd
      · next w hw =>
        by_cases hl : w.loc = x
        · simp only [hl, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hrd
          exact ⟨w, hw, hl, hrd⟩
        · simp [hl] at hrd
      · cases hrd
    by_cases hs : Settled c g tr
    · have hXr := (E.writes x htr (val, tr)).mpr (.inr ⟨w, hw, hl, hv, hs⟩)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (hmax _ hXr))
    · simp only [Settled, not_or, Classical.not_not] at hs
      obtain ⟨⟨i, t', hi, hpr⟩, hnpd⟩ := hs
      by_cases hit : i = tid
      · subst hit; rw [ht] at hi; cases hi; simp [hpr] at hnp
      · have hmw' := E.promValid i t' hi (fun h => h) tr hpr hnpd w hw
        rw [hl] at hmw'
        exact hmw i t' hit hi hmw'
  obtain rfl := Nat.le_antisymm hge hle
  exact ⟨rfl, Option.some.inj (hrd.symm.trans hr0)⟩

/-- **A read under a full permission held by a slot** (clean erasure): the
slot `s` holds all of `x`, with maximal write `(v0, ts)`, and thread `tid`
holds the slot's acquire id once. No one else may write `x`
(`not_mayWrite_of_slot`), so a read of `x` by `tid` at `tr` (not its own
promise) with no write to `x` in `(tr, B]`, `ts ≤ B`, returns `(v0, ts)`. -/
theorem read_max_slot (E : Erase rF g (fun _ => False) c) {tid : Nat} {t : Thread I}
    (ht : c.threads[tid]? = some t) {s : Slot} (hs : s ∈ g.u) {x : Loc} (hq : (s.res.wr x).q = 1)
    (hacq : (rF tid).acq s.key.1 s.id = 1) {v0 val : Val} {ts tr B : Time}
    (hX : (s.res.wr x).X (v0, ts)) (hmax : ∀ p, (s.res.wr x).X p → p.2 ≤ ts)
    (hrd : c.mem.read? x tr = some val) (hnp : t.prom.contains tr = false)
    (hwi : c.mem.writeIn x tr B = false) (hB : ts ≤ B) : tr = ts ∧ val = v0 := by
  obtain ⟨hqT, hXT, hmaxT⟩ := total_max_of_slot E hs hq hX hmax
  exact read_max_gen E ht hqT hXT hmaxT
    (fun i _ hit hi => not_mayWrite_of_slot E hs hq (lt_size_of_get? ht) hacq (lt_size_of_get? hi) hit)
    hrd hnp hwi hB

end Slot

/-- **A read under a full permission of the reader** (clean erasure, `T = ⊥`): thread
`tid` holds all of `x`, whose write set has the maximum `(v0, ts)`, and reads
`x` at `tr` (not its own promise) with no write to `x` in `(tr, B]`, `ts ≤ B`.
Then it reads `(v0, ts)`: a later message of `x` would be settled (in the
holder's write set, so `≤ ts`) or an outstanding promise of another thread
(which may not write `x`), and `(v0, ts)` itself is a write of `x`. The
corollary of `read_max_gen` for a full permission held by the reader. -/
theorem read_max {rF : Nat → Res} {g : Ghost} {c : Config I} {tid : Nat} {t : Thread I} {r : Res} {x : Loc}
    {v0 val : Val} {ts tr B : Time} (E : Erase (setRes rF tid r) g (fun _ => False) c)
    (ht : c.threads[tid]? = some t) (hq : (r.wr x).q = 1) (hX : (r.wr x).X (v0, ts))
    (hmax : ∀ p, (r.wr x).X p → p.2 ≤ ts) (hrd : c.mem.read? x tr = some val) (hnp : t.prom.contains tr = false)
    (hwi : c.mem.writeIn x tr B = false) (hB : ts ≤ B) : tr = ts ∧ val = v0 := by
  have hn := lt_size_of_get? ht
  have hq' : ((setRes rF tid r tid).wr x).q = 1 := by rw [setRes_self]; exact hq
  obtain ⟨hth, hsl⟩ := E.unique_holder hn hq'
  obtain ⟨d, hd⟩ := sub_total_thread (rF := setRes rF tid r) (g := g) hn
  refine read_max_gen E ht ?_ ?_ ?_ ?_ hrd hnp hwi hB
  · rw [hd]; show 0 < ((setRes rF tid r tid).wr x).q + (d.wr x).q
    rw [hq']; have := (d.wr x).nonneg; grind
  · rw [hd]; exact Or.inl (by rw [setRes_self]; exact hX)
  · intro p hp
    rcases X_total_cases hp with ⟨j, hj, hXj⟩ | ⟨s, hs', hXs⟩
    · by_cases hjt : j = tid
      · subst hjt; rw [setRes_self] at hXj; exact hmax _ hXj
      · exact (((setRes rF tid r j).wr x).zero (hth j hj hjt) _ hXj).elim
    · exact ((s.res.wr x).zero (hsl s hs') _ hXs).elim
  · intro i t' hit hi hmw
    rcases hmw with hpos | ⟨s', hs', -, hpos⟩
    · rw [hth i (lt_size_of_get? hi) hit] at hpos; exact Rat.lt_irrefl hpos
    · rw [hsl s' hs'] at hpos; exact Rat.lt_irrefl hpos

end Kraken.Promising.SLR
