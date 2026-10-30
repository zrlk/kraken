/-
**The memory relation with outstanding promises, one thread** (`Scc/DESIGN.md`
§9.0, with (e) and (f′)).

`MemRel` with the per-location timestamp order of `Components.ts_mono` (e)
in place of the global one, and the thread's outstanding target promises
split by a mirroring policy into the ones mirrored in the source (`tp`,
mirrored by the source promises `sp`) and the ones that are not (`tq`). A
source message's image is a mirrored target promise exactly when the
message is a source promise (`prom_corr`); an unmirrored promise has no
image and is exempt from `mem_onto`. The policy is the caller's: no
mirroring (`tp = []`, the one-thread case), mirroring all (`tq = []`), or
any split in between.

- `MemRelP`, `MemRelP.of_memRel` (no promises);
- `MemRelP.ts_le_last`, `MemRelP.lt_of_ts`: every image exists;
- `MemRelP.store`: a target write appended at `tm.last + 1` paired with a
  source message pushed at `sm.size`; with `b = true` both are promises
  (mirrored), with `b = false` plain appends;
- `MemRelP.runtime_write`: a target write outside every placed label, no
  source step; `MemRelP.fulfil_runtime`: the fulfilment of an unmirrored
  promise outside every placed label, no source step;
- `MemRelP.fulfil`: a mirrored promise fulfilled on both sides (memories
  and map unchanged, both promises removed);
- `MemRelP.promise_unmirrored`: a target promise the source does not mirror
  (anywhere), no source step; `MemRelP.fulfil_unmirrored`: its fulfilment,
  paired with a source append imaged at the promise's timestamp;
- `MemRelP.alloc`: as `MemRel.alloc`; every target message in the new range
  is an unmirrored promise (`hnone`); `MemRelP.alloc_placed`: the same at a
  label placed in advance (placement maps unchanged);
- the read side: `SLatestP` (the latest source message not promised),
  `MemRelP.latestP` (it maps to the latest target write not promised,
  `TLatestP` over `tp ++ tq`), `MemRelP.latestP_read`;
- `Components.ofMemRelP`: `Components` for a witness with no source epochs
  and target epochs at or after every unmirrored promise.
-/
import Scc.Sem.Coh

namespace Scc.Sem

open Kraken.Promising

/-- **The memory relation with promises**: the memory clauses of
`Components` over every label (no epochs), per-location timestamp order,
and the correspondence between the mirrored target promises `tp` and the
source promises `sp`. -/
structure MemRelP (Λ : Layout) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (ts : Nat → Option Nat) (tm : Memory) (sm : WeakMem.Memory) (tp tq sp : List Nat) : Prop where
  lbl_static : ∀ l b, Λ.static l = some b → lbl l = some b
  lbl_range : ∀ l b, lbl l = some b → b % 8 = 0 ∧ ((lrange lsize l b).Sub Λ.heap ∨ (lrange lsize l b).Sub Λ.data ∨
    (lsize l = 0 ∧ (lrange lsize l b).Sub Λ.pinned))
  lbl_disj : ∀ l l' b b', l ≠ l' → lbl l = some b → lbl l' = some b' → (lrange lsize l b).Disjoint (lrange lsize l' b')
  lbl_mem : ∀ m ∈ sm.toList, ∃ b, lbl m.loc.label = some b ∧ m.loc.offset < lsize m.loc.label
  mem_rep : ∀ k m, sm[k]? = some m → ∃ k' a v, ts k = some k' ∧ wordAddr lbl m.loc = some a ∧
    wordAt tm a k' = some v ∧ ValRep lbl m.val v
  ts_first : ∀ k m, sm[k]? = some m → ts k = some 0 → ∀ k2 m2, k2 < k → sm[k2]? = some m2 → m2.loc ≠ m.loc
  /-- (e): strictly increasing on the positive images of messages to one
  location. -/
  ts_mono : ∀ k1 k2 k1' k2' m1 m2, sm[k1]? = some m1 → sm[k2]? = some m2 → m1.loc = m2.loc →
    ts k1 = some k1' → ts k2 = some k2' → 0 < k1' → 0 < k2' → k1 < k2 → k1' < k2'
  /-- Every target write inside a placed label is an image, or an
  outstanding target promise that is not mirrored (`tq`). -/
  mem_onto : ∀ k' m', tm.get? k' = some m' → (∃ l b, lbl l = some b ∧ (lrange lsize l b).contains m'.loc.addr.toNat) →
    (∃ k, k < sm.size ∧ ts k = some k') ∨ k' ∈ tq
  /-- The map is defined on source messages only. -/
  ts_dom : ∀ k, sm.size ≤ k → ts k = none
  tp_nodup : tp.Nodup
  sp_nodup : sp.Nodup
  /-- Mirrored target promises are target messages. -/
  tp_le : ∀ p ∈ tp, 0 < p ∧ p ≤ tm.last
  /-- Source promises are source messages. -/
  sp_lt : ∀ k ∈ sp, k < sm.size
  /-- A source message is a source promise iff its image is a mirrored
  target promise. -/
  prom_corr : ∀ k k', ts k = some k' → 0 < k' → (k ∈ sp ↔ k' ∈ tp)
  tq_nodup : tq.Nodup
  /-- Unmirrored target promises are target messages ... -/
  tq_le : ∀ p ∈ tq, 0 < p ∧ p ≤ tm.last
  /-- ... with no source image ... -/
  tq_img : ∀ k k', ts k = some k' → k' ∉ tq
  /-- ... and not mirrored. -/
  tp_tq : ∀ p ∈ tp, p ∉ tq

namespace MemRelP

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}

/-- **No promises**: a promise-free `MemRel` (any pair list), with the map
defined on source messages only. -/
theorem of_memRel {pairs : List Nat} (h : MemRel Λ lbl lsize ts tm sm pairs) (hts : ∀ k, sm.size ≤ k → ts k = none) :
    MemRelP Λ lbl lsize ts tm sm [] [] [] where
  lbl_static := h.lbl_static
  lbl_range := h.lbl_range
  lbl_disj := h.lbl_disj
  lbl_mem := h.lbl_mem
  mem_rep := h.mem_rep
  ts_first := h.ts_first
  ts_mono k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt :=
    (h.ts_mono k1 k2 k1' k2' h1 h2 p1 p2 hlt).resolve_right fun ⟨_, _, _, hne⟩ => hne m1 m2 hm1 hm2 hloc
  mem_onto k' m' hg hin := .inl (h.mem_onto k' m' hg hin)
  ts_dom := hts
  tp_nodup := List.nodup_nil
  sp_nodup := List.nodup_nil
  tp_le _ hp := absurd hp List.not_mem_nil
  sp_lt _ hk := absurd hk List.not_mem_nil
  prom_corr _ _ _ _ := ⟨fun h => absurd h List.not_mem_nil, fun h => absurd h List.not_mem_nil⟩
  tq_nodup := List.nodup_nil
  tq_le _ hp := absurd hp List.not_mem_nil
  tq_img _ _ _ := List.not_mem_nil
  tp_tq _ hp := absurd hp List.not_mem_nil

/-- **Every image exists**: a source message's timestamp is at most the
target's last. -/
theorem ts_le_last (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {k k' : Nat} (hk : k < sm.size)
    (ht : ts k = some k') : k' ≤ tm.last := by
  obtain ⟨k'', a, v, ht', -, hw, -⟩ := h.mem_rep k sm[k] (Array.getElem?_eq_getElem hk)
  rw [ht] at ht'; cases ht'
  exact le_last_of_wordAt hw

/-- A source message index of a defined image is a source message. -/
theorem lt_of_ts (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {k k' : Nat} (ht : ts k = some k') : k < sm.size := by
  rcases Nat.lt_or_ge k sm.size with h' | h'
  · exact h'
  · rw [h.ts_dom k h'] at ht; cases ht

/-- A timestamp of an appended memory other than the new one is old. -/
theorem le_last_of_append_ne {w : Msg} {k' : Nat} {m' : Msg} (hg : (tm.append w).1.get? k' = some m')
    (hk : k' ≠ tm.last + 1) : k' ≤ tm.last :=
  Memory.le_last_of_get? (CohCoversP.get?_append_ne hg hk)

/-! ## A store or a promise -/

/-- **A store, or a promise on both sides**: the target appends an 8-byte
message of `v` at the word address `a` (timestamp `tm.last + 1`); the source
pushes a message `m` (index `sm.size`) to the source address placed at `a`,
in bounds, with a value `v` represents. With `b = true` the pair is an
outstanding promise on each side. -/
theorem store (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {a : Nat} {v : Val} {tid : Nat} {m : WeakMem.Msg}
    (ha : wordAddr lbl m.loc = some a) (ho : m.loc.offset < lsize m.loc.label) (hv : ValRep lbl m.val v.toNat)
    (b : Bool) :
    MemRelP Λ lbl lsize (fun k => if k = sm.size then some (tm.last + 1) else ts k)
      (tm.append ⟨wordLoc a, v, tid⟩).1 (sm.push m)
      (if b then tp ++ [tm.last + 1] else tp) tq (if b then sp ++ [sm.size] else sp) := by
  have hlast : ∀ k k', ts k = some k' → k' ≤ tm.last := fun k k' ht => h.ts_le_last (h.lt_of_ts ht) ht
  have pushGet : ∀ k m', (sm.push m)[k]? = some m' → (k < sm.size ∧ sm[k]? = some m') ∨ (k = sm.size ∧ m' = m) := by
    intro k m' hk
    rw [Array.getElem?_push] at hk
    split at hk
    · cases hk; exact .inr ⟨by assumption, rfl⟩
    · refine .inl ⟨?_, hk⟩
      rcases Nat.lt_or_ge k sm.size with h' | h'
      · exact h'
      · rename_i hne
        simp [Array.getElem?_eq_none (by omega : sm.size ≤ k)] at hk
  have hlastA : (tm.append ⟨wordLoc a, v, tid⟩).1.last = tm.last + 1 := by
    simp [Memory.last, Memory.append]
  have tpNew : tm.last + 1 ∉ tp := fun hm => by have := (h.tp_le _ hm).2; omega
  have spNew : sm.size ∉ sp := fun hm => by have := h.sp_lt _ hm; omega
  have tqNew : tm.last + 1 ∉ tq := fun hm => by have := (h.tq_le _ hm).2; omega
  refine ⟨h.lbl_static, h.lbl_range, h.lbl_disj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.tq_nodup, ?_, ?_, ?_⟩
  · intro m' hm'
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm'
    rcases hm' with hm' | rfl
    · exact h.lbl_mem m' hm'
    · simp only [wordAddr, Option.map_eq_some_iff] at ha
      obtain ⟨b, hb, -⟩ := ha
      exact ⟨b, hb, ho⟩
  · intro k m' hk
    rcases pushGet k m' hk with ⟨hlt, hk⟩ | ⟨rfl, rfl⟩
    · obtain ⟨k', a', v', ht, ha', hw, hv'⟩ := h.mem_rep k m' hk
      refine ⟨k', a', v', by simp [Nat.ne_of_lt hlt, ht], ha', ?_, hv'⟩
      rw [wordAt_append_le (hlast k k' ht)]; exact hw
    · refine ⟨tm.last + 1, a, v.toNat, by simp, ha, ?_, hv⟩
      simp [wordAt, Memory.read?, Memory.get?_append_new]
  · intro k m' hk ht0 k2 m2 hk2 hm2
    rcases pushGet k m' hk with ⟨hlt, hk⟩ | ⟨rfl, rfl⟩
    · have ht : ts k = some 0 := by simpa [Nat.ne_of_lt hlt] using ht0
      rcases pushGet k2 m2 hm2 with ⟨-, hm2⟩ | ⟨rfl, -⟩
      · exact h.ts_first k m' hk ht k2 m2 hk2 hm2
      · omega
    · simp at ht0
  · intro k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt
    by_cases e2 : k2 = sm.size
    · subst e2
      have e1 : k1 ≠ sm.size := by omega
      simp only [e1, ite_false] at h1
      simp only [ite_true] at h2; cases h2
      have := hlast k1 k1' h1
      omega
    · have e1 : k1 ≠ sm.size := by
        intro e; subst e
        simp only [e2, ite_false] at h2
        rw [h.ts_dom k2 (by omega)] at h2; cases h2
      simp only [e1, e2, ite_false] at h1 h2
      rcases pushGet k1 m1 hm1 with ⟨-, hm1⟩ | ⟨he, -⟩
      · rcases pushGet k2 m2 hm2 with ⟨-, hm2⟩ | ⟨he, -⟩
        · exact h.ts_mono k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt
        · exact absurd he e2
      · exact absurd he e1
  · intro k' m' hg hin
    by_cases hk : k' = tm.last + 1
    · subst hk
      exact .inl ⟨sm.size, by simp, by simp⟩
    · have hle := le_last_of_append_ne hg hk
      rw [Memory.get?_append_le hle] at hg
      rcases h.mem_onto k' m' hg hin with ⟨k, hk', ht⟩ | hq
      · refine .inl ⟨k, by simp; omega, ?_⟩
        simp [Nat.ne_of_lt hk', ht]
      · exact .inr hq
  · intro k hk
    simp only [Array.size_push] at hk
    simp only [show k ≠ sm.size by omega, ite_false]
    exact h.ts_dom k (by omega)
  · cases b
    · exact h.tp_nodup
    · simp only [ite_true]
      exact List.nodup_append.mpr ⟨h.tp_nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun x hx y hy => by
        rw [List.mem_singleton] at hy; subst hy; intro he; subst he; exact tpNew hx⟩
  · cases b
    · exact h.sp_nodup
    · simp only [ite_true]
      exact List.nodup_append.mpr ⟨h.sp_nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun x hx y hy => by
        rw [List.mem_singleton] at hy; subst hy; intro he; subst he; exact spNew hx⟩
  · intro p hp
    rw [hlastA]
    cases b
    · have := h.tp_le p hp; omega
    · simp only [ite_true, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · have := h.tp_le p hp; omega
      · omega
  · intro k hk
    simp only [Array.size_push]
    cases b
    · have := h.sp_lt k hk; omega
    · simp only [ite_true, List.mem_append, List.mem_singleton] at hk
      rcases hk with hk | rfl
      · have := h.sp_lt k hk; omega
      · omega
  · intro k k' ht hpos
    by_cases e : k = sm.size
    · subst e
      simp only [ite_true, Option.some.injEq] at ht; subst ht
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        exact ⟨fun hm => absurd hm spNew, fun hm => absurd hm tpNew⟩
      · simp
    · simp only [e, ite_false] at ht
      have hk' := hlast k k' ht
      have c := h.prom_corr k k' ht hpos
      cases b
      · exact c
      · simp only [ite_true, List.mem_append, List.mem_singleton]
        constructor
        · rintro (hm | hm)
          · exact .inl (c.mp hm)
          · exact absurd hm e
        · rintro (hm | hm)
          · exact .inl (c.mpr hm)
          · omega

  · intro p hp
    rw [hlastA]; have := h.tq_le p hp; omega
  · intro k k' ht hq
    by_cases e : k = sm.size
    · subst e
      simp only [ite_true, Option.some.injEq] at ht; subst ht
      exact tqNew hq
    · simp only [e, ite_false] at ht
      exact h.tq_img k k' ht hq
  · intro p hp
    cases b
    · exact h.tp_tq p hp
    · simp only [ite_true, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact h.tp_tq p hp
      · exact tqNew

/-! ## Runtime writes -/

/-- **A runtime write or promise**: a target message outside every placed
label's range, with no source step and no mirrored promise. -/
theorem runtime_write (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {w : Msg}
    (hout : ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains w.loc.addr.toNat) :
    MemRelP Λ lbl lsize ts (tm.append w).1 sm tp tq sp := by
  have hlastA : (tm.append w).1.last = tm.last + 1 := by simp [Memory.last, Memory.append]
  refine ⟨h.lbl_static, h.lbl_range, h.lbl_disj, h.lbl_mem, ?_, h.ts_first, h.ts_mono, ?_, h.ts_dom,
    h.tp_nodup, h.sp_nodup, ?_, h.sp_lt, h.prom_corr, h.tq_nodup, ?_, h.tq_img, h.tp_tq⟩
  · intro k m hk
    obtain ⟨k', a, v, ht, ha, hw, hv⟩ := h.mem_rep k m hk
    refine ⟨k', a, v, ht, ha, ?_, hv⟩
    rw [wordAt_append_le (h.ts_le_last (h.lt_of_ts ht) ht)]; exact hw
  · intro k' m' hg hin
    by_cases hk : k' = tm.last + 1
    · subst hk
      rw [Memory.get?_append_new] at hg; cases hg
      exact absurd hin hout
    · rw [Memory.get?_append_le (le_last_of_append_ne hg hk)] at hg
      exact h.mem_onto k' m' hg hin
  · intro p hp
    rw [hlastA]; have := h.tp_le p hp; omega
  · intro p hp
    rw [hlastA]; have := h.tq_le p hp; omega

/-- **A runtime fulfilment**: the target fulfils an unmirrored promise `q`
whose message lies outside every placed label's range; memories, the map and
the mirrored promises are unchanged, `q` leaves `tq`. -/
theorem fulfil_runtime (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {q : Nat} {w : Msg}
    (hg : tm.get? q = some w)
    (hout : ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains w.loc.addr.toNat) :
    MemRelP Λ lbl lsize ts tm sm tp (tq.erase q) sp := by
  refine ⟨h.lbl_static, h.lbl_range, h.lbl_disj, h.lbl_mem, h.mem_rep, h.ts_first, h.ts_mono, ?_, h.ts_dom,
    h.tp_nodup, h.sp_nodup, h.tp_le, h.sp_lt, h.prom_corr, h.tq_nodup.erase q,
    fun p hp => h.tq_le p (List.mem_of_mem_erase hp),
    fun k k' ht hq => h.tq_img k k' ht (List.mem_of_mem_erase hq),
    fun p hp hq => h.tp_tq p hp (List.mem_of_mem_erase hq)⟩
  intro k' m' hg' hin
  by_cases he : k' = q
  · subst he; rw [hg] at hg'; cases hg'; exact absurd hin hout
  · exact (h.mem_onto k' m' hg' hin).imp_right fun hm => (List.mem_erase_of_ne he).mpr hm

/-! ## Allocation -/

/-- **An allocation**: as `MemRel.alloc`. Every target message in the new
range is an unmirrored outstanding promise (`hnone`: a promise the thread
made to the address its allocator returns now); the promises are unchanged. -/
theorem alloc (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {l : WeakMem.AllocLabel} {n b : Nat}
    (hfresh : lbl l = none) (hb : b % 8 = 0) (hheap : (Range.mk b (8 * n)).Sub Λ.heap)
    (hdisj : ∀ l' b', lbl l' = some b' → (Range.mk b (8 * n)).Disjoint (lrange lsize l' b'))
    (hnone : ∀ k' w, tm.get? k' = some w → (Range.mk b (8 * n)).contains w.loc.addr.toNat → k' ∈ tq)
    (hinit : ∀ i < n, tm.initVal (wordLoc (b + 8 * i)) = 0)
    {sm' : WeakMem.Memory} (hsize : sm'.size = sm.size + n) (hold : ∀ k < sm.size, sm'[k]? = sm[k]?)
    (hnew : ∀ i < n, ∃ m, sm'[sm.size + i]? = some m ∧ m.loc = ⟨l, i⟩ ∧
      ValRep (fun l' => if l' = l then some b else lbl l') m.val 0) :
    MemRelP Λ (fun l' => if l' = l then some b else lbl l') (fun l' => if l' = l then n else lsize l')
      (fun k => if sm.size ≤ k ∧ k < sm.size + n then some 0 else ts k) tm sm' tp tq sp := by
  have hold_lbl : ∀ m ∈ sm.toList, m.loc.label ≠ l := by
    intro m hm he
    obtain ⟨b', hb', -⟩ := h.lbl_mem m hm
    rw [he, hfresh] at hb'; cases hb'
  have hext : ∀ l' b', lbl l' = some b' → (fun l'' => if l'' = l then some b else lbl l'') l' = some b' := by
    intro l' b' hl'
    have : l' ≠ l := by intro he; rw [he, hfresh] at hl'; cases hl'
    simp [this, hl']
  have hrange : ∀ l', l' ≠ l → ∀ b', lrange (fun l'' => if l'' = l then n else lsize l'') l' b' = lrange lsize l' b' := by
    intro l' hl' b'; simp [lrange, hl']
  have hrange_l : lrange (fun l'' => if l'' = l then n else lsize l'') l b = Range.mk b (8 * n) := by simp [lrange]
  have hcases : ∀ k m, sm'[k]? = some m → (k < sm.size ∧ sm[k]? = some m) ∨
      (∃ i, i < n ∧ k = sm.size + i ∧ m.loc = ⟨l, i⟩ ∧ ValRep (fun l' => if l' = l then some b else lbl l') m.val 0) := by
    intro k m hk
    rcases Nat.lt_or_ge k sm.size with hlt | hge
    · exact .inl ⟨hlt, by rw [← hold k hlt]; exact hk⟩
    · have hkn : k < sm.size + n := by
        rcases Nat.lt_or_ge k (sm.size + n) with h' | h'
        · exact h'
        · rw [← hsize] at h'; simp [Array.getElem?_eq_none h'] at hk
      obtain ⟨m', hm', hl', hv'⟩ := hnew (k - sm.size) (by omega)
      rw [show sm.size + (k - sm.size) = k by omega, hk] at hm'; cases hm'
      exact .inr ⟨k - sm.size, by omega, by omega, hl', hv'⟩
  have hmemOld : ∀ k m, sm[k]? = some m → m ∈ sm.toList := fun k m hk =>
    Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk)
  -- a positive image is an old one
  have hpos : ∀ k k', (if sm.size ≤ k ∧ k < sm.size + n then some 0 else ts k) = some k' → 0 < k' →
      ts k = some k' ∧ k < sm.size := by
    intro k k' ht hp
    by_cases hc : sm.size ≤ k ∧ k < sm.size + n
    · simp only [hc, and_self, ite_true, Option.some.injEq] at ht; omega
    · simp only [hc, ite_false] at ht; exact ⟨ht, h.lt_of_ts ht⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.tp_nodup, h.sp_nodup, h.tp_le, ?_, ?_, h.tq_nodup, h.tq_le, ?_, h.tp_tq⟩
  · intro l' b' hs
    exact hext _ _ (h.lbl_static l' b' hs)
  · intro l' b' hl'
    by_cases he : l' = l
    · subst he
      simp only [ite_true] at hl'; cases hl'
      exact ⟨hb, .inl (by rw [hrange_l]; exact hheap)⟩
    · simp only [he, ite_false] at hl'
      rw [hrange l' he]; simpa only [he, ite_false] using h.lbl_range l' b' hl'
  · intro l1 l2 b1 b2 hne h1 h2
    by_cases e1 : l1 = l
    · subst e1
      have e2 : l2 ≠ l1 := fun e => hne e.symm
      simp only [ite_true] at h1; cases h1
      simp only [e2, ite_false] at h2
      rw [hrange_l, hrange l2 e2]; exact hdisj l2 b2 h2
    · simp only [e1, ite_false] at h1
      by_cases e2 : l2 = l
      · subst e2
        simp only [ite_true] at h2; cases h2
        rw [hrange_l, hrange l1 e1]
        have := hdisj l1 b1 h1
        simp only [Range.Disjoint] at this ⊢; omega
      · simp only [e2, ite_false] at h2
        rw [hrange l1 e1, hrange l2 e2]; exact h.lbl_disj l1 l2 b1 b2 hne h1 h2
  · intro m hm
    obtain ⟨k, hk⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp hm)
    rcases hcases k m hk with ⟨-, hk⟩ | ⟨i, hi, -, hl, -⟩
    · have hne := hold_lbl m (hmemOld k m hk)
      obtain ⟨b', hb', ho⟩ := h.lbl_mem m (hmemOld k m hk)
      exact ⟨b', by simp [hne, hb'], by simp [hne, ho]⟩
    · rw [hl]; exact ⟨b, by simp, by simpa using hi⟩
  · intro k m hk
    rcases hcases k m hk with ⟨hlt, hk⟩ | ⟨i, hi, rfl, hl, hv⟩
    · obtain ⟨k', a, v, ht, ha, hw, hv⟩ := h.mem_rep k m hk
      have hne := hold_lbl m (hmemOld k m hk)
      refine ⟨k', a, v, by simp [show ¬ sm.size ≤ k by omega, ht], ?_, hw, MemRel.valRep_mono hext hv⟩
      simpa [wordAddr, hne] using ha
    · refine ⟨0, b + 8 * i, 0, by simp [show i < n from hi], by simp [wordAddr, hl], ?_, hv⟩
      rw [wordAt_of_read (v := tm.initVal (wordLoc (b + 8 * i))) (by simp [Memory.read?]), hinit i hi]
      rfl
  · intro k m hk ht0 k2 m2 hk2 hm2
    rcases hcases k m hk with ⟨hlt, hk⟩ | ⟨i, hi, rfl, hl, -⟩
    · have ht : ts k = some 0 := by simpa [show ¬ sm.size ≤ k by omega] using ht0
      rcases hcases k2 m2 hm2 with ⟨-, hm2⟩ | ⟨i2, -, rfl, -, -⟩
      · exact h.ts_first k m hk ht k2 m2 hk2 hm2
      · omega
    · rw [hl]
      rcases hcases k2 m2 hm2 with ⟨-, hm2⟩ | ⟨i2, -, rfl, hl2, -⟩
      · intro he; exact hold_lbl m2 (hmemOld k2 m2 hm2) (by rw [he])
      · rw [hl2]; intro he; simp only [WeakMem.Address.mk.injEq] at he
        have he' : @Eq Nat i2 i := by
          first | exact he.2 | exact he | exact he.2.symm | exact he.symm
        exfalso; omega
  · intro k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt
    obtain ⟨h1, hk1⟩ := hpos k1 k1' h1 p1
    obtain ⟨h2, hk2⟩ := hpos k2 k2' h2 p2
    rw [hold k1 hk1] at hm1
    rw [hold k2 hk2] at hm2
    exact h.ts_mono k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt
  · intro k' m' hg hin
    obtain ⟨l', b', hl', hc⟩ := hin
    by_cases he : l' = l
    · subst he
      simp only [ite_true] at hl'; cases hl'
      rw [hrange_l] at hc
      exact .inr (hnone k' m' hg hc)
    · simp only [he, ite_false] at hl'
      rw [hrange l' he] at hc
      rcases h.mem_onto k' m' hg ⟨l', b', hl', hc⟩ with ⟨k, hk, ht⟩ | hq
      · exact .inl ⟨k, by omega, by simp [show ¬ sm.size ≤ k by omega, ht]⟩
      · exact .inr hq
  · intro k hk
    rw [hsize] at hk
    simp only [show ¬ (sm.size ≤ k ∧ k < sm.size + n) by omega, ite_false]
    exact h.ts_dom k (by omega)
  · intro k hk; have := h.sp_lt k hk; omega
  · intro k k' ht hp
    obtain ⟨ht, -⟩ := hpos k k' ht hp
    exact h.prom_corr k k' ht hp
  · intro k k' ht hq
    have := (h.tq_le k' hq).1
    obtain ⟨ht, -⟩ := hpos k k' ht this
    exact h.tq_img k k' ht hq

/-- **An allocation at a label already placed**: as `alloc`, but the label
`l` is placed already (at `b`, `lsize l = n`), with no source message yet
(`hno`). The placement maps are unchanged, so the relation keeps one `lbl`
across the allocation (a placement fixed in advance, as a deterministic
one-thread allocator allows). No condition on the target messages in the
range: `mem_onto` already makes each one an image (of another label's
message, so outside the range by `lbl_disj`) or an unmirrored promise. -/
theorem alloc_placed (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {l : WeakMem.AllocLabel} {n b : Nat}
    (hl : lbl l = some b) (hn : lsize l = n) (hno : ∀ m ∈ sm.toList, m.loc.label ≠ l)
    (hinit : ∀ i < n, tm.initVal (wordLoc (b + 8 * i)) = 0)
    {sm' : WeakMem.Memory} (hsize : sm'.size = sm.size + n) (hold : ∀ k < sm.size, sm'[k]? = sm[k]?)
    (hnew : ∀ i < n, ∃ m, sm'[sm.size + i]? = some m ∧ m.loc = ⟨l, i⟩ ∧ ValRep lbl m.val 0) :
    MemRelP Λ lbl lsize (fun k => if sm.size ≤ k ∧ k < sm.size + n then some 0 else ts k) tm sm' tp tq sp := by
  have hcases : ∀ k m, sm'[k]? = some m → (k < sm.size ∧ sm[k]? = some m) ∨
      (∃ i, i < n ∧ k = sm.size + i ∧ m.loc = ⟨l, i⟩ ∧ ValRep lbl m.val 0) := by
    intro k m hk
    rcases Nat.lt_or_ge k sm.size with hlt | hge
    · exact .inl ⟨hlt, by rw [← hold k hlt]; exact hk⟩
    · have hkn : k < sm.size + n := by
        rcases Nat.lt_or_ge k (sm.size + n) with h' | h'
        · exact h'
        · rw [← hsize] at h'; simp [Array.getElem?_eq_none h'] at hk
      obtain ⟨m', hm', hl', hv'⟩ := hnew (k - sm.size) (by omega)
      rw [show sm.size + (k - sm.size) = k by omega, hk] at hm'; cases hm'
      exact .inr ⟨k - sm.size, by omega, by omega, hl', hv'⟩
  have hmemOld : ∀ k m, sm[k]? = some m → m ∈ sm.toList := fun k m hk =>
    Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk)
  have hpos : ∀ k k', (if sm.size ≤ k ∧ k < sm.size + n then some 0 else ts k) = some k' → 0 < k' →
      ts k = some k' ∧ k < sm.size := by
    intro k k' ht hp
    by_cases hc : sm.size ≤ k ∧ k < sm.size + n
    · simp only [hc, and_self, ite_true, Option.some.injEq] at ht; omega
    · simp only [hc, ite_false] at ht; exact ⟨ht, h.lt_of_ts ht⟩
  refine ⟨h.lbl_static, h.lbl_range, h.lbl_disj, ?_, ?_, ?_, ?_, ?_, ?_, h.tp_nodup, h.sp_nodup, h.tp_le, ?_, ?_,
    h.tq_nodup, h.tq_le, ?_, h.tp_tq⟩
  · intro m hm
    obtain ⟨k, hk⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp hm)
    rcases hcases k m hk with ⟨-, hk⟩ | ⟨i, hi, -, hml, -⟩
    · exact h.lbl_mem m (hmemOld k m hk)
    · rw [hml]; exact ⟨b, hl, show i < lsize l by omega⟩
  · intro k m hk
    rcases hcases k m hk with ⟨hlt, hk⟩ | ⟨i, hi, rfl, hml, hv⟩
    · obtain ⟨k', a, v, ht, ha, hw, hv⟩ := h.mem_rep k m hk
      exact ⟨k', a, v, by simp [show ¬ sm.size ≤ k by omega, ht], ha, hw, hv⟩
    · refine ⟨0, b + 8 * i, 0, by simp [show i < n from hi], by simp [wordAddr, hml, hl], ?_, hv⟩
      rw [wordAt_of_read (v := tm.initVal (wordLoc (b + 8 * i))) (by simp [Memory.read?]), hinit i hi]
      rfl
  · intro k m hk ht0 k2 m2 hk2 hm2
    rcases hcases k m hk with ⟨hlt, hk⟩ | ⟨i, hi, rfl, hml, -⟩
    · have ht : ts k = some 0 := by simpa [show ¬ sm.size ≤ k by omega] using ht0
      rcases hcases k2 m2 hm2 with ⟨-, hm2⟩ | ⟨i2, -, rfl, -, -⟩
      · exact h.ts_first k m hk ht k2 m2 hk2 hm2
      · omega
    · rw [hml]
      rcases hcases k2 m2 hm2 with ⟨-, hm2⟩ | ⟨i2, -, rfl, hl2, -⟩
      · intro he; exact hno m2 (hmemOld k2 m2 hm2) (by rw [he])
      · rw [hl2]; intro he; simp only [WeakMem.Address.mk.injEq] at he
        have he' : @Eq Nat i2 i := by
          first | exact he.2 | exact he | exact he.2.symm | exact he.symm
        exfalso; omega
  · intro k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt
    obtain ⟨h1, hk1⟩ := hpos k1 k1' h1 p1
    obtain ⟨h2, hk2⟩ := hpos k2 k2' h2 p2
    rw [hold k1 hk1] at hm1
    rw [hold k2 hk2] at hm2
    exact h.ts_mono k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt
  · intro k' m' hg hin
    rcases h.mem_onto k' m' hg hin with ⟨k, hk, ht⟩ | hq
    · exact .inl ⟨k, by omega, by simp [show ¬ sm.size ≤ k by omega, ht]⟩
    · exact .inr hq
  · intro k hk
    rw [hsize] at hk
    simp only [show ¬ (sm.size ≤ k ∧ k < sm.size + n) by omega, ite_false]
    exact h.ts_dom k (by omega)
  · intro k hk; have := h.sp_lt k hk; omega
  · intro k k' ht hp
    obtain ⟨ht, -⟩ := hpos k k' ht hp
    exact h.prom_corr k k' ht hp
  · intro k k' ht hq
    have := (h.tq_le k' hq).1
    obtain ⟨ht, -⟩ := hpos k k' ht this
    exact h.tq_img k k' ht hq

/-! ## Fulfilment -/

/-- **A fulfilment on both sides**: the target fulfils its mirrored promise
`p` and the source its promise `k` imaged at `p` (`huniq`: the only source
message imaged at `p`); memories and the map are unchanged, both promises
are removed. -/
theorem fulfil (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {k p : Nat} (hkp : ts k = some p)
    (huniq : ∀ k2, ts k2 = some p → k2 = k) :
    MemRelP Λ lbl lsize ts tm sm (tp.erase p) tq (sp.erase k) := by
  refine ⟨h.lbl_static, h.lbl_range, h.lbl_disj, h.lbl_mem, h.mem_rep, h.ts_first, h.ts_mono, h.mem_onto,
    h.ts_dom, h.tp_nodup.erase p, h.sp_nodup.erase k, fun q hq => h.tp_le q (List.mem_of_mem_erase hq),
    fun q hq => h.sp_lt q (List.mem_of_mem_erase hq), ?_, h.tq_nodup, h.tq_le, h.tq_img,
    fun q hq => h.tp_tq q (List.mem_of_mem_erase hq)⟩
  intro k2 k2' ht hpos
  have c := h.prom_corr k2 k2' ht hpos
  by_cases e : k2 = k
  · subst e
    rw [hkp] at ht; cases ht
    exact ⟨fun hm => absurd hm (h.sp_nodup.not_mem_erase), fun hm => absurd hm (h.tp_nodup.not_mem_erase)⟩
  · have e' : k2' ≠ p := fun he => e (huniq k2 (he ▸ ht))
    rw [List.mem_erase_of_ne e, List.mem_erase_of_ne e']
    exact c

/-! ## Unmirrored promises -/

/-- **An unmirrored target promise**: the target appends a message
(anywhere, in a label's range or not) that the source does not mirror; it
joins `tq`. No source step. -/
theorem promise_unmirrored (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (w : Msg) :
    MemRelP Λ lbl lsize ts (tm.append w).1 sm tp (tq ++ [tm.last + 1]) sp := by
  have hlastA : (tm.append w).1.last = tm.last + 1 := by simp [Memory.last, Memory.append]
  have tqNew : tm.last + 1 ∉ tq := fun hm => by have := (h.tq_le _ hm).2; omega
  refine ⟨h.lbl_static, h.lbl_range, h.lbl_disj, h.lbl_mem, ?_, h.ts_first, h.ts_mono, ?_, h.ts_dom,
    h.tp_nodup, h.sp_nodup, ?_, h.sp_lt, h.prom_corr, ?_, ?_, ?_, ?_⟩
  · intro k m hk
    obtain ⟨k', a, v, ht, ha, hw, hv⟩ := h.mem_rep k m hk
    refine ⟨k', a, v, ht, ha, ?_, hv⟩
    rw [wordAt_append_le (h.ts_le_last (h.lt_of_ts ht) ht)]; exact hw
  · intro k' m' hg hin
    by_cases hk : k' = tm.last + 1
    · subst hk
      exact .inr (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    · rw [Memory.get?_append_le (le_last_of_append_ne hg hk)] at hg
      exact (h.mem_onto k' m' hg hin).imp_right (List.mem_append_left _)
  · intro p hp
    rw [hlastA]; have := h.tp_le p hp; omega
  · exact List.nodup_append.mpr ⟨h.tq_nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun x hx y hy => by rw [List.mem_singleton] at hy; subst hy; intro he; subst he; exact tqNew hx⟩
  · intro p hp
    rw [hlastA]
    rcases List.mem_append.mp hp with hp | hp
    · have := h.tq_le p hp; omega
    · rw [List.mem_singleton] at hp; subst hp; omega
  · intro k k' ht hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h.tq_img k k' ht hq
    · rw [List.mem_singleton] at hq; subst hq
      have := h.ts_le_last (h.lt_of_ts ht) ht; omega
  · intro p hp hq
    rcases List.mem_append.mp hq with hq | hq
    · exact h.tp_tq p hp hq
    · rw [List.mem_singleton] at hq; subst hq
      have := (h.tp_le _ hp).2; omega

/-- **An unmirrored promise fulfilled**: the target fulfils `q ∈ tq`, an
8-byte message of `v` at the word address `a` (memory unchanged); the source
appends a message `m` (index `sm.size`) to the source address placed at
`a`, in bounds, with a value `v` represents, and its image is `q`. Every
earlier source message to that address must map below `q` (`hmono`: Kraken
fulfils above the thread's coherence view of the location, which covers
every earlier write to it in one thread). -/
theorem fulfil_unmirrored (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {q a : Nat} {v : Val} {tid : Nat}
    {m : WeakMem.Msg} (hq : q ∈ tq) (hg : tm.get? q = some ⟨wordLoc a, v, tid⟩)
    (ha : wordAddr lbl m.loc = some a) (ho : m.loc.offset < lsize m.loc.label) (hv : ValRep lbl m.val v.toNat)
    (hmono : ∀ k mk k', sm[k]? = some mk → mk.loc = m.loc → ts k = some k' → k' < q) :
    MemRelP Λ lbl lsize (fun k => if k = sm.size then some q else ts k) tm (sm.push m) tp (tq.erase q) sp := by
  have pushGet : ∀ k m', (sm.push m)[k]? = some m' → (k < sm.size ∧ sm[k]? = some m') ∨ (k = sm.size ∧ m' = m) := by
    intro k m' hk
    rw [Array.getElem?_push] at hk
    split at hk
    · cases hk; exact .inr ⟨by assumption, rfl⟩
    · refine .inl ⟨?_, hk⟩
      rcases Nat.lt_or_ge k sm.size with h' | h'
      · exact h'
      · rename_i hne
        simp [Array.getElem?_eq_none (by omega : sm.size ≤ k)] at hk
  have hqpos := (h.tq_le q hq).1
  have hqtp : q ∉ tp := fun hp => h.tp_tq q hp hq
  have spNew : sm.size ∉ sp := fun hm => by have := h.sp_lt _ hm; omega
  refine ⟨h.lbl_static, h.lbl_range, h.lbl_disj, ?_, ?_, ?_, ?_, ?_, ?_, h.tp_nodup, h.sp_nodup, h.tp_le, ?_, ?_,
    h.tq_nodup.erase q, fun p hp => h.tq_le p (List.mem_of_mem_erase hp), ?_, ?_⟩
  · intro m' hm'
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm'
    rcases hm' with hm' | rfl
    · exact h.lbl_mem m' hm'
    · simp only [wordAddr, Option.map_eq_some_iff] at ha
      obtain ⟨b, hb, -⟩ := ha
      exact ⟨b, hb, ho⟩
  · intro k m' hk
    rcases pushGet k m' hk with ⟨hlt, hk⟩ | ⟨rfl, rfl⟩
    · obtain ⟨k', a', v', ht, ha', hw, hv'⟩ := h.mem_rep k m' hk
      exact ⟨k', a', v', by simp [Nat.ne_of_lt hlt, ht], ha', hw, hv'⟩
    · refine ⟨q, a, v.toNat, by simp, ha, ?_, hv⟩
      have hq0 : q ≠ 0 := by omega
      simp [wordAt, Memory.read?, hq0, hg]
  · intro k m' hk ht0 k2 m2 hk2 hm2
    rcases pushGet k m' hk with ⟨hlt, hk⟩ | ⟨rfl, rfl⟩
    · have ht : ts k = some 0 := by simpa [Nat.ne_of_lt hlt] using ht0
      rcases pushGet k2 m2 hm2 with ⟨-, hm2⟩ | ⟨rfl, -⟩
      · exact h.ts_first k m' hk ht k2 m2 hk2 hm2
      · omega
    · simp only [ite_true, Option.some.injEq] at ht0; omega
  · intro k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt
    rcases pushGet k2 m2 hm2 with ⟨hk2, hm2⟩ | ⟨rfl, rfl⟩
    · rcases pushGet k1 m1 hm1 with ⟨hk1, hm1⟩ | ⟨rfl, -⟩
      · simp only [Nat.ne_of_lt hk1, Nat.ne_of_lt hk2, ite_false] at h1 h2
        exact h.ts_mono k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt
      · omega
    · rcases pushGet k1 m1 hm1 with ⟨hk1, hm1⟩ | ⟨rfl, -⟩
      · simp only [Nat.ne_of_lt hk1, ite_false] at h1
        simp only [ite_true, Option.some.injEq] at h2; subst h2
        exact hmono k1 m1 k1' hm1 hloc h1
      · omega
  · intro k' m' hg' hin
    by_cases e : k' = q
    · subst e
      exact .inl ⟨sm.size, by simp, by simp⟩
    · rcases h.mem_onto k' m' hg' hin with ⟨k, hk, ht⟩ | hq'
      · refine .inl ⟨k, by simp; omega, ?_⟩
        simp [Nat.ne_of_lt hk, ht]
      · exact .inr ((List.mem_erase_of_ne e).mpr hq')
  · intro k hk
    simp only [Array.size_push] at hk
    simp only [show k ≠ sm.size by omega, ite_false]
    exact h.ts_dom k (by omega)
  · intro k hk
    simp only [Array.size_push]; have := h.sp_lt k hk; omega
  · intro k k' ht hpos
    by_cases e : k = sm.size
    · subst e
      simp only [ite_true, Option.some.injEq] at ht; subst ht
      exact ⟨fun hm => absurd hm spNew, fun hm => absurd hm hqtp⟩
    · simp only [e, ite_false] at ht
      exact h.prom_corr k k' ht hpos
  · intro k k' ht hq'
    by_cases e : k = sm.size
    · subst e
      simp only [ite_true, Option.some.injEq] at ht; subst ht
      exact h.tq_nodup.not_mem_erase hq'
    · simp only [e, ite_false] at ht
      exact h.tq_img k k' ht (List.mem_of_mem_erase hq')
  · intro p hp hq'
    exact h.tp_tq p hp (List.mem_of_mem_erase hq')

/-! ## The read side -/

/-- **Placement is injective on in-bounds addresses** (`MemRel.wordAddr_inj`). -/
theorem wordAddr_inj (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {a1 a2 : WeakMem.Address} {x : Nat}
    (h1 : wordAddr lbl a1 = some x) (h2 : wordAddr lbl a2 = some x) (o1 : a1.offset < lsize a1.label)
    (o2 : a2.offset < lsize a2.label) : a1 = a2 := by
  simp only [wordAddr, Option.map_eq_some_iff] at h1 h2
  obtain ⟨b1, hb1, rfl⟩ := h1
  obtain ⟨b2, hb2, he⟩ := h2
  rw [mul_offset, mul_offset] at he
  have o1' : @LT.lt Nat instLTNat a1.offset (lsize a1.label) := o1
  have o2' : @LT.lt Nat instLTNat a2.offset (lsize a2.label) := o2
  by_cases hl : a1.label = a2.label
  · rw [hl, hb2] at hb1; cases hb1
    have : @Eq Nat a1.offset a2.offset := by omega
    cases a1; cases a2; simp_all
  · have := h.lbl_disj _ _ _ _ hl hb1 hb2
    simp only [lrange, Range.Disjoint] at this
    exfalso; omega

/-- Placed in-bounds words of a well-formed layout are below `2^64`
(`MemRel.addr_lt`). -/
theorem addr_lt (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) {sa : WeakMem.Address} {x : Nat}
    (hx : wordAddr lbl sa = some x) (ho : sa.offset < lsize sa.label) : x + 8 ≤ 2 ^ 64 := by
  simp only [wordAddr, Option.map_eq_some_iff] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  rw [mul_offset]
  have ho' : @LT.lt Nat instLTNat sa.offset (lsize sa.label) := ho
  have hh := hwf.inSpace Λ.heap (by simp [Layout.regions])
  have hd := hwf.inSpace Λ.data (by simp [Layout.regions])
  simp only [Range.InSpace] at hh hd
  rcases (h.lbl_range _ _ hb).2 with hs | hs | ⟨h0, hs⟩ <;> simp only [lrange, Range.Sub] at hs <;> omega

end MemRelP

/-- **`j` is the latest source message to `sa` that is not a promise** of
`sp`: every later message to `sa` is in `sp`. -/
def SLatestP (sm : WeakMem.Memory) (sp : List Nat) (sa : WeakMem.Address) (j : Nat) : Prop :=
  (∃ m, sm[j]? = some m ∧ m.loc = sa ∧ j ∉ sp) ∧ ∀ k m, j < k → sm[k]? = some m → m.loc = sa → k ∈ sp

/-- With no promise, `SLatestP` is `MemRel.SLatest`. -/
theorem SLatestP.nil_iff {sm : WeakMem.Memory} {sa : WeakMem.Address} {j : Nat} :
    SLatestP sm [] sa j ↔ MemRel.SLatest sm sa j := by
  constructor
  · rintro ⟨⟨m, hm, hl, -⟩, h2⟩
    exact ⟨⟨m, hm, hl⟩, fun k m hk hg hl => absurd (h2 k m hk hg hl) List.not_mem_nil⟩
  · rintro ⟨⟨m, hm, hl⟩, h2⟩
    exact ⟨⟨m, hm, hl, List.not_mem_nil⟩, fun k m hk hg hl => absurd hl (h2 k m hk hg)⟩

namespace MemRelP

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}

/-- **The read side with promises**: if `j` is the latest source message to
`sa` not promised (`SLatestP`), placed at the word `a`, and `k'` the latest
target write of `a` not promised (`TLatestP` over all the outstanding
target promises, `tp ++ tq`), then `j`'s image is `k'`, and the word the target reads there
represents `j`'s value. Whether the source may read `j` (no later promise
hides it under its read bound) is the view relation's business. -/
theorem latestP (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) (hn : MemRel.Narrow tm)
    {sa : WeakMem.Address} {a j k' : Nat} (ha : wordAddr lbl sa = some a) (hj : SLatestP sm sp sa j)
    (hk : TLatestP tm (tp ++ tq) a k') :
    ts j = some k' ∧ ∃ m v, sm[j]? = some m ∧ wordAt tm a k' = some v ∧ ValRep lbl m.val v := by
  obtain ⟨⟨m, hm, hml, hjp⟩, hjl⟩ := hj
  obtain ⟨kj, a', v, hts, ha', hw, hv⟩ := h.mem_rep j m hm
  rw [hml, ha] at ha'; cases ha'
  have hoa : sa.offset < lsize sa.label := by
    obtain ⟨b, -, hb⟩ := h.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm)); rw [← hml]; exact hb
  have hal := h.addr_lt hwf ha hoa
  -- the image of `j` is at most `k'`: a later write there is a mirrored promise
  have hle : kj ≤ k' := by
    rcases Nat.eq_zero_or_pos kj with rfl | hpos
    · exact Nat.zero_le _
    · obtain ⟨w, hg, hwl, -⟩ := MemRel.wordAt_msg hn hpos hw
      rcases Nat.lt_or_ge k' kj with hlt | hge
      · rcases List.mem_append.mp (hk.2 kj w hlt hg hwl) with hp | hq
        · exact absurd ((h.prom_corr j kj hts hpos).mpr hp) hjp
        · exact absurd hq (h.tq_img j kj hts)
      · exact hge
  have heq : kj = k' := by
    rcases hk.1 with rfl | ⟨w, hg, hwl, hkp⟩
    · omega
    · have hkpos : 0 < k' := by
        rcases Nat.eq_zero_or_pos k' with rfl | hp
        · simp [Memory.get?] at hg
        · exact hp
      have hin : ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains w.loc.addr.toNat := by
        simp only [wordAddr, Option.map_eq_some_iff] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        refine ⟨sa.label, b, hb, ?_⟩
        rw [hwl]
        simp only [lrange, Range.contains, wordLoc, BitVec.toNat_ofNat, mul_offset]
        have ho' : @LT.lt Nat instLTNat sa.offset (lsize sa.label) := hoa
        rw [mul_offset] at hal
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      obtain ⟨k2, hk2, ht2⟩ := (h.mem_onto k' w hg hin).resolve_right
        fun hq => hkp (List.mem_append_right _ hq)
      obtain ⟨m2, hm2⟩ : ∃ m2, sm[k2]? = some m2 := ⟨_, Array.getElem?_eq_getElem hk2⟩
      obtain ⟨k2', x, v2, ht2', hx, hw2, -⟩ := h.mem_rep k2 m2 hm2
      rw [ht2] at ht2'; cases ht2'
      obtain ⟨w', hg', hwl', -⟩ := MemRel.wordAt_msg hn hkpos hw2
      rw [hg] at hg'; cases hg'
      have ho2 : m2.loc.offset < lsize m2.loc.label := by
        obtain ⟨b, -, hb⟩ := h.lbl_mem m2 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm2)); exact hb
      have hxl := h.addr_lt hwf hx ho2
      have hxa : x = a := MemRel.wordLoc_inj (by omega) (by omega) (hwl'.symm.trans hwl)
      subst hxa
      have hloc : m2.loc = sa := h.wordAddr_inj hx ha ho2 hoa
      rcases Nat.lt_trichotomy k2 j with hlt | rfl | hgt
      · rcases Nat.eq_zero_or_pos kj with rfl | hpos
        · exact absurd hloc (by rw [← hml]; exact h.ts_first j m hm hts k2 m2 hlt hm2)
        · have := h.ts_mono k2 j k' kj m2 m hm2 hm (hloc.trans hml.symm) ht2 hts hkpos hpos hlt
          omega
      · rw [hts] at ht2; cases ht2; rfl
      · exact absurd (List.mem_append_left _ ((h.prom_corr k2 k' ht2 hkpos).mp (hjl k2 m2 hgt hm2 hloc))) hkp
  subst heq
  exact ⟨hts, m, v, hm, hw, hv⟩

/-- **What the target reads is what the source's latest unpromised message
holds** (`MemRel.latest_read` with promises). -/
theorem latestP_read (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) (hn : MemRel.Narrow tm)
    {sa : WeakMem.Address} {a j k' : Nat} (ha : wordAddr lbl sa = some a) (hj : SLatestP sm sp sa j)
    (hk : TLatestP tm (tp ++ tq) a k') {val : Val} (hr : tm.read? (wordLoc a) k' = some val) :
    ∃ m, sm[j]? = some m ∧ ValRep lbl m.val val.toNat := by
  obtain ⟨-, m, v, hm, hw, hv⟩ := h.latestP hwf hn ha hj hk
  rw [wordAt_of_read hr] at hw; cases hw
  exact ⟨m, hm, hv⟩

end MemRelP

/-- **`Components` from the memory relation with promises**, for a witness
with no source epochs whose target epochs start at or after every unmirrored
promise (`htf`; `w.tsFrom l = t.1.mem.last` always qualifies): the
per-location order is `ts_mono`; a target write in a live label's range
after `tsFrom` is an image (`mem_onto`, it is not in `tq`); one at or before
it is an image or an unmirrored promise, which is outstanding in its
writer's `prom` (`htq`), as `pre_alloc` asks. -/
theorem Components.ofMemRelP {M : ExtMachine} {Λ : Layout} {w : Witness M} {t : M.Cfg} {s : TermRun.Cfg}
    {tp tq sp : List Nat} (hm : MemRelP Λ w.lbl w.lsize w.ts t.1.mem s.mem tp tq sp) (hr : CompRest M Λ w t s)
    (hs : ∀ l, w.since l = 0) (htf : ∀ l, ∀ q ∈ tq, q ≤ w.tsFrom l)
    (htq : ∀ q ∈ tq, ∀ m', t.1.mem.get? q = some m' → ∃ tt, t.1.threads[m'.tid]? = some tt ∧ q ∈ tt.prom) :
    Components M Λ w t s where
  thr_total := hr.thr_total
  thr_inj := hr.thr_inj
  thr_onto := hr.thr_onto
  lbl_static := hm.lbl_static
  lbl_range := hm.lbl_range
  env_rep := hr.env_rep
  env_total := hr.env_total
  stack_pool := hr.stack_pool
  stack_disj := hr.stack_disj
  stack_owned := hr.stack_owned
  stack_private := hr.stack_private
  stack_marked := hr.stack_marked
  stack_unmarked := hr.stack_unmarked
  env_imm := hr.env_imm
  lbl_disj l l' b b' hne _ _ := hm.lbl_disj l l' b b' hne
  lbl_mem m hmm _ := hm.lbl_mem m hmm
  epoch_fixed _ l := hs l
  mem_rep k m hmm _ _ := hm.mem_rep k m hmm
  ts_first k m hmm _ h0 := ⟨hs _, hm.ts_first k m hmm h0⟩
  ts_mono k1 k2 k1' k2' m1 m2 hm1 hm2 hloc _ _ h1 h2 p1 p2 hlt :=
    hm.ts_mono k1 k2 k1' k2' m1 m2 hm1 hm2 hloc h1 h2 p1 p2 hlt
  mem_onto k' m' hg := fun ⟨l, b, _, hb, hlt, hc⟩ =>
    .inl ((hm.mem_onto k' m' hg ⟨l, b, hb, hc⟩).resolve_right fun hq => by
      have := htf l k' hq; omega)
  pre_alloc _ k' m' hg := fun ⟨l, b, _, hb, _, hc⟩ =>
    (hm.mem_onto k' m' hg ⟨l, b, hb, hc⟩).imp_right fun hq => htq k' hq m' hg

end Scc.Sem
