/-
Adequacy of the SLR-adapted resource model at final configurations (SLR
Lemmas 26/27, item O9).

Theorem 1′ (`SLR.Theorem1II`) concludes, at every reachable live
configuration, full erasure of a virtual configuration with postconditions
for the done threads; at a final configuration the virtual configuration is
the real one (`VirtualRel.eq_of_final`). This file turns such a conclusion
into statements about the machine.

## Contents

- `Res.Sub`: the resource order `a ≼ b` (`b = a • c`), with what it gives on
  fractions, write sets and validity; `threadsRes_sub_pair`,
  `slotsRes_sub`, `Erase.sub_*`: components of the total resource.
- `Erase.q_add_le_one`, `Erase.unique_holder`: **at most one holder** of a
  full write permission (threads and message slots).
- `Config.final_not_outstanding`, `fulf_iff_of_final`,
  `Erase.X_iff_of_final`: at a final configuration every message is settled,
  so the write set of a tracked location is its whole history.
- `Memory.finalVal_of_max`, `Erase.finalVal_of_max`: **confrontation**: the
  element of maximal timestamp of the total write set gives the final value;
  `Erase.X_total_cases`: the total write set is the union of the components'.
- `Erase.init`: **initial erasure** at `Config.init` from conditions on the
  initial ghost state.
- `Spinlock`: the adequacy of the spinlock counter proof (`Spinlock.adequacy`:
  `counter = n` at final configurations, token counting).
-/
import Kraken.Promising.SLR.Theorem1
import Kraken.Promising.SLR.Theorem1Proof

namespace Kraken.Promising.SLR

variable {I : ISA}

/-! ## The resource order -/

/-- `a ≼ b`: `b` is `a` composed with some frame. -/
def Res.Sub (a b : Res) : Prop := ∃ c, b = a.op c

namespace Res.Sub

theorem refl (a : Res) : a.Sub a := ⟨Res.unit, (Res.op_unit a).symm⟩

theorem trans {a b c : Res} (h₁ : a.Sub b) (h₂ : b.Sub c) : a.Sub c := by
  obtain ⟨d, rfl⟩ := h₁
  obtain ⟨e, rfl⟩ := h₂
  exact ⟨d.op e, Res.op_assoc _ _ _⟩

theorem op_left {a b : Res} (c : Res) (h : a.Sub b) : a.Sub (c.op b) := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨c.op d, by rw [Res.op_left_comm]⟩

theorem op_right {a b : Res} (c : Res) (h : a.Sub b) : a.Sub (b.op c) := by
  rw [Res.op_comm]; exact op_left c h

theorem op_mono {a b a' b' : Res} (h : a.Sub b) (h' : a'.Sub b') : (a.op a').Sub (b.op b') := by
  obtain ⟨d, rfl⟩ := h
  obtain ⟨e, rfl⟩ := h'
  refine ⟨d.op e, ?_⟩
  rw [Res.op_assoc, Res.op_left_comm d, ← Res.op_assoc, ← Res.op_assoc, Res.op_assoc (a.op a')]

theorem q_le {a b : Res} (h : a.Sub b) (x : Loc) : (a.wr x).q ≤ (b.wr x).q := by
  obtain ⟨d, rfl⟩ := h
  exact Perm.le_op_left _ _

theorem X {a b : Res} (h : a.Sub b) {x : Loc} {p : Val × Time} (hp : (a.wr x).X p) : (b.wr x).X p := by
  obtain ⟨d, rfl⟩ := h
  exact .inl hp

theorem valid {a b : Res} (h : a.Sub b) (hb : b.valid) : a.valid := by
  obtain ⟨d, rfl⟩ := h
  exact Res.valid_op_left hb

end Res.Sub

theorem Res.sub_prod_of_mem {rs : List Res} {r : Res} (hr : r ∈ rs) : r.Sub (Res.prod rs) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hr
  refine ⟨Res.prod (s ++ t), ?_⟩
  rw [Res.prod_perm (List.perm_middle), Res.prod_cons]

/-- The write set of a product is the union of the components'. -/
theorem Res.X_prod_iff {rs : List Res} {x : Loc} {p : Val × Time} :
    ((Res.prod rs).wr x).X p ↔ ∃ r ∈ rs, (r.wr x).X p := by
  induction rs with
  | nil => simp [Res.prod, Res.unit, Perm.unit]
  | cons s rs ih =>
    rw [Res.prod_cons]
    show (s.wr x).X p ∨ ((Res.prod rs).wr x).X p ↔ _
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- Two distinct threads' resources compose below the threads' product. -/
theorem threadsRes_sub_pair (rF : Nat → Res) {n i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ((rF i).op (rF j)).Sub (threadsRes rF n) := by
  have hi' : i ∈ List.range n := List.mem_range.mpr hi
  have hj' : j ∈ (List.range n).erase i := (List.mem_erase_of_ne (Ne.symm hij)).mpr (List.mem_range.mpr hj)
  have hp := (List.perm_cons_erase hi').trans (List.Perm.cons _ (List.perm_cons_erase hj'))
  refine ⟨Res.prod ((((List.range n).erase i).erase j).map rF), ?_⟩
  unfold threadsRes
  rw [Res.prod_perm (hp.map rF)]
  simp only [List.map_cons, Res.prod_cons, Res.op_assoc]

theorem threadsRes_sub (rF : Nat → Res) {n i : Nat} (hi : i < n) : (rF i).Sub (threadsRes rF n) :=
  Res.sub_prod_of_mem (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem slotsRes_sub {g : Ghost} {s : Slot} (hs : s ∈ g.u) : s.res.Sub g.slotsRes :=
  Res.sub_prod_of_mem (List.mem_map.mpr ⟨s, hs, rfl⟩)

/-! ## Components of the total resource -/

/-- Two distinct slots' resources compose below the slots' product. -/
theorem slotsRes_sub_pair {g : Ghost} {s s' : Slot} (hs : s ∈ g.u) (hs' : s' ∈ g.u) (hne : s' ≠ s) :
    (s.res.op s'.res).Sub g.slotsRes := by
  classical
  have hs'' : s' ∈ g.u.erase s := (List.mem_erase_of_ne hne).mpr hs'
  have hp := (List.perm_cons_erase hs).trans (List.Perm.cons _ (List.perm_cons_erase hs''))
  refine ⟨Res.prod (((g.u.erase s).erase s').map (·.res)), ?_⟩
  unfold Ghost.slotsRes
  rw [Res.prod_perm (hp.map _)]
  simp only [List.map_cons, Res.prod_cons, Res.op_assoc]

/-- The threads' fractions of `x` add up. -/
theorem q_threadsRes (rF : Nat → Res) (n : Nat) (x : Loc) :
    ((threadsRes rF n).wr x).q = ((List.range n).map fun j => ((rF j).wr x).q).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold threadsRes at ih ⊢
    rw [List.range_succ, List.map_append, Res.prod_append, List.map_append, List.sum_append, ← ih]
    simp only [List.map_cons, List.map_nil, Res.prod_cons, Res.prod_nil, List.sum_cons, List.sum_nil]
    show _ + (_ + 0) = _ + (_ + 0)
    rfl

theorem sum_range_const (n : Nat) (q : Rat) : ((List.range n).map fun _ => q).sum = n * q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    grind

/-- A sum over a range of terms each at least `q` is at least `n * q`. -/
theorem sum_range_ge (n : Nat) (q : Rat) (f : Nat → Rat) (h : ∀ j < n, q ≤ f j) :
    n * q ≤ ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h1 := ih fun j hj => h j (by omega)
    have h2 := h n (by omega)
    grind

section Components

variable {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

theorem q_total (x : Loc) :
    ((total rF g c).wr x).q = ((threadsRes rF c.threads.size).wr x).q + (g.slotsRes.wr x).q := rfl

/-- Two distinct slots' fractions of `x` add up to at most `1`. -/
theorem Erase.q_add_le_one_slots (E : Erase rF g T c) {s s' : Slot} (hs : s ∈ g.u) (hs' : s' ∈ g.u)
    (hne : s' ≠ s) (x : Loc) : (s.res.wr x).q + (s'.res.wr x).q ≤ 1 :=
  ((((slotsRes_sub_pair hs hs' hne).op_left (threadsRes rF c.threads.size))).valid E.valid).1 x

theorem sub_total_thread {i : Nat} (hi : i < c.threads.size) : (rF i).Sub (total rF g c) :=
  (threadsRes_sub rF hi).op_right _

theorem sub_total_slot {s : Slot} (hs : s ∈ g.u) : s.res.Sub (total rF g c) :=
  (slotsRes_sub hs).op_left _

theorem sub_total_pair {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j) :
    ((rF i).op (rF j)).Sub (total rF g c) :=
  (threadsRes_sub_pair rF hi hj hij).op_right _

theorem sub_total_thread_slot {i : Nat} {s : Slot} (hi : i < c.threads.size) (hs : s ∈ g.u) :
    ((rF i).op s.res).Sub (total rF g c) :=
  Res.Sub.op_mono (threadsRes_sub rF hi) (slotsRes_sub hs)

/-- The total write set is the union of the threads' and the slots'. -/
theorem X_total_cases {x : Loc} {p : Val × Time} (h : ((total rF g c).wr x).X p) :
    (∃ i < c.threads.size, ((rF i).wr x).X p) ∨ ∃ s ∈ g.u, (s.res.wr x).X p := by
  rcases h with h | h
  · obtain ⟨r, hr, hp⟩ := Res.X_prod_iff.mp h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact .inl ⟨i, List.mem_range.mp hi, hp⟩
  · obtain ⟨r, hr, hp⟩ := Res.X_prod_iff.mp h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact .inr ⟨s, hs, hp⟩

/-! ## At most one holder of a full permission -/

theorem Erase.q_le_one (E : Erase rF g T c) (x : Loc) : ((total rF g c).wr x).q ≤ 1 := E.valid.1 x

/-- Two distinct threads' fractions of `x` add up to at most `1`. -/
theorem Erase.q_add_le_one (E : Erase rF g T c) {i j : Nat} (hi : i < c.threads.size)
    (hj : j < c.threads.size) (hij : i ≠ j) (x : Loc) : ((rF i).wr x).q + ((rF j).wr x).q ≤ 1 :=
  ((sub_total_pair (g := g) hi hj hij).valid E.valid).1 x

/-- A thread's and a slot's fractions of `x` add up to at most `1`. -/
theorem Erase.q_add_le_one_slot (E : Erase rF g T c) {i : Nat} {s : Slot} (hi : i < c.threads.size)
    (hs : s ∈ g.u) (x : Loc) : ((rF i).wr x).q + (s.res.wr x).q ≤ 1 :=
  ((sub_total_thread_slot (g := g) hi hs).valid E.valid).1 x

private theorem q_zero_of_add_le {a b : Perm} (ha : a.q = 1) (h : a.q + b.q ≤ 1) : b.q = 0 := by
  have := b.nonneg; grind

/-- **At most one holder** (SLR Lemma 27's mutual exclusion, resource
level): if thread `i` holds a full write permission for `x`, no other thread
and no message slot holds any. -/
theorem Erase.unique_holder (E : Erase rF g T c) {i : Nat} (hi : i < c.threads.size) {x : Loc}
    (h1 : ((rF i).wr x).q = 1) :
    (∀ j < c.threads.size, j ≠ i → ((rF j).wr x).q = 0) ∧ ∀ s ∈ g.u, (s.res.wr x).q = 0 :=
  ⟨fun _ hj hji => q_zero_of_add_le h1 (E.q_add_le_one hi hj (Ne.symm hji) x),
    fun _ hs => q_zero_of_add_le h1 (E.q_add_le_one_slot hi hs x)⟩

/-- A slot holding a full write permission for `x` excludes every thread
and every other slot from `x`. -/
theorem Erase.unique_holder_slot (E : Erase rF g T c) {s : Slot} (hs : s ∈ g.u) {x : Loc}
    (h1 : (s.res.wr x).q = 1) : ∀ i < c.threads.size, ((rF i).wr x).q = 0 := by
  intro i hi
  have h := E.q_add_le_one_slot hi hs x
  have := ((rF i).wr x).nonneg; grind

end Components

/-! ## Final configurations -/

theorem Config.final_prom {c : Config I} (hf : c.final = true) {i : Nat} {t : Thread I}
    (ht : c.threads[i]? = some t) : t.prom = [] := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
  have := (Array.all_eq_true.mp hf) i hi
  simp only [Bool.and_eq_true, List.isEmpty_iff] at this
  exact this.2

theorem Config.final_halted {c : Config I} (hf : c.final = true) {i : Nat} {t : Thread I}
    (ht : c.threads[i]? = some t) : t.halted = true := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
  have := (Array.all_eq_true.mp hf) i hi
  simp only [Bool.and_eq_true] at this
  exact this.1

/-- In a final configuration every thread is done. -/
theorem Config.final_done {c : Config I} (hf : c.final = true) {i : Nat} (hi : i < c.threads.size) :
    c.Done i :=
  ⟨c.threads[i], Array.getElem?_eq_getElem hi, Config.final_halted hf (Array.getElem?_eq_getElem hi),
    Config.final_prom hf (Array.getElem?_eq_getElem hi)⟩

theorem Config.final_not_outstanding {c : Config I} (hf : c.final = true) (ts : Time) : ¬ Outstanding c ts := by
  rintro ⟨i, t, ht, hts⟩
  rw [Config.final_prom hf ht] at hts
  cases hts

/-- At a final configuration `Fulf` is the memory's history of `x`. -/
theorem fulf_iff_of_final {c : Config I} (hf : c.final = true) (g : Ghost) (x : Loc) (p : Val × Time) :
    Fulf c g x p ↔ c.mem.read? x p.2 = some p.1 := by
  unfold Fulf Memory.read?
  constructor
  · rintro (⟨h0, h1⟩ | ⟨w, hw, hl, hv, -⟩)
    · rw [ite_eq_left h0, h1]
    · have h0 : p.2 ≠ 0 := by rintro h; rw [h, c.mem.get?_zero] at hw; cases hw
      rw [ite_eq_right h0, hw]; simp [hl, hv]
  · intro h
    by_cases h0 : p.2 = 0
    · rw [ite_eq_left h0] at h; exact .inl ⟨h0, (Option.some.inj h).symm⟩
    · rw [ite_eq_right h0] at h
      split at h
      · next w hw =>
        split at h
        · next hl =>
          exact .inr ⟨w, hw, by simpa using hl, Option.some.inj h, .inl (Config.final_not_outstanding hf _)⟩
        · cases h
      · cases h

/-- At a final configuration the total write set of a tracked location is its
whole history. -/
theorem Erase.X_iff_of_final {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (E : Erase rF g T c) (hf : c.final = true) {x : Loc} (hq : 0 < ((total rF g c).wr x).q)
    (p : Val × Time) : ((total rF g c).wr x).X p ↔ c.mem.read? x p.2 = some p.1 := by
  rw [E.writes x (.inl hq) p, fulf_iff_of_final hf]

/-- A timestamp that reads `x` is at most `x`'s last write. -/
theorem Memory.le_lastWrite_of_read? {m : Memory} {x : Loc} {ts : Time} {v : Val} (h : m.read? x ts = some v) :
    ts ≤ m.lastWrite x := by
  refine Nat.le_of_not_lt fun hlt => ?_
  unfold Memory.read? at h
  have h0 : ts ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
  rw [ite_eq_right h0] at h
  split at h
  · next w hw =>
    split at h
    · next hl => exact m.not_write_of_lastWrite_lt x hlt hw (by simpa using hl)
    · cases h
  · cases h

/-- **The final value is the value at the maximal timestamp**: if `x` reads
`v` at `ts` and at no later timestamp, `v` is `x`'s final value. -/
theorem Memory.finalVal_of_max {m : Memory} {x : Loc} {ts : Time} {v : Val} (h : m.read? x ts = some v)
    (hmax : ∀ ts' v', m.read? x ts' = some v' → ts' ≤ ts) : m.finalVal x = v := by
  have h1 := Memory.le_lastWrite_of_read? h
  have h2 := hmax _ _ (m.read?_lastWrite x)
  have : ts = m.lastWrite x := Nat.le_antisymm h1 h2
  subst this
  rw [m.read?_lastWrite x] at h
  exact Option.some.inj h

/-- **Confrontation** (SLR Lemma 26): at a final configuration, the element
of maximal timestamp of the total write set of a tracked location carries its
final value. -/
theorem Erase.finalVal_of_max {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (E : Erase rF g T c) (hf : c.final = true) {x : Loc} (hq : 0 < ((total rF g c).wr x).q)
    {v : Val} {ts : Time} (hX : ((total rF g c).wr x).X (v, ts))
    (hmax : ∀ p, ((total rF g c).wr x).X p → p.2 ≤ ts) : c.mem.finalVal x = v :=
  Memory.finalVal_of_max ((E.X_iff_of_final hf hq _).mp hX)
    fun ts' v' h => hmax (v', ts') ((E.X_iff_of_final hf hq _).mpr h)

/-- At a final configuration, the final value and last write of a tracked
location are in its total write set. -/
theorem Erase.X_last_of_final {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (E : Erase rF g T c) (hf : c.final = true) {x : Loc} (hq : 0 < ((total rF g c).wr x).q) :
    ((total rF g c).wr x).X (c.mem.finalVal x, c.mem.lastWrite x) :=
  (E.X_iff_of_final hf hq _).mpr (c.mem.read?_lastWrite x)

/-! ## Initial erasure -/

section Init

variable {states : List I.State} {initMem : List (Loc × Val)}

theorem Config.init_prom {i : Nat} {t : Thread I} (ht : (Config.init states initMem).threads[i]? = some t) :
    t.prom = [] := by
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
  obtain ⟨st, -, rfl⟩ := ht
  rfl

/-- A thread of the initial configuration is the initial thread of its
state. -/
theorem Config.init_get?_thread {i : Nat} {t : Thread I}
    (h : (Config.init states initMem : Config I).threads[i]? = some t) :
    ∃ s, states[i]? = some s ∧ t = Thread.init s := by
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  exact ⟨s, hs, rfl⟩

theorem Config.init_not_outstanding (ts : Time) : ¬ Outstanding (Config.init states initMem) ts := by
  rintro ⟨i, t, ht, hts⟩
  rw [Config.init_prom ht] at hts
  cases hts

theorem Config.init_get? (ts : Time) : (Config.init states initMem).mem.get? ts = none := by
  simp [Config.init, Memory.get?]

theorem Config.init_read? {x : Loc} {ts : Time} {v : Val}
    (h : (Config.init states initMem).mem.read? x ts = some v) :
    ts = 0 ∧ v = (Config.init states initMem).mem.initVal x := by
  unfold Memory.read? at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · rw [Config.init_get?] at h; cases h

/-- **Initial erasure**: erasure at `Config.init` (no message beyond the
initial ones, no promise) from conditions on the initial ghost state: release
messages and slots only at initial messages, nothing pending or claimed, the
write set of a tracked location the initial message alone, the relaxed
initial messages pure and every slot satisfying its predicate at the initial
value. -/
theorem Erase.init {rF : Nat → Res} {g : Ghost} {T : Nat → Prop}
    (hvalid : (total rF g (Config.init states initMem)).valid)
    (hslotIds : ∀ s ∈ g.u, s.id < g.acqTab.length)
    (hacqIds : ∀ x ι, 1 ≤ (total rF g (Config.init states initMem)).acq x ι → ι < g.acqTab.length)
    (hrelAcq : ∀ x v m V r, (g.rel x).P v m V r →
      Pred.SepList (g.acqPreds (total rF g (Config.init states initMem)).acq x ++ g.updPreds x) v m V r)
    (hwrites : ∀ x, 0 < ((total rF g (Config.init states initMem)).wr x).q → ∀ p,
      ((total rF g (Config.init states initMem)).wr x).X p ↔
        p = ((Config.init states initMem).mem.initVal x, 0))
    (hpure : ∀ x, (x, 0) ∉ g.relMsgs → Pred.Pure (g.rel x) ((Config.init states initMem).mem.initVal x))
    (hrel : ∀ k ∈ g.relMsgs, k.2 = 0)
    (hslotsNodup : (g.u.map fun s => (s.key, s.id)).Nodup)
    (hslotsDom : ∀ k ι, (∃ s ∈ g.u, s.key = k ∧ s.id = ι) ↔
      (k ∈ g.relMsgs ∧ ((total rF g (Config.init states initMem)).acq k.1 ι = 1 ∨ ι ∈ g.upd k.1)))
    (hslotsPred : ∀ s ∈ g.u, (g.acqPred s.id).P ((Config.init states initMem).mem.initVal s.key.1)
      (Config.init states initMem).mem 0 s.res)
    (hupdIds : ∀ x, (g.upd x).Nodup ∧ ∀ ι ∈ g.upd x, ι < g.acqTab.length ∧
      (total rF g (Config.init states initMem)).acq x ι = 0)
    (hpend : g.pend = []) (hclaims : g.claims = []) :
    Erase rF g T (Config.init states initMem) where
  valid := hvalid
  slotIds := hslotIds
  acqIds := hacqIds
  relAcq := hrelAcq
  writes := by
    intro x hx p
    have hq : 0 < ((total rF g (Config.init states initMem)).wr x).q := by
      rcases hx with h | ⟨ts, w, hw, -⟩
      · exact h
      · rw [Config.init_get?] at hw; cases hw
    rw [hwrites x hq p]
    unfold Fulf
    constructor
    · rintro rfl; exact .inl ⟨rfl, rfl⟩
    · rintro (⟨h0, h1⟩ | ⟨w, hw, -⟩)
      · obtain ⟨v, ts⟩ := p; simp only at h0 h1; rw [h0, h1]
      · rw [Config.init_get?] at hw; cases hw
  pure := by
    intro x ts v hv hnot
    obtain ⟨rfl, rfl⟩ := Config.init_read? hv
    exact hpure x hnot
  relExists := by
    intro k hk
    refine ⟨(Config.init states initMem).mem.initVal k.1, ?_⟩
    rw [hrel k hk]
    rfl
  slotsNodup := hslotsNodup
  slotsDom := by
    intro k ι
    rw [hslotsDom]
    simp [Ghost.Claimed, hclaims]
  slotsPred := by
    intro s hs v hv
    obtain ⟨h0, rfl⟩ := Config.init_read? hv
    rw [h0]
    exact hslotsPred s hs
  promWf := by
    intro i t ht ts hts
    rw [Config.init_prom ht] at hts; cases hts
  promValid := by
    intro i t ht _ ts hts
    rw [Config.init_prom ht] at hts; cases hts
  pend := by
    intro ts hts
    rw [hpend] at hts; cases hts
  updIds := hupdIds
  relSettled := fun k _ => .inl (Config.init_not_outstanding k.2)
  claimsNodup := by rw [hclaims]; exact List.nodup_nil
  claimsAt := by
    intro k tw hk
    rw [hclaims] at hk; cases hk
  claimFulf := by
    intro k tw hk
    rw [hclaims] at hk; cases hk

end Init

/-! ## The spinlock counter (SLR Lemma 26, token counting) -/

/-- Machine steps keep the number of threads. -/
theorem Reachable.size_eq {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') : c'.threads.size = c.threads.size := by
  induction h with
  | refl => rfl
  | step hs _ ih =>
    rw [ih]
    cases succs_cases hs with
    | instr _ _ _ => exact Config.withThread_size _ _ _ _
    | promise _ _ => exact Config.withThread_size _ _ _ _

theorem Config.init_size (states : List I.State) (initMem : List (Loc × Val)) :
    (Config.init states initMem).threads.size = states.length := by
  simp [Config.init]

/-- Allocated acquire predicates keep their meaning in a larger world. -/
theorem Ghost.acqPred_of_prefix {g g' : Ghost} (h : g.acqTab <+: g'.acqTab) {ι : PredId}
    (hι : ι < g.acqTab.length) : g'.acqPred ι = g.acqPred ι := by
  unfold Ghost.acqPred
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hι,
    List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hι h.length_le), h.getElem hι]

/-- A list of distinct numbers below `N` of length at least `N` contains
every number below `N`. -/
theorem pigeonhole {l : List Nat} {N : Nat} (hnd : l.Nodup) (hlt : ∀ j ∈ l, j < N) (hlen : N ≤ l.length) :
    ∀ j < N, j ∈ l := by
  intro j hj
  refine Classical.byContradiction fun hn => ?_
  have hsub : l ⊆ (List.range N).erase j := fun a ha =>
    (List.mem_erase_of_ne (fun h => hn (by rw [← h]; exact ha))).mpr (List.mem_range.mpr (hlt a ha))
  have := hnd.length_le_of_subset hsub
  rw [List.length_erase_of_mem (List.mem_range.mpr hj), List.length_range] at this
  omega

private theorem read?_of_get? {m : Memory} {ts : Time} {w : Msg} (hw : m.get? ts = some w) :
    m.read? w.loc ts = some w.val := by
  have h0 : ts ≠ 0 := by rintro rfl; rw [m.get?_zero] at hw; cases hw
  unfold Memory.read?
  rw [ite_eq_right h0, hw]
  simp

/-! ## Program-agnostic adequacy -/

/-- **Adequacy from Theorem 1′'s conclusion** (the program-agnostic step of
SLR Lemma 26): at a final configuration `c` reachable from `Config.init
states initMem`, Theorem 1′'s virtual configuration is `c` itself, so the
final postcondition `Φ` holds of `c` as soon as it follows (`hfin`) from
clean erasure at `c` for some thread resources `rF'` and world `g' ≥ g₀`,
the thread count, and the per-thread postcondition `B` of every halted
thread. -/
theorem final_of_virtual [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State} {initMem : List (Loc × Val)}
    {B : Config I → Res → Ghost → Prop} {g₀ : Ghost} {Φ : Config I → Prop} {c : Config I}
    (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hT : ∃ v rF' g', (VirtualRel.ii A).rel c v ∧ Erase rF' g' (fun _ => False) v ∧ g₀.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g')
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  obtain ⟨v, rF', g', hv, E', hle, hB⟩ := hT
  obtain rfl : v = c := (VirtualRel.ii A).eq_of_final c v hf hv
  exact hfin rF' g' E' hle (by rw [Reachable.size_eq hc, Config.init_size]) hB

/-- **Program-agnostic adequacy from Theorem 1′ under (O5)**
(`Theorem1IIPure`): if erasure holds initially (with no pending promise),
`PromisePure` holds for the initial ghost's release predicates and every
thread is non-promisingly safe (clean flag `True`) with the per-thread
postcondition `B`, then every final configuration reachable from the initial
one satisfies the final postcondition `Φ`, provided `Φ` follows from clean
erasure, a world above `g₀`, the thread count and `B` at every halted thread
(`hfin`). `Spinlock.counter_of_theorem1Pure` is the counter instance. -/
theorem final_of_theorem1Pure [I.LawfulState] {A : Arch} {fuel : Nat} (hT : Theorem1IIPure (I := I) A fuel)
    {states : List I.State} {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost}
    {B : Config I → Res → Ghost → Prop} {Φ : Config I → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (hpure : PromisePure A fuel states initMem g₀.rel)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_virtual hc hf (hT B states initMem rF g₀ hH hE hpend hpure hsafe c hc ⟨c, .refl c, hf⟩) hfin

namespace Spinlock

/-- What the lock's acquire (and release) predicate `φ` says at the unlocked
value `0`: either (the *bad* disjunct) the resource carries a positive share
of the lock permission `Lk`, or the resource carries the full counter
permission, whose write set has its maximal element at value `k`, and a
token pool in which every thread `j` that has not incremented (`S j = false`)
leaves a positive fraction of its token location `K j`; `k` counts the
threads that have incremented.

The bad disjunct is how a thread pays for a release after a step from a
configuration without full erasure (`NPSafe`'s clean flag false), where the
counter value it read may be a foreign promise: it gives away part of its
lock share, so its postcondition (asked only of clean threads) fails, and at
a final configuration, where every thread holds its share `1/N`, no slot can
hold a share (validity). -/
def PoolSpec (N : Nat) (Lk C : Loc) (K : Nat → Loc) (φ : Pred) : Prop :=
  ∀ m V r, φ.P 0 m V r → 0 < (r.wr Lk).q ∨ ∃ (k : Nat) (S : Nat → Bool) (ts : Time),
    (r.wr C).q = 1 ∧ (r.wr C).X (BitVec.ofNat 128 k, ts) ∧ (∀ p, (r.wr C).X p → p.2 ≤ ts) ∧
    k = ((List.range N).filter S).length ∧ ∀ j < N, S j = false → 0 < (r.wr (K j)).q

/-- The postcondition of every worker (`NPSafe`'s `B`, the same for every
thread): it holds the full token of some `j < N` (it has incremented), at
least its share `1/N` of the lock permission, and each non-zero (locking)
write in its write set of the lock is followed by a zero (unlocking) one.
(Lower bounds: validity makes them exact at a final configuration.) -/
def Post (N : Nat) (Lk : Loc) (K : Nat → Loc) (r : Res) : Prop :=
  (∃ j < N, 1 ≤ (r.wr (K j)).q) ∧ 1 / N ≤ (r.wr Lk).q ∧
    ∀ p, (r.wr Lk).X p → p.1 ≠ 0 → ∃ p', (r.wr Lk).X p' ∧ p'.1 = 0 ∧ p.2 < p'.2

/-- **Adequacy of the spinlock counter** (SLR Lemma 26 instance): at a final
configuration with full erasure, a world above `g₀` (in which the lock's
release predicate is `φ`, an update id `ι` of the lock has predicate `φ`) and
every thread's postcondition, the counter's final value is the number of
threads.

The argument: the threads hold the whole lock permission, so its write set
is theirs; its last message is an unlock (value `0`) by the postconditions;
it is a release message (`φ` is not pure at `0`) and unclaimed (it is the
last), so it carries the update slot `ι`, whose resource satisfies `φ`; that
slot holds no lock share (the threads hold it all), so it is the pool: it
holds the full counter permission, so the counter's write set is the
slot's and its maximal element `k` is the final value (confrontation); every
thread's full token excludes its pool fraction, the tokens are distinct
(validity), so every thread has incremented and `k = N`. -/
theorem adequacy {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {N : Nat}
    {Lk C : Loc} {K : Nat → Loc} {g₀ : Ghost} {φ : Pred} {ι : PredId}
    (E : Erase rF g T c) (hf : c.final = true) (hN : c.threads.size = N) (hN0 : 0 < N)
    (hle : g₀.Le g) (hrel : g₀.rel Lk = φ) (hupd : ι ∈ g₀.upd Lk) (hιlt : ι < g₀.acqTab.length)
    (hφ : g₀.acqPred ι = φ) (hspec : PoolSpec N Lk C K φ) (hpost : ∀ i < N, Post N Lk K (rF i)) :
    c.mem.finalVal C = BitVec.ofNat 128 N := by
  subst hN
  -- the threads hold the whole lock permission, the slots none of it
  have hsumL : 1 ≤ ((threadsRes rF c.threads.size).wr Lk).q := by
    rw [q_threadsRes]
    have h := sum_range_ge c.threads.size (1 / c.threads.size) _ fun j hj => (hpost j hj).2.1
    have : (c.threads.size : Rat) ≠ 0 := by
      have := Nat.pos_iff_ne_zero.mp hN0
      exact_mod_cast this
    grind
  have hslotL : (g.slotsRes.wr Lk).q = 0 := by
    have h1 := E.q_le_one Lk
    rw [q_total] at h1
    have := (g.slotsRes.wr Lk).nonneg
    grind
  have hsL : ∀ s ∈ g.u, ∀ p, ¬ (s.res.wr Lk).X p := fun s hs => (s.res.wr Lk).zero (by
    have h1 := (slotsRes_sub hs).q_le Lk
    have := (s.res.wr Lk).nonneg
    grind)
  have hqL : 0 < ((total rF g c).wr Lk).q := by
    rw [q_total, hslotL]; grind
  -- the lock's last message is an unlock
  have hX := E.X_last_of_final hf hqL
  have hlast0 : c.mem.finalVal Lk = 0 := by
    refine Classical.byContradiction fun hne => ?_
    rcases X_total_cases hX with ⟨i, hi, hXi⟩ | ⟨s, hs, hXs⟩
    · obtain ⟨p', hp', -, hlt⟩ := (hpost i hi).2.2 _ hXi hne
      have hp'' := (E.X_iff_of_final hf hqL p').mp ((sub_total_thread hi).X hp')
      exact absurd (Memory.le_lastWrite_of_read? hp'') (Nat.not_le.mpr hlt)
    · exact hsL s hs _ hXs
  have hread : c.mem.read? Lk (c.mem.lastWrite Lk) = some 0 := hlast0 ▸ c.mem.read?_lastWrite Lk
  -- it is a release message
  have hφg : g.rel Lk = φ := (congrFun hle.rel Lk).trans hrel
  have hnoC : ∀ m V, ¬ φ.P 0 m V Res.unit := by
    intro m V h
    rcases hspec m V _ h with hq | ⟨k, S, ts, hq, -⟩ <;> simp [Res.unit, Perm.unit] at hq
  have hrelmsg : (Lk, c.mem.lastWrite Lk) ∈ g.relMsgs := Classical.byContradiction fun hn =>
    hnoC c.mem 0 (hφg ▸ E.pure Lk _ 0 hread hn c.mem 0)
  -- it carries the update slot `ι`
  have hupd' : ι ∈ g.upd Lk := (hle.upd Lk).subset hupd
  have hunclaimed : ¬ g.Claimed (Lk, c.mem.lastWrite Lk) := by
    intro hc
    obtain ⟨⟨k, tw⟩, hk, hkeq⟩ := List.mem_map.mp hc
    simp only at hkeq
    subst hkeq
    obtain ⟨hlt, w, hw, hl, -, -⟩ := E.claimsAt _ tw hk
    exact absurd (Memory.le_lastWrite_of_read? (hl ▸ read?_of_get? hw)) (Nat.not_le.mpr hlt)
  obtain ⟨s, hs, hkey, hid⟩ := (E.slotsDom _ ι).mpr ⟨hrelmsg, .inr ⟨hupd', hunclaimed⟩⟩
  have hP := E.slotsPred s hs 0 (by rw [hkey]; exact hread)
  rw [hid, Ghost.acqPred_of_prefix hle.acqTab hιlt, hφ, hkey] at hP
  obtain ⟨k, S, ts, hq1, hXk, hmax, hk, hS⟩ := (hspec _ _ _ hP).resolve_left fun hq => by
    have h1 := (slotsRes_sub hs).q_le Lk
    rw [hslotL] at h1
    grind
  -- confrontation: the slot's maximal counter element is the final value
  have hqC : 0 < ((total rF g c).wr C).q := by
    have := (sub_total_slot (rF := rF) (c := c) hs).q_le C
    rw [hq1] at this
    grind
  have hthC := E.unique_holder_slot hs hq1
  have hfin : c.mem.finalVal C = BitVec.ofNat 128 k := by
    refine E.finalVal_of_max hf hqC ((sub_total_slot hs).X hXk) fun p hp => ?_
    rcases X_total_cases hp with ⟨i, hi, hXi⟩ | ⟨s', hs', hXs'⟩
    · exact absurd hXi (((rF i).wr C).zero (hthC i hi) p)
    · by_cases he : s' = s
      · subst he; exact hmax p hXs'
      · have h2 := E.q_add_le_one_slots hs hs' he C
        rw [hq1] at h2
        exact absurd hXs' ((s'.res.wr C).zero (by have := (s'.res.wr C).nonneg; grind) p)
  -- counting: every thread's token is distinct and excludes its pool share
  rw [hfin, hk]
  have hex : ∀ i, ∃ j, i < c.threads.size → j < c.threads.size ∧ 1 ≤ ((rF i).wr (K j)).q := fun i =>
    if hi : i < c.threads.size then
      match (hpost i hi).1 with
      | ⟨j, hj, h1⟩ => ⟨j, fun _ => ⟨hj, h1⟩⟩
    else ⟨0, fun h => absurd h hi⟩
  let f := fun i => Classical.choose (hex i)
  have hfj : ∀ i, i < c.threads.size → f i < c.threads.size ∧ 1 ≤ ((rF i).wr (K (f i))).q :=
    fun i => Classical.choose_spec (hex i)
  have hinj : ∀ i₁ ∈ List.range c.threads.size, ∀ i₂ ∈ List.range c.threads.size, f i₁ = f i₂ → i₁ = i₂ := by
    intro i₁ h₁ i₂ h₂ he
    have h₁' := List.mem_range.mp h₁
    have h₂' := List.mem_range.mp h₂
    refine Classical.byContradiction fun hne => ?_
    have := E.q_add_le_one h₁' h₂' hne (K (f i₁))
    have h1 := (hfj i₁ h₁').2
    have h2 := (hfj i₂ h₂').2
    rw [← he] at h2
    grind
  have hnd : ((List.range c.threads.size).map f).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact List.nodup_range.imp_of_mem fun ha hb hne he => hne (hinj _ ha _ hb he)
  have hall := pigeonhole hnd (by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    exact (hfj i (List.mem_range.mp hi)).1) (by simp)
  have hSall : ∀ j < c.threads.size, S j = true := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (hall j hj)
    have hi' := List.mem_range.mp hi
    refine Classical.byContradiction fun hn => ?_
    have hpos := hS _ hj (by simpa using hn)
    have := E.q_add_le_one_slot hi' hs (K (f i))
    have h1 := (hfj i hi').2
    grind
  rw [List.filter_eq_self.mpr (fun j hj => hSall j (List.mem_range.mp hj)), List.length_range]

/-- **`counter = n` from Theorem 1′ under (O5)** (`Theorem1IIPure`): if
erasure holds initially (with no pending promise), `PromisePure` holds for
the initial ghost's release predicates (for a program, from
`promisePure_of_cells`) and every worker is non-promisingly safe (clean flag
`True`) with postcondition `Post`, every final configuration reachable from
the initial one has counter value `N`, the number of threads: the counter
instance of `final_of_theorem1Pure`, with `adequacy` as `hfin`. -/
theorem counter_of_theorem1Pure [I.LawfulState] {A : Arch} {fuel : Nat} (hT : Theorem1IIPure (I := I) A fuel)
    {states : List I.State} {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {N : Nat}
    {Lk C : Loc} {K : Nat → Loc} {φ : Pred} {ι : PredId}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (hpure : PromisePure A fuel states initMem g₀.rel)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A (fun _ r _ => Post N Lk K r) tid n m True (Config.init states initMem) (rF tid) g₀)
    (hN : states.length = N) (hN0 : 0 < N) (hrel : g₀.rel Lk = φ) (hupd : ι ∈ g₀.upd Lk)
    (hιlt : ι < g₀.acqTab.length) (hφ : g₀.acqPred ι = φ) (hspec : PoolSpec N Lk C K φ)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true) :
    c.mem.finalVal C = BitVec.ofNat 128 N :=
  final_of_theorem1Pure (Φ := fun c => c.mem.finalVal C = BitVec.ofNat 128 N) hT hH hE hpend hpure hsafe hc hf
    fun _ _ E' hle hsize hB =>
      adequacy E' hf (hsize.trans hN) hN0 hle hrel hupd hιlt hφ hspec fun i hi =>
        hB i (Config.final_done hf (by rw [hsize, hN]; exact hi))

end Spinlock

end Kraken.Promising.SLR
