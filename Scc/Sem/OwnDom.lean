/-
**Every thread's private memory is its own** (`OwnDom`): along every run of
the kernel model's machine (`Kernel.hooks`), thread `tid`'s private memory
(`Abi.dmem`) maps exactly the addresses of its initial stack (`E tid`: the
entry state's stack for thread 0, nothing for the others, `initDom`) and of
the stack ranges it holds (`KState.held`), and every thread is in a
fragment `P` of the ISA's states. The held ranges are nonempty, inside the
stack pool and the address space, held by slots that are not dormant, and
pairwise disjoint; the initial stacks avoid the pool and the dormant slots.

What the ISA must give is `DomHyps`: on `P`, every leaf of an instruction
keeps `P` and the domain; a system-call return and a thread-pointer change
keep both; the child of a `clone` is in `P` with no private memory;
`setDmem` and `skip` keep `P`. The instances are `Scc.Cert.DomA64.domHyps`
and `Scc.Cert.DomX64.domHyps` (`P := WideSt`).

- `OwnDom.init`: the invariant at load time (`KState.init`), given the
  loaded threads' domains and the initial stack clear of the stack pool.
- `OwnDom.step`, `OwnDom.run`: every step and every run of the machine keeps
  it (per step: `stepSemC` for an instruction or promise, `take`,
  `release`, `spawn`, `sys`).
- `OwnDom.take_unmapped`, `OwnDom.release_mapped`: what the P1 lemmas
  `certSem_step_of_take` and `certSem_step_of_release` need of the private
  memory at a transfer (`hdom`): at a take no byte of the range is mapped,
  at a release every byte is.
- `Mem.mem_storeInt_of_loadInt`, `leaf_of_map`: ISA-neutral facts the
  instances use (a store after a load of the same bytes maps nothing new; a
  leaf of a mapped tree is the image of a leaf).
-/
import Scc.Sem.CertStep
open Std

/-- **A store to mapped bytes keeps the domain**: after a load of the same
bytes succeeds, `storeInt` maps exactly the addresses mapped before. -/
theorem Mem.mem_storeInt_of_loadInt {w} {m : Mem w} {a : BitVec w} {n : Nat} {v : Int} {i : Int}
    (h : Mem.loadInt m a n = some i) (k : BitVec w) : k ∈ Mem.storeInt m a n v ↔ k ∈ m := by
  by_cases hk : k ∈ (Int.toBytes n v).At a
  · have hm : k ∈ m := by
      obtain ⟨j, hj, rfl⟩ := (mem_At_iff _ _ _).mp hk
      rw [Int.toBytes_length] at hj
      simp only [Mem.loadInt, Mem.loadBytes, Option.map_eq_some_iff] at h
      obtain ⟨bs, hb, -⟩ := h
      have := (List.allSome_isSome_iff _).mp (by rw [hb]; rfl) (m.get? (a + .ofNat w j))
        (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      rw [ExtHashMap.mem_iff_isSome_getElem?]
      simpa [ExtHashMap.get?_eq_getElem?] using this
    refine ⟨fun _ => hm, fun _ => ?_⟩
    rw [ExtHashMap.mem_iff_isSome_getElem?]
    simp only [Mem.storeInt, Mem.storeBytes, ExtHashMap.union_eq, ExtHashMap.getElem?_union]
    rw [ExtHashMap.mem_iff_isSome_getElem?] at hk
    cases h2 : ((Int.toBytes n v).At a)[k]? <;> simp_all
  · have := Mem.get?_storeBytes_of_not_mem m a k (Int.toBytes n v) hk
    simp only [ExtHashMap.mem_iff_isSome_getElem?, ← ExtHashMap.get?_eq_getElem?]
    unfold Mem.storeInt
    rw [this]

namespace Scc.Sem.Kernel

open Kraken Kraken.Promising

/-- A leaf of a mapped tree is the image of a leaf. -/
theorem _root_.Scc.Sem.leaf_of_map {σ τ : Type} (f : σ → τ) :
    ∀ {t : EvTree σ} {y : τ}, TreeLeaf (t.map f) y → ∃ x, TreeLeaf t x ∧ y = f x
  | .done x, _, h => ⟨x, rfl, h⟩
  | .fault _, _, h => h.elim
  | .choose _ _, _, ⟨i, h⟩ => let ⟨x, hx, e⟩ := leaf_of_map f h; ⟨x, ⟨i, hx⟩, e⟩
  | .load _ _ _ _, _, ⟨i, h⟩ => let ⟨x, hx, e⟩ := leaf_of_map f h; ⟨x, ⟨i, hx⟩, e⟩
  | .store _ _ _ _ _, _, ⟨i, h⟩ => let ⟨x, hx, e⟩ := leaf_of_map f h; ⟨x, ⟨i, hx⟩, e⟩
  | .rmw _ _ _ _ _, _, ⟨i, h⟩ => let ⟨x, hx, e⟩ := leaf_of_map f h; ⟨x, ⟨i, hx⟩, e⟩
  | .fence _ _, _, ⟨i, h⟩ => let ⟨x, hx, e⟩ := leaf_of_map f h; ⟨x, ⟨i, hx⟩, e⟩

variable {I : ISA} {K : Abi I}

/-! ## Addresses of a range -/

/-- **The addresses of a range that does not wrap** are the 64-bit words whose
value is in it. -/
theorem mem_addrs_iff {r : Range} (hr : r.lo + r.size ≤ 2 ^ 64) (a : BitVec 64) :
    a ∈ addrs r ↔ r.contains a.toNat := by
  unfold addrs Range.contains
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    rw [List.mem_range] at hi
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro h
    refine List.mem_map.mpr ⟨a.toNat - r.lo, List.mem_range.mpr (by omega), ?_⟩
    rw [show r.lo + (a.toNat - r.lo) = a.toNat by omega, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mem_copyRange (src dst : _root_.Mem 64) (r : Range) (a : BitVec 64) :
    a ∈ copyRange src dst r ↔ a ∈ addrs r ∨ a ∈ dst := by
  simp only [Std.ExtHashMap.mem_iff_isSome_getElem?, copyRange, get_foldl_insert]
  split <;> simp_all

theorem mem_eraseRange (m : _root_.Mem 64) (r : Range) (a : BitVec 64) :
    a ∈ eraseRange m r ↔ a ∉ addrs r ∧ a ∈ m := by
  simp only [Std.ExtHashMap.mem_iff_isSome_getElem?, get_eraseRange]
  split <;> simp_all

/-! ## Slots -/

theorem set_slots_get (x : KState) (j k : Nat) (s : Slot) :
    (x.set j s).slots[k]? = if j = k ∧ j < x.slots.size then some s else x.slots[k]? := by
  simp only [KState.set, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h1 : j = k
  · subst h1
    by_cases h2 : j < x.slots.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem set_dormant {x : KState} {j k : Nat} {s : Slot} (hs : s ≠ .dormant)
    (h : (x.set j s).slots[k]? = some .dormant) : x.slots[k]? = some .dormant := by
  rw [set_slots_get] at h
  split at h
  · cases h; exact absurd rfl hs
  · exact h

theorem not_dormant_of_runs {x : KState} {tid : Nat} (h : x.runs tid = true) :
    x.slots[tid]? ≠ some .dormant := by
  unfold KState.runs at h
  intro hd
  rw [hd] at h
  cases h

/-! ## The domain invariant -/

/-- Address `a` lies in a range thread `tid` holds. -/
def HeldAt (held : List (Nat × Range)) (tid : Nat) (a : BitVec 64) : Prop :=
  ∃ r, (tid, r) ∈ held ∧ r.contains a.toNat

/-- **Every thread's private memory is its own**: thread `tid` maps exactly
the addresses of `E tid` (its initial stack, fixed at load) and of the stack
ranges it holds; every thread is in the fragment `P`; the held ranges are
nonempty, inside the pool, in the address space, held by slots that are
not dormant and pairwise disjoint; `E` is disjoint from the pool and empty
at the dormant slots. -/
structure OwnDom (K : Abi I) (E : Nat → BitVec 64 → Prop) (P : I.State → Prop) (c : Config I × KState) :
    Prop where
  dom : ∀ (tid : Nat) (t : Thread I), c.1.threads[tid]? = some t →
    ∀ a, a ∈ K.dmem t.st ↔ E tid a ∨ HeldAt c.2.held tid a
  frag : ∀ (tid : Nat) (t : Thread I), c.1.threads[tid]? = some t → P t.st
  held_ok : ∀ h ∈ c.2.held, 0 < h.2.size ∧ h.2.Sub c.2.pool ∧ h.2.lo + h.2.size ≤ 2 ^ 64
  held_live : ∀ h ∈ c.2.held, c.2.slots[h.1]? ≠ some .dormant
  held_disj : c.2.held.Pairwise fun h h' => h.2.Disjoint h'.2
  pool_E : ∀ j a, E j a → ¬ c.2.pool.contains a.toNat
  E_dorm : ∀ j a, c.2.slots[j]? = some .dormant → ¬ E j a

/-- **What the ISA must give**: on the fragment `P`, every leaf of an
instruction keeps `P` and the private memory's domain; a system-call return
and a thread-pointer change keep both; the child of a `clone` is in `P`
with no private memory; a range transfer keeps `P`. -/
structure DomHyps (K : Abi I) (P : I.State → Prop) : Prop where
  exec : ∀ s tree s', P s → I.exec s = some tree → TreeLeaf tree s' → P s' ∧ ∀ a, a ∈ K.dmem s' ↔ a ∈ K.dmem s
  ret : ∀ s r, P s → P (K.ret s r) ∧ K.dmem (K.ret s r) = K.dmem s
  setTp : ∀ s a, P s → P (K.setTp s a) ∧ K.dmem (K.setTp s a) = K.dmem s
  child : ∀ s st tls, P s → P (K.child s st tls) ∧ K.dmem (K.child s st tls) = ∅
  setDmem : ∀ s m, P s → P (K.setDmem s m)
  skip : ∀ s, P s → P (K.skip s)

variable {E : Nat → BitVec 64 → Prop} {P : I.State → Prop}

/-- Two held ranges are disjoint, unless they are the same entry. -/
theorem disj_of_erase {held : List (Nat × Range)} (hd : held.Pairwise fun h h' => h.2.Disjoint h'.2)
    (hp : ∀ h ∈ held, 0 < h.2.size) {x y : Nat × Range} (hx : x ∈ held) (hy : y ∈ held.erase x) :
    y.2.Disjoint x.2 := by
  induction held with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.pairwise_cons] at hd
    by_cases hzx : z = x
    · subst hzx
      rw [List.erase_cons_head] at hy
      have := hd.1 y hy; unfold Range.Disjoint at *; omega
    · rw [List.erase_cons_tail (by simpa using hzx)] at hy
      have hx' : x ∈ zs := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hzx
        · exact h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hd.1 x hx'
      · exact ih hd.2 (fun h hh => hp h (List.mem_cons_of_mem _ hh)) hx' hy


/-- **The initial stack's domain**: thread 0 maps the entry state's
initial stack, no other thread a stack of its own. -/
def initDom (Ent : Entry) (j : Nat) (a : BitVec 64) : Prop := j = 0 ∧ Ent.stack.contains a.toNat

namespace OwnDom

variable {c c' : Config I × KState}

/-- **The frame of a step**: the held ranges and the pool unchanged, no slot
made dormant, and every thread of `c'` with the domain and the fragment of
the thread at the same index of `c`. -/
theorem frame (hc : OwnDom K E P c) (hh : c'.2.held = c.2.held) (hp : c'.2.pool = c.2.pool)
    (hd : ∀ k : Nat, c'.2.slots[k]? = some Slot.dormant → c.2.slots[k]? = some Slot.dormant)
    (ht : ∀ (k : Nat) (t' : Thread I), c'.1.threads[k]? = some t' →
      ∃ t, c.1.threads[k]? = some t ∧ (∀ a, a ∈ K.dmem t'.st ↔ a ∈ K.dmem t.st) ∧ P t'.st) :
    OwnDom K E P c' where
  dom k t' h a := by
    obtain ⟨t, h0, hm, -⟩ := ht k t' h
    rw [hm, hc.dom k t h0, hh]
  frag k t' h := by obtain ⟨_, -, -, hP⟩ := ht k t' h; exact hP
  held_ok := by rw [hh, hp]; exact hc.held_ok
  held_live h hm hdm := by rw [hh] at hm; exact hc.held_live h hm (hd _ hdm)
  held_disj := by rw [hh]; exact hc.held_disj
  pool_E j a := by rw [hp]; exact hc.pool_E j a
  E_dorm j a hdm := hc.E_dorm j a (hd j hdm)

/-- **Replacing one thread** by one with the same domain in the fragment. -/
theorem replace (hc : OwnDom K E P c) {tid : Nat} {t u : Thread I} {mem : Memory} {x : KState}
    (ht : c.1.threads[tid]? = some t) (hm : ∀ a, a ∈ K.dmem u.st ↔ a ∈ K.dmem t.st) (hu : P u.st)
    (hh : x.held = c.2.held) (hp : x.pool = c.2.pool)
    (hd : ∀ k : Nat, x.slots[k]? = some Slot.dormant → c.2.slots[k]? = some Slot.dormant) :
    OwnDom K E P (c.1.withThread tid u mem, x) := by
  refine frame hc hh hp hd fun k t' h => ?_
  rw [withThread_get] at h
  split at h
  · rename_i hk
    obtain ⟨rfl, -⟩ := hk
    cases h
    exact ⟨t, ht, hm, hu⟩
  · exact ⟨t', h, fun _ => Iff.rfl, hc.frag k t' h⟩

/-! ### Held ranges -/

theorem heldAt_cons_ne {held : List (Nat × Range)} {j k : Nat} {r : Range} (h : j ≠ k) (a : BitVec 64) :
    HeldAt ((j, r) :: held) k a ↔ HeldAt held k a := by
  unfold HeldAt
  constructor
  · rintro ⟨r', hm, hr⟩
    rcases List.mem_cons.mp hm with he | hm
    · cases he; exact absurd rfl h
    · exact ⟨r', hm, hr⟩
  · rintro ⟨r', hm, hr⟩
    exact ⟨r', List.mem_cons_of_mem _ hm, hr⟩

theorem heldAt_cons_self {held : List (Nat × Range)} {k : Nat} {r : Range} (a : BitVec 64) :
    HeldAt ((k, r) :: held) k a ↔ r.contains a.toNat ∨ HeldAt held k a := by
  unfold HeldAt
  constructor
  · rintro ⟨r', hm, hr⟩
    rcases List.mem_cons.mp hm with he | hm
    · cases he; exact .inl hr
    · exact .inr ⟨r', hm, hr⟩
  · rintro (hr | ⟨r', hm, hr⟩)
    · exact ⟨r, List.mem_cons_self, hr⟩
    · exact ⟨r', List.mem_cons_of_mem _ hm, hr⟩

theorem heldAt_erase_ne {held : List (Nat × Range)} {k tid : Nat} {r : Range} (h : k ≠ tid) (a : BitVec 64) :
    HeldAt (held.erase (tid, r)) k a ↔ HeldAt held k a := by
  unfold HeldAt
  have hne : ∀ r', (k, r') ≠ (tid, r) := fun r' e => h (Prod.mk.inj e).1
  exact exists_congr fun r' => and_congr_left fun _ => List.mem_erase_of_ne (hne r')

/-- **Giving up a held range** `r`: thread `tid`'s domain without the
addresses of `r` is its domain for the held ranges without `(tid, r)`. -/
theorem dom_erase (hc : OwnDom K E P c) {tid : Nat} {r : Range} (hm : (tid, r) ∈ c.2.held) (a : BitVec 64) :
    (a ∉ addrs r ∧ (E tid a ∨ HeldAt c.2.held tid a)) ↔ (E tid a ∨ HeldAt (c.2.held.erase (tid, r)) tid a) := by
  have hok : 0 < r.size ∧ r.Sub c.2.pool ∧ r.lo + r.size ≤ 2 ^ 64 := hc.held_ok _ hm
  have hin : a ∈ addrs r ↔ r.contains a.toNat := mem_addrs_iff hok.2.2 a
  constructor
  · rintro ⟨hna, hE | ⟨r', hm', hr'⟩⟩
    · exact .inl hE
    · refine .inr ⟨r', ?_, hr'⟩
      by_cases he : r' = r
      · subst he; exact absurd (hin.mpr hr') hna
      · exact (List.mem_erase_of_ne fun e => he (Prod.mk.inj e).2).mpr hm'
  · rintro (hE | ⟨r', hm', hr'⟩)
    · refine ⟨fun ha => hc.pool_E tid a hE ?_, .inl hE⟩
      have h1 := hin.mp ha
      have h2 := hok.2.1
      unfold Range.contains at *; unfold Range.Sub at h2; omega
    · refine ⟨fun ha => ?_, .inr ⟨r', List.mem_of_mem_erase hm', hr'⟩⟩
      have hd := disj_of_erase hc.held_disj (fun h hh => (hc.held_ok h hh).1) hm hm'
      exact hd.not_both hr' (hin.mp ha)

/-- **At load time** (`KState.init`): thread 0's private memory is the
initial stack, every other thread's is empty, every thread is in the
fragment, and the initial stack is clear of the stack pool. -/
theorem init {n : Nat} {Ent : Entry} {Λ : Layout} {c1 : Config I}
    (h0 : ∀ t, c1.threads[0]? = some t → ∀ a, a ∈ K.dmem t.st ↔ Ent.stack.contains a.toNat)
    (hk : ∀ (k : Nat) (t : Thread I), 0 < k → c1.threads[k]? = some t → ∀ a, a ∉ K.dmem t.st)
    (hP : ∀ (k : Nat) (t : Thread I), c1.threads[k]? = some t → P t.st) (hd : Λ.stackPool.Disjoint Ent.stack) :
    OwnDom K (initDom Ent) P (c1, KState.init n Ent Λ) where
  dom k t h a := by
    have hh : ¬ HeldAt (KState.init n Ent Λ).held k a := fun ⟨_, hm, _⟩ => by simp [KState.init] at hm
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [h0 t h a]; simp [initDom, hh]
    · simp only [initDom, Nat.ne_of_gt hpos, false_and, hh, or_self, iff_false]; exact hk k t hpos h a
  frag := hP
  held_ok h hm := by simp [KState.init] at hm
  held_live h hm := by simp [KState.init] at hm
  held_disj := by simp [KState.init]
  pool_E j a he hp := by
    obtain ⟨-, hs⟩ := he
    exact hd.not_both (by simpa [KState.init] using hp) hs
  E_dorm j a hdm he := by
    obtain ⟨rfl, -⟩ := he
    simp only [KState.init] at hdm
    rw [Array.getElem?_append_left (by simp)] at hdm
    simp at hdm

/-! ### Steps -/

/-- **An instruction or promise step** (of the existing machine, `StepSemC`)
keeps the invariant: the thread moves to a leaf of the ISA's `exec` or
only gains a promise. -/
theorem stepSemC (hD : DomHyps K P) (hc : OwnDom K E P c) {A : Arch} {cs : CertSem I} {tid : Nat}
    {c1 : Config I} (h : StepSemC A cs tid c.1 c1) : OwnDom K E P (c1, c.2) := by
  rcases h with ⟨t, outs, o, ht, hs, ho, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · obtain ⟨tree, st, c'', hex, hr, hth, -⟩ :=
      stepOneWith_runOut (cs := CertSem.ofExec I.exec) A hs ho
    have hl := runTree_treeLeaf A tid _ tree _ st c'' hr
    rw [← finishInstr_st hth] at hl
    obtain ⟨hP, hm⟩ := hD.exec t.st tree o.thread.st (hc.frag tid t ht) hex hl
    exact hc.replace ht hm hP rfl rfl fun _ h => h
  · exact hc.replace ht (fun _ => Iff.rfl) (hc.frag tid t ht) rfl rfl fun _ h => h

/-- **A take** keeps the invariant: the range is fresh, so inside the pool
and disjoint from every held range; the thread's domain gains its
addresses. -/
theorem take (hD : DomHyps K P) (hc : OwnDom K E P c) {tid : Nat} (h : takeStep K tid c = some c') :
    OwnDom K E P c' := by
  simp only [takeStep] at h
  split at h
  · cases h
  rename_i t ht
  split at h
  rotate_left
  · cases h
  rename_i hg
  cases h
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨⟨hrun, -⟩, -⟩, hf⟩ := hg
  unfold fresh at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at hf
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, hh⟩, -⟩, -⟩ := hf
  have hlt : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  refine ⟨fun k u hk a => ?_, fun k u hk => ?_, fun h hm => ?_, fun h hm => ?_, ?_, hc.pool_E, hc.E_dorm⟩
  · rw [withThread_get] at hk
    split at hk
    · rename_i hk'
      obtain ⟨rfl, -⟩ := hk'
      cases hk
      simp only [K.dmem_skip, K.dmem_setDmem]
      rw [mem_copyRange, mem_addrs_iff h3, hc.dom _ t ht a, heldAt_cons_self]
      exact or_left_comm
    · rename_i hk'
      have hne : tid ≠ k := fun e => hk' ⟨e, hlt⟩
      rw [hc.dom k u hk a]
      exact or_congr_right (heldAt_cons_ne hne a).symm
  · rw [withThread_get] at hk
    split at hk
    · rename_i hk'
      obtain ⟨rfl, -⟩ := hk'
      cases hk
      exact hD.skip _ (hD.setDmem _ _ (hc.frag _ t ht))
    · exact hc.frag k u hk
  · rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨h0, ⟨h1, h2⟩, h3⟩
    · exact hc.held_ok h hm
  · rcases List.mem_cons.mp hm with rfl | hm
    · exact not_dormant_of_runs hrun
    · exact hc.held_live h hm
  · refine List.pairwise_cons.mpr ⟨fun h hm => ?_, hc.held_disj⟩
    have := hh h hm
    unfold overlaps at this
    unfold Range.Disjoint
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at this
    omega

/-- **A release** keeps the invariant: the thread's domain loses the
addresses of a range it holds, which no other of its ranges and not its
initial stack contain. -/
theorem release (hD : DomHyps K P) (hc : OwnDom K E P c) {tid : Nat} (h : releaseStep K tid c = some c') :
    OwnDom K E P c' := by
  simp only [releaseStep] at h
  split at h
  · cases h
  rename_i t ht
  split at h
  rotate_left
  · cases h
  rename_i hg
  cases h
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hcon⟩, -⟩ := hg
  have hm := List.mem_of_elem_eq_true hcon
  have hlt : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  have hsub : c.2.held.erase (tid, siteRange K t.st) ⊆ c.2.held := fun _ h => List.mem_of_mem_erase h
  refine ⟨fun k u hk a => ?_, fun k u hk => ?_, fun h hm => hc.held_ok h (hsub hm),
    fun h hm => hc.held_live h (hsub hm), hc.held_disj.sublist List.erase_sublist, hc.pool_E, hc.E_dorm⟩
  · rw [withThread_get] at hk
    split at hk
    · rename_i hk'
      obtain ⟨rfl, -⟩ := hk'
      cases hk
      simp only [K.dmem_skip, K.dmem_setDmem]
      rw [mem_eraseRange, hc.dom _ t ht a]
      exact hc.dom_erase hm a
    · rename_i hk'
      have hne : tid ≠ k := fun e => hk' ⟨e, hlt⟩
      rw [hc.dom k u hk a]
      exact or_congr_right (heldAt_erase_ne (Ne.symm hne) a).symm
  · rw [withThread_get] at hk
    split at hk
    · rename_i hk'
      obtain ⟨rfl, -⟩ := hk'
      cases hk
      exact hD.skip _ (hD.setDmem _ _ (hc.frag _ t ht))
    · exact hc.frag k u hk

theorem set_dormant_run {x : KState} {j k w : Nat} (h : (x.set j (.run w)).slots[k]? = some Slot.dormant) :
    x.slots[k]? = some Slot.dormant := set_dormant (by simp) h

/-- **A `clone`** keeps the invariant: the parent returns, with the range it
hands over (if any) erased; the child, in a slot that was dormant (so with
no initial stack and no held range), maps exactly that range. -/
theorem spawn (hD : DomHyps K P) (hc : OwnDom K E P c) {tid j : Nat} {ctid : BitVec 64}
    (h : spawnStep K tid c j ctid = some c') : OwnDom K E P c' := by
  unfold spawnStep at h
  split at h
  · cases h
  rename_i t ht
  split at h
  · cases h
  rename_i hrd
  split at h
  rotate_left
  · cases h
  rename_i stack tls hcall
  split at h
  rotate_left
  · cases h
  rename_i hcond
  obtain ⟨hdor, hj, -, -⟩ := hcond
  have hjt : j ≠ tid := by
    rintro rfl
    simp [ready, KState.runs, hdor] at hrd
  have hlt : tid < c.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  have hnoj : ∀ a, ¬ HeldAt c.2.held j a := fun a ⟨r, hm, _⟩ => hc.held_live _ hm hdor
  have hEj : ∀ a, ¬ E j a := fun a => hc.E_dorm j a hdor
  have hP := hc.frag tid t ht
  have hget : ∀ {u v : Thread I} {k : Nat} {w : Thread I},
      ((c.1.withThread tid u c.1.mem).withThread j v c.1.mem).threads[k]? = some w →
        (k = j ∧ w = v) ∨ (k = tid ∧ w = u) ∨ (k ≠ j ∧ k ≠ tid ∧ c.1.threads[k]? = some w) := by
    intro u v k w hk
    have hsz : (c.1.withThread tid u c.1.mem).threads.size = c.1.threads.size := by simp [Config.withThread]
    rw [withThread_get, hsz, withThread_get] at hk
    by_cases h1 : j = k
    · subst h1; simp only [hj, and_self, ite_true, Option.some.injEq] at hk; exact .inl ⟨rfl, hk.symm⟩
    · simp only [h1, false_and, ite_false] at hk
      by_cases h2 : tid = k
      · subst h2; simp only [hlt, and_self, ite_true, Option.some.injEq] at hk; exact .inr (.inl ⟨rfl, hk.symm⟩)
      · simp only [h2, false_and, ite_false] at hk; exact .inr (.inr ⟨Ne.symm h1, Ne.symm h2, hk⟩)
  split at h
  · cases h
    refine ⟨fun k w hk a => ?_, fun k w hk => ?_, hc.held_ok, fun h hm hd => hc.held_live h hm (set_dormant_run hd),
      hc.held_disj, hc.pool_E, fun j' a hd => hc.E_dorm j' a (set_dormant_run hd)⟩
    · rcases hget hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hk⟩
      · show a ∈ K.dmem (K.child t.st stack tls) ↔ _
        rw [(hD.child _ _ _ hP).2]
        simp [KState.set, hEj a, hnoj a]
      · rw [retThread_st, (hD.ret _ _ hP).2]; exact hc.dom _ t ht a
      · exact hc.dom k w hk a
    · rcases hget hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hk⟩
      · exact (hD.child _ _ _ hP).1
      · rw [retThread_st]; exact (hD.ret _ _ hP).1
      · exact hc.frag k w hk
  · rename_i x r hf
    cases h
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, -⟩ := hp
    have hm := List.mem_of_find?_eq_some hf
    have hok : 0 < r.size ∧ r.Sub c.2.pool ∧ r.lo + r.size ≤ 2 ^ 64 := hc.held_ok _ hm
    have hsub : c.2.held.erase (x, r) ⊆ c.2.held := fun _ h => List.mem_of_mem_erase h
    refine ⟨fun k w hk a => ?_, fun k w hk => ?_, fun h hm' => ?_, fun h hm' hd => ?_, ?_, hc.pool_E,
      fun j' a hd => hc.E_dorm j' a (set_dormant_run hd)⟩
    · rcases hget hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hkj, hkt, hk⟩
      · show a ∈ K.dmem (K.setDmem (K.child t.st stack tls) _) ↔ _
        rw [K.dmem_setDmem]
        show a ∈ copyRange _ (K.dmem (K.child t.st stack tls)) r ↔ _
        rw [(hD.child _ _ _ hP).2, mem_copyRange, mem_addrs_iff hok.2.2, heldAt_cons_self, heldAt_erase_ne hjt]
        simp [hEj a, hnoj a]
      · rw [retThread_st, (hD.ret _ _ (hD.setDmem _ _ hP)).2, K.dmem_setDmem, mem_eraseRange, hc.dom _ t ht a,
          heldAt_cons_ne hjt]
        exact hc.dom_erase hm a
      · rw [hc.dom k w hk a, heldAt_cons_ne (Ne.symm hkj), heldAt_erase_ne hkt]
    · rcases hget hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hk⟩
      · exact hD.setDmem _ _ (hD.child _ _ _ hP).1
      · rw [retThread_st]; exact (hD.ret _ _ (hD.setDmem _ _ hP)).1
      · exact hc.frag k w hk
    · rcases List.mem_cons.mp hm' with rfl | hm'
      · exact hok
      · exact hc.held_ok h (hsub hm')
    · rcases List.mem_cons.mp hm' with rfl | hm'
      · have := (Array.getElem?_eq_some_iff.mp hdor).1
        simp [set_slots_get, this] at hd
      · exact hc.held_live h (hsub hm') (set_dormant_run hd)
    · refine List.pairwise_cons.mpr ⟨fun h hm' => ?_, hc.held_disj.sublist List.erase_sublist⟩
      have : h.2.Disjoint r := disj_of_erase hc.held_disj (fun h hh => (hc.held_ok h hh).1) hm hm'
      show r.Disjoint h.2
      unfold Range.Disjoint at *; omega

/-- **A system call other than `clone`** keeps the invariant: it changes no
held range and makes no slot dormant; the thread stays where it is, or
returns (after `setTp` for `arch_prctl`). -/
theorem sys (hD : DomHyps K P) (hc : OwnDom K E P c) {A : Arch} {tid : Nat} {p : Pick} {es : List Ev}
    (h : sysStep K A tid c p = some (es, c')) : OwnDom K E P c' := by
  unfold sysStep at h
  split at h
  · cases h
  rename_i t ht
  have hP := hc.frag tid t ht
  have hu : ∀ (u : Thread I) (x : KState), (∀ a, a ∈ K.dmem u.st ↔ a ∈ K.dmem t.st) → P u.st →
      x.held = c.2.held → x.pool = c.2.pool →
      (∀ k : Nat, x.slots[k]? = some Slot.dormant → c.2.slots[k]? = some Slot.dormant) →
      OwnDom K E P (c.1.withThread tid u c.1.mem, x) := fun u x hm hu hh hp hd => hc.replace ht hm hu hh hp hd
  have hb : ∀ (u : Thread I) (r : BitVec 64) (x : KState), K.dmem u.st = K.dmem t.st → P u.st →
      x.held = c.2.held → x.pool = c.2.pool →
      (∀ k : Nat, x.slots[k]? = some Slot.dormant → c.2.slots[k]? = some Slot.dormant) →
      OwnDom K E P (c.1.withThread tid (retThread K u r) c.1.mem, x) := by
    intro u r x hm hu' hh hp hd
    refine hu _ x (fun a => ?_) ?_ hh hp hd
    · rw [retThread_st, (hD.ret _ _ hu').2, hm]
    · rw [retThread_st]; exact (hD.ret _ _ hu').1
  have hrd : ∀ {rd a : Nat} {f : Fin 256 → List Ev},
      Option.map (fun x => (f x.1, c.1.withThread tid x.2 c.1.mem, c.2.set tid (.run (c.2.wr tid + 1))))
        (readByte K A t c.1.mem a rd) = some (es, c') → OwnDom K E P c' := by
    intro rd a f h
    obtain ⟨⟨b, t'⟩, hr, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    have hst := readByte_st hr
    exact hu t' _ (fun _ => by rw [hst]) (hst ▸ hP) rfl rfl fun _ h => set_dormant_run h
  have hs1 : ∀ x : KState, x.held = c.2.held → x.pool = c.2.pool →
      (∀ k : Nat, x.slots[k]? = some Slot.dormant → c.2.slots[k]? = some Slot.dormant) →
      OwnDom K E P (c.1, x) := fun x hh hp hd =>
    hc.frame hh hp hd fun k t' h => ⟨t', h, fun _ => Iff.rfl, hc.frag k t' h⟩
  split at h
  · cases h
  rcases hcall : callOf K t with _ | call
  · simp [hcall] at h
  cases call <;> cases p <;> simp only [hcall] at h <;> (repeat' split at h) <;> (try cases h)
  all_goals first
    | exact hb _ _ _ rfl hP rfl rfl (fun _ h => set_dormant_run h)
    | exact hb _ _ _ rfl hP rfl rfl (fun _ h => h)
    | exact hb { t with st := K.setTp t.st _ } _ _ (hD.setTp _ _ hP).2 (hD.setTp _ _ hP).1 rfl rfl (fun _ h => h)
    | exact hrd (f := fun b => [.out b]) h
    | exact hrd (f := fun _ => []) h
    | exact hs1 _ rfl rfl (fun _ h => set_dormant (by simp) h)
    | exact hs1 _ rfl rfl (fun _ h => h)
    | skip


/-! ### What the P1 lemmas need -/

/-- **At a take the range is not mapped** in the thread's private memory
(`certSem_step_of_take`'s `hdom`): it is in the pool, which the initial
stack avoids, and disjoint from every held range. -/
theorem take_unmapped (hc : OwnDom K E P c) {tid : Nat} {t : Thread I} (ht : c.1.threads[tid]? = some t)
    (h : (takeStep K tid c).isSome) : ∀ a ∈ addrs (siteRange K t.st), (K.dmem t.st)[a]? = none := by
  simp only [takeStep, ht] at h
  split at h
  rotate_left
  · simp at h
  rename_i hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨-, hf⟩ := hg
  unfold fresh at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at hf
  obtain ⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, hh⟩, -⟩, -⟩ := hf
  intro a ha
  have hr := (mem_addrs_iff h3 a).mp ha
  refine Std.ExtHashMap.getElem?_eq_none fun hm => ?_
  rcases (hc.dom tid t ht a).mp hm with hE | ⟨r', hm', hr'⟩
  · exact hc.pool_E tid a hE (by unfold Range.contains at *; omega)
  · have := hh _ hm'
    unfold overlaps at this
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at this
    unfold Range.contains at *; omega

/-- **At a release the range is mapped** in the thread's private memory
(`certSem_step_of_release`'s `hdom`): the thread holds it. -/
theorem release_mapped (hc : OwnDom K E P c) {tid : Nat} {t : Thread I} (ht : c.1.threads[tid]? = some t)
    (h : (releaseStep K tid c).isSome) : ∀ a ∈ addrs (siteRange K t.st), ((K.dmem t.st)[a]?).isSome := by
  simp only [releaseStep, ht] at h
  split at h
  rotate_left
  · simp at h
  rename_i hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hcon⟩, -⟩ := hg
  have hm := List.mem_of_elem_eq_true hcon
  intro a ha
  rw [← Std.ExtHashMap.mem_iff_isSome_getElem?, hc.dom tid t ht a]
  exact .inr ⟨_, hm, (mem_addrs_iff (hc.held_ok _ hm).2.2 a).mp ha⟩

variable {A : Arch} {n : Nat} {rv : I.State → I.RegId → BitVec 64}
  {pl : I.State → BitVec 64 → Option (BitVec 64)} {pcf : I.State → Nat} {μ : Marks}

/-- **Every step of the kernel model's machine keeps the invariant.** -/
theorem step (hD : DomHyps K P) {tid : Nat} {es : List Ev}
    {c c' : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg}
    (hc : OwnDom K E P c) (h : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Step μ tid c es c') :
    OwnDom K E P c' := by
  cases h with
  | instr _ _ _ hs => exact hc.stepSemC hD hs
  | spawn _ hs => obtain ⟨j, r, hs, -⟩ := hs; exact hc.spawn hD hs
  | sys _ hs => obtain ⟨p, hs, -⟩ := hs; exact hc.sys hD hs
  | xfer k _ _ hx =>
    cases k
    · exact hc.take hD hx
    · exact hc.release hD hx

/-- **Every run of the kernel model's machine keeps the invariant.** -/
theorem run (hD : DomHyps K P) {tr : List Ev} {c c' : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Cfg}
    (hc : OwnDom K E P c) (h : (ExtMachine.ofHooks I A (hooks K A n) rv pl pcf).Run μ c tr c') :
    OwnDom K E P c' := by
  unfold ExtMachine.Run at h
  induction h with
  | refl => exact hc
  | step hs _ ih => obtain ⟨tid, hs⟩ := hs; exact ih (hc.step hD hs)

end OwnDom

end Scc.Sem.Kernel
