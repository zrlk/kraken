/-
**The memory relation for one thread** (`Scc/DESIGN.md` §8, M1).

The memory clauses of `ComponentsAll`, over the witness's label placement
`lbl`, label sizes `lsize` and timestamp map `ts`, the target memory `tm`,
the source memory `sm` and the source's pair list (`MemRel`), and their
preservation by the shared accesses of one thread with no promises, paired
with the matching source steps. Under `gc none` no label range is reused, so
the unscoped form (every label) is an invariant; `Components` follows by
`ComponentsAll.scoped` (`Components.ofMemRel`).

- `MemRel`, `CompRest` (the non-memory clauses), `ComponentsAll.iff_memRel`;
- derived facts: `MemRel.ts_le_last` (every image exists),
  `MemRel.wordAddr_inj` (in-bounds source addresses mapped to one target
  word are equal);
- `MemRel.empty`: the base case;
- `MemRel.store`: a target append of an 8-byte message at a word address
  paired with a source message to the source address placed there;
- the read side, assuming every target message is an 8-byte access
  (`Narrow`): `MemRel.latest` (the latest source message to an address maps
  to the latest target write of its word), `MemRel.latest_read`,
  `MemRel.latest_byte` (the kernel's byte of a `write` buffer), and
  `readable_latest` (the source can always read the latest message);
- `MemRel.runtime_write`: a target write outside every placed label, with no
  source step;
- `MemRel.alloc`: a fresh label placed in the heap, its zero cells mapped to
  timestamp 0.

A read-modify-write on an own cell (`xchg`, lowered as a plain load then a
plain store) is the read side followed by `store`: the target load appends
nothing. Sub-word stores are outside this fragment.
-/
import Scc.Sem.Correct

namespace Scc.Sem

open Kraken.Promising

/-- The range of label `l` placed at `b` with sizes `lsize` (`labelRange`
without a witness). -/
def lrange (lsize : WeakMem.AllocLabel → Nat) (l : WeakMem.AllocLabel) (b : Nat) : Range := ⟨b, 8 * lsize l⟩

/-- **The memory relation**: the memory clauses of `ComponentsAll` (`lbl_static`,
`lbl_range`, `lbl_disj`, `lbl_mem`, `mem_rep`, `ts_first`, `ts_mono`,
`mem_onto`) over the witness's maps, the target memory `tm`, the source
memory `sm` and the source's pair list `pairs`. -/
structure MemRel (Λ : Layout) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (ts : Nat → Option Nat) (tm : Memory) (sm : WeakMem.Memory) (pairs : List Nat) : Prop where
  lbl_static : ∀ l b, Λ.static l = some b → lbl l = some b
  lbl_range : ∀ l b, lbl l = some b → b % 8 = 0 ∧ ((lrange lsize l b).Sub Λ.heap ∨ (lrange lsize l b).Sub Λ.data)
  lbl_disj : ∀ l l' b b', l ≠ l' → lbl l = some b → lbl l' = some b' → (lrange lsize l b).Disjoint (lrange lsize l' b')
  lbl_mem : ∀ m ∈ sm.toList, ∃ b, lbl m.loc.label = some b ∧ m.loc.offset < lsize m.loc.label
  mem_rep : ∀ k m, sm[k]? = some m → ∃ k' a v, ts k = some k' ∧ wordAddr lbl m.loc = some a ∧
    wordAt tm a k' = some v ∧ ValRep lbl m.val v
  ts_first : ∀ k m, sm[k]? = some m → ts k = some 0 → ∀ k2 m2, k2 < k → sm[k2]? = some m2 → m2.loc ≠ m.loc
  ts_mono : ∀ k1 k2 k1' k2', ts k1 = some k1' → ts k2 = some k2' → 0 < k1' → 0 < k2' → k1 < k2 →
    k1' < k2' ∨ (k1' = k2' ∧ k2 = k1 + 1 ∧ k1 ∈ pairs ∧
      ∀ m1 m2, sm[k1]? = some m1 → sm[k2]? = some m2 → m1.loc ≠ m2.loc)
  mem_onto : ∀ k' m', tm.get? k' = some m' → (∃ l b, lbl l = some b ∧ (lrange lsize l b).contains m'.loc.addr.toNat) →
    ∃ k, k < sm.size ∧ ts k = some k'

/-- **The non-memory clauses of `ComponentsAll`**: threads, environments and
stacks. -/
structure CompRest (M : ExtMachine) (Λ : Layout) (w : Witness M) (t : M.Cfg) (s : TermRun.Cfg) : Prop where
  thr_total : ∀ i, i < s.ths.size → ∃ j, w.thr i = some j ∧ j < t.1.threads.size
  thr_inj : ∀ i i' j, w.thr i = some j → w.thr i' = some j → i = i'
  thr_onto : ∀ j tt, M.runs t j → t.1.threads[j]? = some tt → ∃ i, i < s.ths.size ∧ w.thr i = some j
  env_rep : ∀ i th j tt, s.ths[i]? = some th → w.thr i = some j → t.1.threads[j]? = some tt →
    ∀ d e, (frameEnvs th)[d]? = some e → ∀ x ty ws, TermRun.lookupE e x = some (ty, ws) →
    ∀ k wd wp, ws[k]? = some wd → w.env i d x k = some wp → ¬ ExternFrame th d →
    WordPlaceRep M w.lbl tt.st wp wd.val
  env_total : ∀ i th, s.ths[i]? = some th → ∀ d e xs, (frameEnvs th)[d]? = some e → (frameFv th)[d]? = some xs →
    ¬ ExternFrame th d → ∀ x ∈ xs, ∀ ty ws, TermRun.lookupE e x = some (ty, ws) →
    ∀ k < ws.length, ∃ pl, w.env i d x k = some pl
  stack_pool : ∀ j rg, M.stackRange t j = some rg → rg.Sub Λ.stackPool
  stack_disj : ∀ j j' rg rg', j ≠ j' → M.stackRange t j = some rg → M.stackRange t j' = some rg' →
    rg.Disjoint rg'
  stack_owned : ∀ j rg, M.stackRange t j = some rg → ∀ j' tt', t.1.threads[j']? = some tt' →
    ∀ a, a % 8 = 0 → rg.contains a → rg.contains (a + 7) →
    ((M.privLoad tt'.st (BitVec.ofNat 64 a)).isSome ↔ j' = j)
  stack_private : ∀ j rg, M.stackRange t j = some rg → ∀ m ∈ t.1.mem.msgs.toList,
    ¬ rg.contains m.loc.addr.toNat
  stack_marked : ∀ j pl, w.marked j pl → ∃ tt rg v, t.1.threads[j]? = some tt ∧
    M.stackRange t j = some rg ∧ placeVal M tt.st pl = some v ∧ rg.contains v
  stack_unmarked : ∀ i d x k wp pl j, w.env i d x k = some wp → pl ∈ wp.places → w.thr i = some j →
    ¬ w.marked j pl
  env_imm : ∀ i th d e x k n, s.ths[i]? = some th → (frameTerms th)[d]? = some e →
    w.env i d x k = some (.imm n) → Λ.imms e x k = some n

/-- **`ComponentsAll` is the memory relation and the rest.** -/
theorem ComponentsAll.iff_memRel {M : ExtMachine} {Λ : Layout} {w : Witness M} {t : M.Cfg} {s : TermRun.Cfg} :
    ComponentsAll M Λ w t s ↔ MemRel Λ w.lbl w.lsize w.ts t.1.mem s.mem s.pairs ∧ CompRest M Λ w t s := by
  constructor
  · intro h
    exact ⟨⟨h.lbl_static, h.lbl_range, h.lbl_disj, h.lbl_mem, h.mem_rep, h.ts_first, h.ts_mono, h.mem_onto⟩,
      ⟨h.thr_total, h.thr_inj, h.thr_onto, h.env_rep, h.env_total, h.stack_pool, h.stack_disj, h.stack_owned,
        h.stack_private, h.stack_marked, h.stack_unmarked, h.env_imm⟩⟩
  · rintro ⟨m, r⟩
    exact ⟨r.thr_total, r.thr_inj, r.thr_onto, m.lbl_static, m.lbl_range, m.lbl_disj, m.lbl_mem, m.mem_rep,
      m.ts_first, m.ts_mono, m.mem_onto, r.env_rep, r.env_total, r.stack_pool, r.stack_disj, r.stack_owned,
      r.stack_private, r.stack_marked, r.stack_unmarked, r.env_imm⟩

/-- **`Components` from the memory relation** (`Scc/DESIGN.md` §8, item 7),
for a witness with no epochs. -/
theorem Components.ofMemRel {M : ExtMachine} {Λ : Layout} {w : Witness M} {t : M.Cfg} {s : TermRun.Cfg}
    (hm : MemRel Λ w.lbl w.lsize w.ts t.1.mem s.mem s.pairs) (hr : CompRest M Λ w t s)
    (hs : ∀ l, w.since l = 0) (ht : ∀ l, w.tsFrom l = 0) : Components M Λ w t s :=
  (ComponentsAll.iff_memRel.mpr ⟨hm, hr⟩).scoped hs ht

/-! ## Target memory facts -/

/-- `8 * offset` at `Nat` (source offsets are `WeakMem.Offset`, which
`omega` does not read through). -/
theorem mul_offset (n : Nat) (o : WeakMem.Offset) :
    @HMul.hMul Nat WeakMem.Offset Nat (@instHMul Nat instMulNat) n o = @HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n o :=
  rfl

namespace Memory

/-- Appending keeps every earlier message. -/
theorem get?_append_le {m : Memory} {w : Msg} {k : Nat} (hk : k ≤ m.last) : (m.append w).1.get? k = m.get? k := by
  unfold Memory.get? Memory.append
  split
  · rfl
  · simp only [Memory.last] at hk
    rw [Array.getElem?_push]
    split
    · rename_i h1 h2
      have h3 : (k - 1 : Nat) = m.msgs.size := h2
      have h4 : (k : Nat) ≤ m.msgs.size := hk
      have h5 : (k : Nat) ≠ 0 := h1
      omega
    · rfl

/-- The appended message is at `last + 1`. -/
theorem get?_append_new {m : Memory} {w : Msg} : (m.append w).1.get? (m.last + 1) = some w := by
  simp [Memory.get?, Memory.append, Memory.last]

/-- A message exists only up to `last`. -/
theorem le_last_of_get? {m : Memory} {k : Nat} {w : Msg} (h : m.get? k = some w) : k ≤ m.last := by
  unfold Memory.get? at h
  split at h
  · cases h
  · have : k - 1 < m.msgs.size := by
      rcases Nat.lt_or_ge (k - 1) m.msgs.size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_none h'] at h
    simp only [Memory.last]; omega

/-- Appending keeps every earlier read. -/
theorem read?_append_le {m : Memory} {w : Msg} {l : Loc} {k : Nat} (hk : k ≤ m.last) :
    (m.append w).1.read? l k = m.read? l k := by
  unfold Memory.read?
  split
  · rfl
  · rw [get?_append_le hk]

end Memory

/-- Appending keeps every earlier `wordAt`. -/
theorem wordAt_append_le {m : Memory} {w : Msg} {a k : Nat} (hk : k ≤ m.last) :
    wordAt (m.append w).1 a k = wordAt m a k := by
  simp only [wordAt, Memory.read?_append_le hk]

/-- A defined `wordAt` is at a timestamp of the memory. -/
theorem le_last_of_wordAt {m : Memory} {a k v : Nat} (h : wordAt m a k = some v) : k ≤ m.last := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  · have key : ∀ l v', m.read? l k = some v' → k ≤ m.last := by
      intro l v' hr
      have hk0 : k ≠ 0 := by omega
      unfold Memory.read? at hr
      simp only [hk0, ↓reduceIte] at hr
      cases hg : m.get? k with
      | none => rw [hg] at hr; cases hr
      | some w => exact Memory.le_last_of_get? hg
    unfold wordAt at h
    split at h
    · rename_i v' hr; exact key _ _ hr
    · split at h
      · rename_i v' hr; exact key _ _ hr
      · split at h
        · cases hr : m.read? ⟨BitVec.ofNat 64 (a - 8), 16⟩ k with
          | none => rw [hr] at h; cases h
          | some v' => exact key _ _ hr
        · cases h

namespace MemRel

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {pairs : List Nat}

/-! ## Derived facts -/

/-- **Every image exists**: a source message's timestamp is at most the
target's last. -/
theorem ts_le_last (h : MemRel Λ lbl lsize ts tm sm pairs) {k k' : Nat} (hk : k < sm.size)
    (ht : ts k = some k') : k' ≤ tm.last := by
  obtain ⟨k'', a, v, ht', -, hw, -⟩ := h.mem_rep k sm[k] (Array.getElem?_eq_getElem hk)
  rw [ht] at ht'; cases ht'
  exact le_last_of_wordAt hw

/-- **Placement is injective on in-bounds addresses**: two source addresses
with in-bounds offsets of placed labels that map to the same target word are
equal. -/
theorem wordAddr_inj (h : MemRel Λ lbl lsize ts tm sm pairs) {a1 a2 : WeakMem.Address} {x : Nat}
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

/-- **The empty relation**: with no static labels, nothing placed and no
source message, any target memory is related (the base case before the
first allocation). -/
theorem empty (hs : ∀ l, Λ.static l = none) (lsize : WeakMem.AllocLabel → Nat) (tm : Memory)
    (pairs : List Nat) : MemRel Λ (fun _ => none) lsize (fun _ => none) tm #[] pairs := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l b hb; rw [hs l] at hb; cases hb
  · intro l b hb; cases hb
  · intro l l' b b' _ hb; cases hb
  · intro m hm; simp at hm
  · intro k m hk; simp at hk
  · intro k m hk; simp at hk
  · intro k1 k2 k1' k2' h1; cases h1
  · intro k' m' _ hin; obtain ⟨l, b, hb, -⟩ := hin; cases hb

/-! ## A store -/

/-- **A store** (`Scc/DESIGN.md` §8, item 1): the target appends an 8-byte
message of `v` at the word address `a`; the source pushes a message `m` to
the source address `sa` placed at `a`, in bounds, with a value `v`
represents. The new image of source message `sm.size` is the new target
timestamp `tm.last + 1`. -/
theorem store (h : MemRel Λ lbl lsize ts tm sm pairs) {a : Nat} {v : Val} {tid : Nat} {m : WeakMem.Msg}
    (ha : wordAddr lbl m.loc = some a) (ho : m.loc.offset < lsize m.loc.label) (hv : ValRep lbl m.val v.toNat)
    (hts : ∀ k, sm.size ≤ k → ts k = none) :
    MemRel Λ lbl lsize (fun k => if k = sm.size then some (tm.last + 1) else ts k)
      (tm.append ⟨wordLoc a, v, tid⟩).1 (sm.push m) pairs := by
  have hlast : ∀ k k', k < sm.size → ts k = some k' → k' ≤ tm.last := fun k k' hk ht => h.ts_le_last hk ht
  have pushGet : ∀ k m', (sm.push m)[k]? = some m' → (k < sm.size ∧ sm[k]? = some m') ∨ (k = sm.size ∧ m' = m) := by
    intro k m' hk
    rw [Array.getElem?_push] at hk
    split at hk
    · cases hk; exact .inr ⟨by assumption, rfl⟩
    · refine .inl ⟨?_, hk⟩
      rcases Nat.lt_or_ge k sm.size with h' | h'
      · exact h'
      · rename_i hne
        have : sm.size < k := by omega
        simp [Array.getElem?_eq_none (by omega : sm.size ≤ k)] at hk
  refine ⟨h.lbl_static, h.lbl_range, h.lbl_disj, ?_, ?_, ?_, ?_, ?_⟩
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
      rw [wordAt_append_le (hlast k k' hlt ht)]; exact hw
    · refine ⟨tm.last + 1, a, v.toNat, by simp, ha, ?_, hv⟩
      simp [wordAt, Memory.read?, Memory.get?_append_new]
  · intro k m' hk ht0 k2 m2 hk2 hm2
    rcases pushGet k m' hk with ⟨hlt, hk⟩ | ⟨rfl, rfl⟩
    · have ht : ts k = some 0 := by simpa [Nat.ne_of_lt hlt] using ht0
      rcases pushGet k2 m2 hm2 with ⟨-, hm2⟩ | ⟨rfl, -⟩
      · exact h.ts_first k m' hk ht k2 m2 hk2 hm2
      · omega
    · simp at ht0
  · intro k1 k2 k1' k2' h1 h2 p1 p2 hlt
    by_cases e2 : k2 = sm.size
    · subst e2
      have e1 : k1 ≠ sm.size := by omega
      simp only [e1, ite_false] at h1
      simp only [ite_true] at h2; cases h2
      have := hlast k1 k1' hlt h1
      exact .inl (by omega)
    · have e1 : k1 ≠ sm.size := by
        intro e; subst e
        have : sm.size < k2 := by omega
        simp only [e2, ite_false] at h2
        rw [hts k2 (by omega)] at h2; cases h2
      simp only [e1, e2, ite_false] at h1 h2
      rcases h.ts_mono k1 k2 k1' k2' h1 h2 p1 p2 hlt with h' | ⟨a1, a2, a3, a4⟩
      · exact .inl h'
      · refine .inr ⟨a1, a2, a3, fun m1 m2 hm1 hm2 => ?_⟩
        have hk2 : k2 < sm.size := by
          rcases Nat.lt_or_ge k2 sm.size with h' | h'
          · exact h'
          · rw [hts k2 h'] at h2; cases h2
        rcases pushGet k1 m1 hm1 with ⟨-, hm1⟩ | ⟨rfl, -⟩
        · rcases pushGet k2 m2 hm2 with ⟨-, hm2⟩ | ⟨rfl, -⟩
          · exact a4 m1 m2 hm1 hm2
          · omega
        · omega
  · intro k' m' hg hin
    by_cases hk : k' = tm.last + 1
    · subst hk
      exact ⟨sm.size, by simp, by simp⟩
    · have hle : k' ≤ tm.last := by
        have h1 := Memory.le_last_of_get? hg
        simp only [Memory.last, Memory.append, Array.size_push] at h1 hk
        have h2 : (k' : Nat) ≤ tm.msgs.size + 1 := h1
        have h3 : (k' : Nat) ≠ tm.msgs.size + 1 := hk
        show (k' : Nat) ≤ tm.msgs.size
        rcases Nat.lt_or_ge k' (tm.msgs.size + 1) with h4 | h4
        · exact Nat.le_of_lt_succ h4
        · exact absurd (Nat.le_antisymm h2 h4) h3
      rw [Memory.get?_append_le hle] at hg
      obtain ⟨k, hk', ht⟩ := h.mem_onto k' m' hg hin
      refine ⟨k, by simp; omega, ?_⟩
      simp [Nat.ne_of_lt hk', ht]

/-! ## The read side: latest messages -/

/-- **Every target message is an 8-byte access** (M1: no store pairs, no
16-byte or narrower shared accesses). -/
def Narrow (tm : Memory) : Prop := ∀ k w, tm.get? k = some w → w.loc.bytes = 8

/-- **`j` is the latest source message to `sa`.** -/
def SLatest (sm : WeakMem.Memory) (sa : WeakMem.Address) (j : Nat) : Prop :=
  (∃ m, sm[j]? = some m ∧ m.loc = sa) ∧ ∀ k m, j < k → sm[k]? = some m → m.loc ≠ sa

/-- **`k'` is the latest target write of the word at `a`**: the initial write
(`0`) or an 8-byte message there, with no later one there. -/
def TLatest (tm : Memory) (a k' : Nat) : Prop :=
  (k' = 0 ∨ ∃ w, tm.get? k' = some w ∧ w.loc = wordLoc a) ∧
    ∀ k'' w, k' < k'' → tm.get? k'' = some w → w.loc ≠ wordLoc a

/-- With 8-byte messages only, a defined `wordAt` at a positive timestamp is
the 8-byte message at that word. -/
theorem wordAt_msg {tm : Memory} (hn : Narrow tm) {x k' v : Nat} (hk : 0 < k') (h : wordAt tm x k' = some v) :
    ∃ w, tm.get? k' = some w ∧ w.loc = wordLoc x ∧ v = w.val.toNat := by
  have hk0 : k' ≠ 0 := by omega
  cases hg : tm.get? k' with
  | none =>
    simp [wordAt, Memory.read?, hk0, hg] at h
  | some w =>
    have hb := hn k' w hg
    by_cases hl : w.loc = wordLoc x
    · simp [wordAt, Memory.read?, hk0, hg, hl] at h
      exact ⟨w, rfl, hl, h.symm⟩
    · have h16 : ∀ y, (w.loc == ⟨BitVec.ofNat 64 y, 16⟩) = false := by
        intro y; simp only [beq_eq_false_iff_ne, ne_eq]; intro he; rw [he] at hb; cases hb
      simp [wordAt, Memory.read?, hk0, hg, hl, h16] at h

/-- Placed in-bounds words of a well-formed layout are below `2^64`. -/
theorem addr_lt (h : MemRel Λ lbl lsize ts tm sm pairs) (hwf : Λ.WF) {sa : WeakMem.Address} {x : Nat}
    (hx : wordAddr lbl sa = some x) (ho : sa.offset < lsize sa.label) : x + 8 ≤ 2 ^ 64 := by
  simp only [wordAddr, Option.map_eq_some_iff] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  rw [mul_offset]
  have ho' : @LT.lt Nat instLTNat sa.offset (lsize sa.label) := ho
  have hh := hwf.inSpace Λ.heap (by simp [Layout.regions])
  have hd := hwf.inSpace Λ.data (by simp [Layout.regions])
  simp only [Range.InSpace] at hh hd
  rcases (h.lbl_range _ _ hb).2 with hs | hs <;> simp only [lrange, Range.Sub] at hs <;> omega

/-- Two placed in-bounds words with the same 8-byte location are the same
word. -/
theorem wordLoc_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : wordLoc x = wordLoc y) : x = y := by
  simp only [wordLoc, Loc.mk.injEq, and_true] at h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  exact this

/-- **The read side** (`Scc/DESIGN.md` §8, item 2): if `j` is the latest
source message to `sa`, placed at the word `a`, and `k'` the latest target
write of `a`, then `j`'s image is `k'`, and the word the target reads there
represents `j`'s value. -/
theorem latest (h : MemRel Λ lbl lsize ts tm sm pairs) (hwf : Λ.WF) (hn : Narrow tm) {sa : WeakMem.Address}
    {a j k' : Nat} (ha : wordAddr lbl sa = some a) (hj : SLatest sm sa j) (hk : TLatest tm a k') :
    ts j = some k' ∧ ∃ m v, sm[j]? = some m ∧ wordAt tm a k' = some v ∧ ValRep lbl m.val v := by
  obtain ⟨⟨m, hm, hml⟩, hjl⟩ := hj
  obtain ⟨kj, a', v, hts, ha', hw, hv⟩ := h.mem_rep j m hm
  rw [hml, ha] at ha'; cases ha'
  have hoa : sa.offset < lsize sa.label := by
    obtain ⟨b, -, hb⟩ := h.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm)); rw [← hml]; exact hb
  have hal := h.addr_lt hwf ha hoa
  -- the image of `j` is at most `k'`
  have hle : kj ≤ k' := by
    rcases Nat.eq_zero_or_pos kj with rfl | hpos
    · exact Nat.zero_le _
    · obtain ⟨w, hg, hwl, -⟩ := wordAt_msg hn hpos hw
      rcases Nat.lt_or_ge k' kj with hlt | hge
      · exact absurd hwl (hk.2 kj w hlt hg)
      · exact hge
  have heq : kj = k' := by
    rcases hk.1 with rfl | ⟨w, hg, hwl⟩
    · omega
    · have hkpos : 0 < k' := by
        rcases Nat.eq_zero_or_pos k' with rfl | hp
        · simp [Memory.get?] at hg
        · exact hp
      -- the target message `k'` has a preimage, at `sa`
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
      obtain ⟨k2, hk2, ht2⟩ := h.mem_onto k' w hg hin
      obtain ⟨m2, hm2⟩ : ∃ m2, sm[k2]? = some m2 := ⟨_, Array.getElem?_eq_getElem hk2⟩
      obtain ⟨k2', x, v2, ht2', hx, hw2, -⟩ := h.mem_rep k2 m2 hm2
      rw [ht2] at ht2'; cases ht2'
      obtain ⟨w', hg', hwl', -⟩ := wordAt_msg hn hkpos hw2
      rw [hg] at hg'; cases hg'
      have ho2 : m2.loc.offset < lsize m2.loc.label := by
        obtain ⟨b, -, hb⟩ := h.lbl_mem m2 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm2)); exact hb
      have hxl := h.addr_lt hwf hx ho2
      have hxa : x = a := wordLoc_inj (by omega) (by omega) (hwl'.symm.trans hwl)
      subst hxa
      have hloc : m2.loc = sa := h.wordAddr_inj hx ha ho2 hoa
      -- `k2` is `j`
      rcases Nat.lt_trichotomy k2 j with hlt | rfl | hgt
      · rcases Nat.eq_zero_or_pos kj with rfl | hpos
        · exact absurd hloc (by rw [← hml]; exact h.ts_first j m hm hts k2 m2 hlt hm2)
        · rcases h.ts_mono k2 j k' kj ht2 hts hkpos hpos hlt with hlt' | ⟨-, -, -, hne⟩
          · omega
          · exact absurd (hloc.trans hml.symm) (hne m2 m hm2 hm)
      · rw [hts] at ht2; cases ht2; rfl
      · exact absurd hloc (hjl k2 m2 hgt hm2)
  subst heq
  exact ⟨hts, m, v, hm, hw, hv⟩

/-- **What the target reads is what the source reads**: under `latest`, an
8-byte target read of `a` at `k'` returns the value `sm[j].val` represents. -/
theorem latest_read (h : MemRel Λ lbl lsize ts tm sm pairs) (hwf : Λ.WF) (hn : Narrow tm) {sa : WeakMem.Address}
    {a j k' : Nat} (ha : wordAddr lbl sa = some a) (hj : SLatest sm sa j) (hk : TLatest tm a k') {val : Val}
    (hr : tm.read? (wordLoc a) k' = some val) : ∃ m, sm[j]? = some m ∧ ValRep lbl m.val val.toNat := by
  obtain ⟨-, m, v, hm, hw, hv⟩ := h.latest hwf hn ha hj hk
  rw [wordAt_of_read hr] at hw; cases hw
  exact ⟨m, hm, hv⟩

/-- **The kernel's byte of a `write` buffer** (`Kernel.readByte` reads the
8-byte word containing the byte and takes byte `i` of it): when the latest
source message to the word holds the number `n`, the byte is byte `i` of
`n`. -/
theorem latest_byte (h : MemRel Λ lbl lsize ts tm sm pairs) (hwf : Λ.WF) (hn : Narrow tm) {sa : WeakMem.Address}
    {a j k' : Nat} (ha : wordAddr lbl sa = some a) (hj : SLatest sm sa j) (hk : TLatest tm a k') {val : Val}
    (hr : tm.read? (wordLoc a) k' = some val) {n : Nat} (hnum : ∃ m, sm[j]? = some m ∧ m.val = .num n) (i : Nat) :
    (val.toNat / 2 ^ (8 * i)) % 256 = (n / 2 ^ (8 * i)) % 256 := by
  obtain ⟨m, hm, hv⟩ := h.latest_read hwf hn ha hj hk hr
  obtain ⟨m', hm', hval⟩ := hnum
  rw [hm] at hm'; cases hm'
  rw [hval] at hv
  rw [hv.2]

/-- **The source reads only the latest message** when its read bound covers
it: with `j` the latest message to `sa` and `j ≤ bound`, `sa` is readable
from `t` exactly when `t = j`. -/
theorem readable_iff_latest {sm : WeakMem.Memory} {sa : WeakMem.Address} {j bound t : Nat} (hj : SLatest sm sa j)
    (hb : j ≤ bound) : WeakMem.readable sm sa t bound = true ↔ t = j := by
  obtain ⟨⟨m, hm, hml⟩, hjl⟩ := hj
  constructor
  · intro hr
    simp only [WeakMem.readable, Bool.and_eq_true, Bool.not_eq_true'] at hr
    obtain ⟨hloc, hhid⟩ := hr
    cases ht : sm[t]? with
    | none => rw [ht] at hloc; cases hloc
    | some mt =>
      rw [ht] at hloc
      simp only [Option.elim, decide_eq_true_eq] at hloc
      rcases Nat.lt_trichotomy t j with hlt | rfl | hgt
      · exfalso
        have : WeakMem.hiddenFrom sm sa t bound = true := by
          simp only [WeakMem.hiddenFrom, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨j, by omega, hlt, by rw [hm]; simp [hml]⟩
        rw [this] at hhid; cases hhid
      · rfl
      · exact absurd hloc (hjl t mt hgt ht)
  · rintro rfl
    simp only [WeakMem.readable, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨by rw [hm]; simp [hml], ?_⟩
    simp only [WeakMem.hiddenFrom, List.any_eq_false, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro t' _ hlt hx
    cases ht : sm[t']? with
    | none => rw [ht] at hx; cases hx
    | some mt =>
      rw [ht] at hx
      simp only [Option.elim, decide_eq_true_eq] at hx
      exact hjl t' mt hlt ht hx

/-- **The latest message is always readable** by the source, whatever its
read bound: no later message to `sa` can hide it. -/
theorem readable_latest {sm : WeakMem.Memory} {sa : WeakMem.Address} {j bound : Nat} (hj : SLatest sm sa j) :
    WeakMem.readable sm sa j bound = true := by
  obtain ⟨⟨m, hm, hml⟩, hjl⟩ := hj
  simp only [WeakMem.readable, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨by rw [hm]; simp [hml], ?_⟩
  simp only [WeakMem.hiddenFrom, List.any_eq_false, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro t' _ hlt hx
  cases ht : sm[t']? with
  | none => rw [ht] at hx; cases hx
  | some mt =>
    rw [ht] at hx
    simp only [Option.elim, decide_eq_true_eq] at hx
    exact hjl t' mt hlt ht hx

/-! ## Runtime writes -/

/-- **A runtime write** (`Scc/DESIGN.md` §8, item 6): a target message
outside every placed label's range (allocator cursors, headers, the stack
pool's metadata, control blocks), any location and value, with no source
step: source memory and `ts` unchanged. -/
theorem runtime_write (h : MemRel Λ lbl lsize ts tm sm pairs) {w : Msg}
    (hout : ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains w.loc.addr.toNat) :
    MemRel Λ lbl lsize ts (tm.append w).1 sm pairs := by
  refine ⟨h.lbl_static, h.lbl_range, h.lbl_disj, h.lbl_mem, ?_, h.ts_first, h.ts_mono, ?_⟩
  · intro k m hk
    obtain ⟨k', a, v, ht, ha, hw, hv⟩ := h.mem_rep k m hk
    have hlt : k < sm.size := by
      rcases Nat.lt_or_ge k sm.size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_none h'] at hk
    refine ⟨k', a, v, ht, ha, ?_, hv⟩
    rw [wordAt_append_le (h.ts_le_last hlt ht)]; exact hw
  · intro k' m' hg hin
    by_cases hk : k' = tm.last + 1
    · subst hk
      rw [Memory.get?_append_new] at hg; cases hg
      exact absurd hin hout
    · have hle : k' ≤ tm.last := by
        have h1 := Memory.le_last_of_get? hg
        simp only [Memory.last, Memory.append, Array.size_push] at h1 hk
        have h2 : (k' : Nat) ≤ tm.msgs.size + 1 := h1
        have h3 : (k' : Nat) ≠ tm.msgs.size + 1 := hk
        show (k' : Nat) ≤ tm.msgs.size
        rcases Nat.lt_or_ge k' (tm.msgs.size + 1) with h4 | h4
        · exact Nat.le_of_lt_succ h4
        · exact absurd (Nat.le_antisymm h2 h4) h3
      rw [Memory.get?_append_le hle] at hg
      exact h.mem_onto k' m' hg hin

/-! ## Allocation -/

/-- Placing one more label keeps every value representation. -/
theorem valRep_mono {lbl lbl' : WeakMem.AllocLabel → Option Nat} (hl : ∀ l b, lbl l = some b → lbl' l = some b)
    {x : WeakMem.Val} {v : Nat} (h : ValRep lbl x v) : ValRep lbl' x v := by
  cases x with
  | loc a g =>
    obtain ⟨hg, y, hy, rfl⟩ := h
    refine ⟨hg, y, ?_, rfl⟩
    simp only [wordAddr, Option.map_eq_some_iff] at hy ⊢
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨b, hl _ _ hb, rfl⟩
  | _ => exact h

/-- **An allocation** (`Scc/DESIGN.md` §8, item 5): the source allocates the
fresh label `l` (no placement, no message) with `n` words, pushing message
`sm.size + i` to `⟨l, i⟩` for each `i < n` (`TermRun.alloc`, `allocBuf`),
each with a value the zero word represents; the target bumps its cursor
and writes no cell: `l` is placed at `b`, a word-aligned range of the heap
disjoint from every placed label, holding no target message and initially
zero. The new messages map to timestamp 0. -/
theorem alloc (h : MemRel Λ lbl lsize ts tm sm pairs) {l : WeakMem.AllocLabel} {n b : Nat}
    (hfresh : lbl l = none) (hb : b % 8 = 0) (hheap : (Range.mk b (8 * n)).Sub Λ.heap)
    (hdisj : ∀ l' b', lbl l' = some b' → (Range.mk b (8 * n)).Disjoint (lrange lsize l' b'))
    (hnone : ∀ k' w, tm.get? k' = some w → ¬ (Range.mk b (8 * n)).contains w.loc.addr.toNat)
    (hinit : ∀ i < n, tm.initVal (wordLoc (b + 8 * i)) = 0)
    {sm' : WeakMem.Memory} (hsize : sm'.size = sm.size + n) (hold : ∀ k < sm.size, sm'[k]? = sm[k]?)
    (hnew : ∀ i < n, ∃ m, sm'[sm.size + i]? = some m ∧ m.loc = ⟨l, i⟩ ∧
      ValRep (fun l' => if l' = l then some b else lbl l') m.val 0)
    (hts : ∀ k, sm.size ≤ k → ts k = none) :
    MemRel Λ (fun l' => if l' = l then some b else lbl l') (fun l' => if l' = l then n else lsize l')
      (fun k => if sm.size ≤ k ∧ k < sm.size + n then some 0 else ts k) tm sm' pairs := by
  -- the labels of old messages are placed, so they are not `l`
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
  -- the messages of `sm'`
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l' b' hs
    exact hext _ _ (h.lbl_static l' b' hs)
  · intro l' b' hl'
    by_cases he : l' = l
    · subst he
      simp only [ite_true] at hl'; cases hl'
      exact ⟨hb, .inl (by rw [hrange_l]; exact hheap)⟩
    · simp only [he, ite_false] at hl'
      rw [hrange l' he]; exact h.lbl_range l' b' hl'
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
      refine ⟨k', a, v, by simp [show ¬ sm.size ≤ k by omega, ht], ?_, hw, valRep_mono hext hv⟩
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
  · intro k1 k2 k1' k2' h1 h2 p1 p2 hlt
    have n1 : ¬ (sm.size ≤ k1 ∧ k1 < sm.size + n) := by
      intro hc; simp only [hc, and_self, ite_true] at h1; cases h1; omega
    have n2 : ¬ (sm.size ≤ k2 ∧ k2 < sm.size + n) := by
      intro hc; simp only [hc, and_self, ite_true] at h2; cases h2; omega
    simp only [n1, n2, ite_false] at h1 h2
    have hk2 : k2 < sm.size := by
      rcases Nat.lt_or_ge k2 sm.size with h' | h'
      · exact h'
      · rw [hts k2 h'] at h2; cases h2
    rcases h.ts_mono k1 k2 k1' k2' h1 h2 p1 p2 hlt with h' | ⟨a1, a2, a3, a4⟩
    · exact .inl h'
    · refine .inr ⟨a1, a2, a3, fun m1 m2 hm1 hm2 => ?_⟩
      rw [hold k1 (by omega)] at hm1
      rw [hold k2 hk2] at hm2
      exact a4 m1 m2 hm1 hm2
  · intro k' m' hg hin
    obtain ⟨l', b', hl', hc⟩ := hin
    by_cases he : l' = l
    · subst he
      simp only [ite_true] at hl'; cases hl'
      rw [hrange_l] at hc
      exact absurd hc (hnone k' m' hg)
    · simp only [he, ite_false] at hl'
      rw [hrange l' he] at hc
      obtain ⟨k, hk, ht⟩ := h.mem_onto k' m' hg ⟨l', b', hl', hc⟩
      exact ⟨k, by omega, by simp [show ¬ sm.size ≤ k by omega, ht]⟩

/-! ## Example: one word, allocated then stored -/

/-- The source's allocation of label `0`, one word (zero). -/
def toyCell : WeakMem.Msg := ⟨⟨0, 0⟩, .num 0, default⟩

/-- The source's store of `7` to it. -/
def toyStore : WeakMem.Msg := ⟨⟨0, 0⟩, .num 7, default⟩

/-- **The lemmas compose**: from `empty`, label `0` is allocated at `64` in
`trivLayout`'s heap (its zero cell mapped to the initial write) and then
stored `7` (mapped to the target's one message). -/
theorem toy : MemRel trivLayout (fun l => if l = 0 then some 64 else none) (fun l => if l = 0 then 1 else 0)
    (fun k => if k = 1 then some 1 else if 0 ≤ k ∧ k < 0 + 1 then some 0 else none)
    (({ init := [], msgs := #[] } : Memory).append ⟨wordLoc 64, 7, 0⟩).1 #[toyCell, toyStore] [] := by
  have h0 := MemRel.empty (Λ := trivLayout) (fun _ => rfl) (fun _ => 0) { init := [], msgs := #[] } []
  have h1 := h0.alloc (l := 0) (n := 1) (b := 64) rfl rfl
    (by simp [Range.Sub, trivLayout]) (fun _ _ h => by cases h)
    (fun k w hw => by simp [Memory.get?] at hw) (fun i hi => by simp [Memory.initVal])
    (sm' := #[toyCell]) rfl (fun k hk => by simp at hk)
    (fun i hi => ⟨toyCell, by simp at hi ⊢; subst hi; rfl, by simp at hi ⊢; subst hi; rfl, by simp [toyCell, ValRep]⟩)
    (fun _ _ => rfl)
  have h2 := h1.store (a := 64) (v := 7) (tid := 0) (m := toyStore) (by simp [toyStore, wordAddr]) (by simp [toyStore])
    (by simp [toyStore, ValRep]) (fun k hk => by simp at hk ⊢; omega)
  simpa [Memory.last] using h2

end MemRel

end Scc.Sem
