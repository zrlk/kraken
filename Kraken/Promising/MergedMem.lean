/-
The merged memory of a one-thread run: the ISA-independent part of linking
the Promising machine to Kraken's single-threaded judgment.

A thread of the Promising machine keeps the shared locations out of its
private `dmem`, so that every access to them reaches the memory model. Kraken's
single-threaded judgment (`Effects.All`) needs them mapped. `MemRel L d mem D`
relates the thread's private memory `d` and the Promising memory `mem` to the
*merged* memory `D`: off the shared footprint `D` is `d`; on it, `D` holds the
last write to each location (`Memory.finalVal`), little-endian at the
location's width; `d` has nothing there.

The shared locations are a `SharedLayout`: address and width in bytes, pairwise
disjoint (`SharedLayout.WF`). The Promising machine is non-mixed-size (a
location is its footprint, address and width), so the link needs every
access to the footprint to be exactly at a location's address and width:
`SharedLayout.Ok`.
The lemmas here are what a load or a store does to the relation.
-/
import Kraken.Mem
import Kraken.Promising.Basic

open Std

namespace Kraken.Promising

theorem Memory.finalVal_append (m : Memory) (w : Msg) (l : Loc) :
    (m.append w).1.finalVal l = if w.loc = l then w.val else m.finalVal l := by
  unfold Memory.finalVal; simp only [Memory.append]
  by_cases hl : w.loc = l
  · rw [Array.findRev?_push_of_pos (by simpa using hl), ite_eq_left hl]
  · rw [Array.findRev?_push_of_neg (by simpa using hl), ite_eq_right hl]
    rfl

/-! ## Layouts -/

/-- The shared locations of a one-thread run: address and width in bytes. -/
abbrev SharedLayout := List (BitVec 64 × Nat)

namespace SharedLayout

/-- The address `k` lies in the footprint of a shared location. -/
def Covers (L : SharedLayout) (k : BitVec 64) : Prop := ∃ a n, (a, n) ∈ L ∧ (k - a).toNat < n

/-- Locations are nonempty, at most 16 bytes wide, and two locations that
share a byte are the same location.

The bound is the widest value a location holds (`Val` has 128 bits; a 16-byte
location is what an atomic vector access or `cmpxchg16b` reaches). It is a bound rather than the set
{1, 2, 4, 8, 16}: the lemmas here only need a location's value to fit in a
`Val`, and which widths an access can have is the access discipline's concern
(`Ok`, and per ISA `Effects.AllW`), not the layout's. -/
structure WF (L : SharedLayout) : Prop where
  pos : ∀ a n, (a, n) ∈ L → 0 < n
  le16 : ∀ a n, (a, n) ∈ L → n ≤ 16
  disj : ∀ a n b m k, (a, n) ∈ L → (b, m) ∈ L → (k - a).toNat < n → (k - b).toNat < m → a = b ∧ n = m

/-- An access of `n` bytes at `addr` respects the layout: it is exactly a
shared location, or it misses the footprint. -/
def Ok (L : SharedLayout) (addr : BitVec 64) (n : Nat) : Prop :=
  (addr, n) ∈ L ∨ ∀ i < n, ¬ L.Covers (addr + BitVec.ofNat 64 i)

theorem covers_of_mem {L : SharedLayout} {a : BitVec 64} {n i : Nat} (h : (a, n) ∈ L) (hi : i < n) (hn : n ≤ 16) :
    L.Covers (a + BitVec.ofNat 64 i) := by
  refine ⟨a, n, h, ?_⟩
  rw [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hi

end SharedLayout

/-- The Promising location of a shared location of `n` bytes at `a`: its
footprint, as the ISA adapters build it for an access of `n` bytes at `a`
with no declarations. -/
def sharedLoc (a : BitVec 64) (n : Nat) : Loc := { addr := a, bytes := n }

/-- The bytes of a shared location of `n` bytes in the merged memory: its last
write, little-endian. -/
def sharedBytes (mem : Memory) (a : BitVec 64) (n : Nat) : List UInt8 :=
  Int.toBytes n ((mem.finalVal (sharedLoc a n)).toNat : Int)

/-- A load of a shared location from the merged memory returns its last write
at the access width. -/
theorem sharedBytes_val (mem : Memory) (a : BitVec 64) {w n : Nat} (hw : w = 8 * n) :
    BitVec.ofInt w (Int.ofBytes (sharedBytes mem a n)) = (mem.finalVal (sharedLoc a n)).setWidth w := by
  rw [sharedBytes, BitVec.ofInt_ofBytes_toBytes_eq w n hw, BitVec.ofInt_natCast]
  exact BitVec.ofNat_toNat w _

/-- The merged memory `D` of the private memory `d` and the Promising memory
`mem`. -/
structure MemRel (L : SharedLayout) (d : Mem 64) (mem : Memory) (D : Mem 64) : Prop where
  priv : ∀ k, ¬ L.Covers k → D.get? k = d.get? k
  split : ∀ k, L.Covers k → d.get? k = none
  shared : ∀ a n, (a, n) ∈ L → D.loadBytes a n = some (sharedBytes mem a n)

/-! ## Bytes -/

theorem Mem.loadBytes_congr {m₁ m₂ : Mem 64} {a : BitVec 64} {n : Nat}
    (h : ∀ i < n, m₁.get? (a + BitVec.ofNat 64 i) = m₂.get? (a + BitVec.ofNat 64 i)) :
    m₁.loadBytes a n = m₂.loadBytes a n := by
  unfold Mem.loadBytes
  congr 1
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem Mem.get?_isSome_of_loadBytes {m : Mem 64} {a : BitVec 64} {n : Nat}
    (h : (m.loadBytes a n).isSome) : ∀ i < n, (m.get? (a + BitVec.ofNat 64 i)).isSome := by
  intro i hi
  unfold Mem.loadBytes at h
  exact (List.allSome_isSome_iff _).mp h _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem Mem.get?_storeBytes (m : Mem 64) (a k : BitVec 64) (bs : List UInt8) :
    (m.storeBytes a bs).get? k = ((bs.At a).get? k).or (m.get? k) := by
  simp only [Mem.storeBytes, ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq, ExtHashMap.getElem?_union]

/-- A byte a store of `n` bytes at `a` writes is `a + i` for some `i < n`. -/
theorem Mem.get?_At_eq_none {a k : BitVec 64} {bs : List UInt8}
    (h : ∀ i < bs.length, k ≠ a + BitVec.ofNat 64 i) : (bs.At a).get? k = none := by
  rw [ExtHashMap.get?_eq_getElem?]
  apply ExtHashMap.getElem?_eq_none
  rw [mem_At_iff]
  rintro ⟨i, hi, rfl⟩
  exact h i hi rfl

theorem Mem.loadBytes_isSome_of_loadInt {m : Mem 64} {a : BitVec 64} {n : Nat} {x : Int}
    (h : Mem.loadInt m a n = some x) : (m.loadBytes a n).isSome := by
  unfold Mem.loadInt at h
  cases hb : m.loadBytes a n <;> simp [hb] at h ⊢

/-- A load of `p + q` bytes is a load of `p` bytes followed by one of `q`. -/
theorem Mem.loadBytes_add (m : Mem 64) (a : BitVec 64) (p q : Nat) :
    m.loadBytes a (p + q) = (m.loadBytes a p).bind fun l₁ =>
      (m.loadBytes (a + BitVec.ofNat 64 p) q).map fun l₂ => l₁ ++ l₂ := by
  unfold Mem.loadBytes List.allSome
  rw [List.range_add, List.map_append, List.mapM_append, List.map_map]
  have hf : ((fun i => m.get? (a + BitVec.ofNat 64 i)) ∘ (p + ·)) =
      fun i => m.get? (a + BitVec.ofNat 64 p + BitVec.ofNat 64 i) := by
    funext i; simp only [Function.comp, BitVec.ofNat_add, BitVec.add_assoc]
  rw [hf]
  cases (List.map (fun i => m.get? (a + BitVec.ofNat 64 i)) (List.range p)).mapM id <;>
    cases (List.map (fun i => m.get? (a + BitVec.ofNat 64 p + BitVec.ofNat 64 i)) (List.range q)).mapM id <;> rfl

theorem Mem.loadBytes_add_some {m : Mem 64} {a : BitVec 64} {p q : Nat} {bs : List UInt8}
    (h : m.loadBytes a (p + q) = some bs) :
    ∃ bs₁ bs₂, m.loadBytes a p = some bs₁ ∧ m.loadBytes (a + BitVec.ofNat 64 p) q = some bs₂ ∧
      bs = bs₁ ++ bs₂ := by
  rw [Mem.loadBytes_add] at h
  cases h₁ : m.loadBytes a p with
  | none => rw [h₁] at h; cases h
  | some bs₁ =>
    cases h₂ : m.loadBytes (a + BitVec.ofNat 64 p) q with
    | none => rw [h₁, h₂] at h; cases h
    | some bs₂ =>
      rw [h₁, h₂] at h
      exact ⟨bs₁, bs₂, rfl, rfl, (Option.some.inj h).symm⟩

theorem Mem.loadBytes_length {m : Mem 64} {a : BitVec 64} {n : Nat} {bs : List UInt8}
    (h : m.loadBytes a n = some bs) : bs.length = n := by
  unfold Mem.loadBytes at h
  have := congrArg List.length (List.allSome_eq_map_some h)
  simpa using this.symm

/-- A store keeps every byte that was mapped mapped. -/
theorem Mem.loadBytes_isSome_storeBytes {m : Mem 64} {b : BitVec 64} {n : Nat} (a : BitVec 64)
    (bs : List UInt8) (h : (m.loadBytes b n).isSome) : ((m.storeBytes a bs).loadBytes b n).isSome := by
  unfold Mem.loadBytes at h ⊢
  rw [List.allSome_isSome_iff] at h ⊢
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
  have := h _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  simp only [Mem.storeBytes, ExtHashMap.get?_eq_getElem?, ExtHashMap.union_eq, ExtHashMap.getElem?_union] at this ⊢
  cases ((bs.At a)[b + BitVec.ofNat 64 i]? : Option UInt8) <;> simp_all

theorem Mem.storeBytes_nil (m : Mem 64) (a : BitVec 64) : m.storeBytes a [] = m := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [Mem.storeBytes, ExtHashMap.union_eq, ExtHashMap.getElem?_union]
  rw [ExtHashMap.getElem?_eq_none (by rw [mem_At_iff]; simp)]
  rfl

/-- A store of `bs₁ ++ bs₂` is a store of `bs₁` followed by one of `bs₂`. -/
theorem Mem.storeBytes_append (m : Mem 64) (a : BitVec 64) (bs₁ bs₂ : List UInt8)
    (h : bs₁.length + bs₂.length ≤ 2 ^ 64) :
    m.storeBytes a (bs₁ ++ bs₂) = (m.storeBytes a bs₁).storeBytes (a + BitVec.ofNat 64 bs₁.length) bs₂ := by
  apply ExtHashMap.ext_getElem?
  intro k
  simp only [Mem.storeBytes, List.At_append bs₁ bs₂ a h, ExtHashMap.union_eq, ExtHashMap.getElem?_union,
    Option.or_assoc]

/-- The bytes of an 8-byte piece's value are the piece. -/
theorem toBytes_ofInt_ofBytes {w n : Nat} (hw : w = 8 * n) {bs : List UInt8} (h : bs.length = n) :
    Int.toBytes n (BitVec.ofInt w (Int.ofBytes bs)).toInt = bs := by
  rw [BitVec.ofInt_ofBytes_take w n hw, BitVec.toInt_ofInt]
  rw [show 2 ^ w = 256 ^ n by
    subst w
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]]
  have := Int.toBytes_bmod_ofBytes n (bs.take n) (by simp [h])
  rw [List.take_of_length_le (by omega)] at this
  rw [List.take_of_length_le (by omega)]
  exact_mod_cast this

/-- Without shared locations, a memory is its own merge. -/
theorem MemRel.nil (d : Mem 64) (mem : Memory) : MemRel [] d mem d :=
  ⟨fun _ _ => rfl, fun _ ⟨_, _, h, _⟩ => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem SharedLayout.ok_nil (addr : BitVec 64) (n : Nat) : SharedLayout.Ok [] addr n :=
  .inr fun _ _ ⟨_, _, h, _⟩ => nomatch h

theorem SharedLayout.wf_nil : SharedLayout.WF [] :=
  ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ _ _ _ h => (nomatch h)⟩

/-! ## Loads -/

namespace MemRel

variable {L : SharedLayout} {d D : Mem 64} {mem : Memory}

/-- A load the private memory serves reads the same bytes from the merged one. -/
theorem loadBytes_priv (h : MemRel L d mem D) {a : BitVec 64} {n : Nat} (hd : (d.loadBytes a n).isSome) :
    D.loadBytes a n = d.loadBytes a n := by
  apply Mem.loadBytes_congr
  intro i hi
  apply h.priv
  intro hc
  have := Mem.get?_isSome_of_loadBytes hd i hi
  rw [h.split _ hc] at this
  cases this

/-- A load that misses the footprint reads the same from both memories. -/
theorem loadBytes_off (h : MemRel L d mem D) {a : BitVec 64} {n : Nat}
    (hoff : ∀ i < n, ¬ L.Covers (a + BitVec.ofNat 64 i)) : D.loadBytes a n = d.loadBytes a n :=
  Mem.loadBytes_congr fun i hi => h.priv _ (hoff i hi)

theorem loadInt_priv (h : MemRel L d mem D) {a : BitVec 64} {n : Nat} {x : Int}
    (hd : Mem.loadInt d a n = some x) : Mem.loadInt D a n = some x := by
  have hs : (d.loadBytes a n).isSome := by
    unfold Mem.loadInt at hd
    cases hb : d.loadBytes a n <;> simp [hb] at hd ⊢
  unfold Mem.loadInt
  rw [h.loadBytes_priv hs]
  exact hd

/-- A load the private memory does not serve and that respects the layout:
either it is a shared location, read from the merged memory, or the merged
memory does not serve it either. -/
theorem loadInt_none (h : MemRel L d mem D) {a : BitVec 64} {n : Nat}
    (hd : Mem.loadInt d a n = none) (hok : L.Ok a n) :
    ((a, n) ∈ L ∧ Mem.loadInt D a n = some (Int.ofBytes (sharedBytes mem a n))) ∨ Mem.loadInt D a n = none := by
  rcases hok with hmem | hoff
  · left
    refine ⟨hmem, ?_⟩
    unfold Mem.loadInt
    rw [h.shared a n hmem]
    rfl
  · right
    unfold Mem.loadInt at hd ⊢
    rw [h.loadBytes_off hoff]
    exact hd

/-! ## Stores -/

/-- A store the private memory serves: both memories take it. -/
theorem store_priv (h : MemRel L d mem D) {a : BitVec 64} {n : Nat} (x : Int)
    (hd : (d.loadBytes a n).isSome) :
    MemRel L (Mem.storeInt d a n x) mem (Mem.storeInt D a n x) := by
  have hlen : (Int.toBytes n x).length = n := Int.toBytes_length n x
  -- the bytes written are private
  have hpriv : ∀ k, k ∈ (Int.toBytes n x).At a → ¬ L.Covers k := by
    intro k hk hc
    rw [mem_At_iff, hlen] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    have := Mem.get?_isSome_of_loadBytes hd i hi
    rw [h.split _ hc] at this
    cases this
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun b m hb => ?_⟩
  · simp only [Mem.storeInt, Mem.get?_storeBytes, h.priv k hk]
  · simp only [Mem.storeInt, Mem.get?_storeBytes, h.split k hk, Option.or_none]
    rw [ExtHashMap.get?_eq_getElem?]
    exact ExtHashMap.getElem?_eq_none fun hm => hpriv k hm hk
  · rw [← h.shared b m hb]
    apply Mem.loadBytes_congr
    intro i hi
    have hc : L.Covers (b + BitVec.ofNat 64 i) := ⟨b, m, hb, by
      rw [BitVec.add_comm b, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hi⟩
    simp only [Mem.storeInt, Mem.get?_storeBytes]
    rw [ExtHashMap.get?_eq_getElem? (m := (Int.toBytes n x).At a),
      ExtHashMap.getElem?_eq_none fun hm => hpriv _ hm hc]
    rfl

/-- `store_priv` for a store of bytes. -/
theorem storeBytes_priv (h : MemRel L d mem D) {a : BitVec 64} {bs : List UInt8}
    (hd : (d.loadBytes a bs.length).isSome) :
    MemRel L (d.storeBytes a bs) mem (D.storeBytes a bs) := by
  have := h.store_priv (Int.ofBytes bs) hd
  rwa [Mem.storeInt, Mem.storeInt, Int.toBytes_ofBytes _ _ (Nat.le_refl _), List.take_length] at this

private theorem toBytes_toInt {w n : Nat} (hw : w = 8 * n) (v : BitVec w) :
    Int.toBytes n v.toInt = Int.toBytes n (v.toNat : Int) := by
  rw [← Int.toBytes_emod n v.toInt, ← Int.toBytes_emod n (v.toNat : Int), Int.take, Int.take, ← hw,
    BitVec.toInt_eq_toNat_bmod]
  have h2 : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by norm_cast
  rw [h2, Int.bmod_emod]

/-- A store to a shared location: the merged memory takes it, the private
memory does not, and the Promising memory appends it. -/
theorem store_shared (hL : L.WF) (h : MemRel L d mem D) {a : BitVec 64} {n w : Nat} (ha : (a, n) ∈ L)
    (hw : w = 8 * n) (v : BitVec w) (tid : Nat) :
    MemRel L d (mem.append { loc := sharedLoc a n, val := v.setWidth 128, tid }).1 (Mem.storeInt D a n v.toInt) := by
  have hn8 := hL.le16 a n ha
  have hlen : (Int.toBytes n v.toInt).length = n := Int.toBytes_length n v.toInt
  -- the bytes written are those of the location
  have hown : ∀ k, k ∈ (Int.toBytes n v.toInt).At a → ∃ i < n, k = a + BitVec.ofNat 64 i := by
    intro k hk
    rw [mem_At_iff, hlen] at hk
    exact hk
  refine ⟨fun k hk => ?_, h.split, fun b m hb => ?_⟩
  · simp only [Mem.storeInt, Mem.get?_storeBytes, ← h.priv k hk]
    rw [ExtHashMap.get?_eq_getElem? (m := (Int.toBytes n v.toInt).At a),
      ExtHashMap.getElem?_eq_none fun hm => by
        obtain ⟨i, hi, rfl⟩ := hown k hm
        exact hk (SharedLayout.covers_of_mem ha hi hn8)]
    rfl
  · have hm8 := hL.le16 b m hb
    by_cases hab : b = a
    · subst hab
      have hmn : m = n := (hL.disj b n b m b ha hb (by simp [hL.pos b n ha]) (by simp [hL.pos b m hb])).2.symm
      subst hmn
      have hst := Mem.loadBytes_storeBytes D b (Int.toBytes m v.toInt) (by rw [hlen]; omega)
      rw [hlen] at hst
      rw [Mem.storeInt, hst, sharedBytes, Memory.finalVal_append, ite_eq_left rfl, toBytes_toInt hw,
        BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
      exact Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    · have hfv : (mem.append { loc := sharedLoc a n, val := v.setWidth 128, tid }).1.finalVal (sharedLoc b m)
          = mem.finalVal (sharedLoc b m) := by
        rw [Memory.finalVal_append, ite_eq_right]
        intro he
        exact hab (congrArg Loc.addr he).symm
      rw [sharedBytes, hfv, ← sharedBytes, ← h.shared b m hb]
      apply Mem.loadBytes_congr
      intro i hi
      simp only [Mem.storeInt, Mem.get?_storeBytes]
      rw [ExtHashMap.get?_eq_getElem? (m := (Int.toBytes n v.toInt).At a),
        ExtHashMap.getElem?_eq_none fun hm => by
          obtain ⟨j, hj, he⟩ := hown _ hm
          have h1 := SharedLayout.covers_of_mem hb hi hm8
          have := hL.disj b m a n (b + BitVec.ofNat 64 i) hb ha
            (by rw [BitVec.add_comm b, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)
            (by rw [he, BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hj)
          exact hab this.1]
      rfl

end MemRel

end Kraken.Promising
